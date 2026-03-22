import json
import os
import re
import time
import random
import secrets
import hashlib
import base64
import threading
import argparse
from dataclasses import dataclass
from typing import Any, Dict, Optional
import urllib.parse
import logging

from curl_cffi import requests as _raw_requests

logging.basicConfig(
    level=getattr(logging, os.getenv("OPENAI_REG_LOG_LEVEL", "DEBUG").upper(), logging.DEBUG),
    format="%(asctime)s | %(levelname)-8s | %(message)s",
    datefmt="%H:%M:%S",
)


class _StdLogger:
    def __init__(self) -> None:
        self._logger = logging.getLogger("openai_reg")

    def _fmt(self, message: str, *args: Any) -> str:
        return message.format(*args) if args else message

    def debug(self, message: str, *args: Any) -> None:
        self._logger.debug(self._fmt(message, *args))

    def info(self, message: str, *args: Any) -> None:
        self._logger.info(self._fmt(message, *args))

    def warning(self, message: str, *args: Any) -> None:
        self._logger.warning(self._fmt(message, *args))

    def error(self, message: str, *args: Any) -> None:
        self._logger.error(self._fmt(message, *args))

    def exception(self, message: str, *args: Any) -> None:
        self._logger.exception(self._fmt(message, *args))


logger = _StdLogger()


def _is_tls_error(e: Exception) -> bool:
    """判断是否为 TLS/SSL/curl 握手错误"""
    msg = str(e)
    return "TLS" in msg or "SSL" in msg or "curl" in msg.lower()


def _request_with_tls_retry(method: str, url: str, *, session=None, max_retries: int = 3, **kwargs):
    """带 TLS 快速重试的请求包装器，重试间隔 0.5s"""
    caller = session if session else _raw_requests
    for attempt in range(1, max_retries + 1):
        try:
            return getattr(caller, method)(url, **kwargs)
        except Exception as e:
            if _is_tls_error(e) and attempt < max_retries:
                logger.warning(
                    "TLS 快速重试: method={} url={} attempt={}/{} error={}",
                    method.upper(),
                    url[:80],
                    attempt,
                    max_retries,
                    e,
                )
                time.sleep(0.5 * attempt)
                continue
            raise


class _RetrySession:
    """包装 curl_cffi Session，所有请求自动带 TLS 重试"""
    def __init__(self, **kwargs):
        self._s = _raw_requests.Session(**kwargs)

    def __getattr__(self, name):
        return getattr(self._s, name)

    def get(self, url, **kwargs):
        return _request_with_tls_retry("get", url, session=self._s, **kwargs)

    def post(self, url, **kwargs):
        return _request_with_tls_retry("post", url, session=self._s, **kwargs)


# 用带重试的 requests 模块替代裸调用
class requests:
    """带 TLS 重试的 requests 命名空间"""
    Session = _RetrySession

    @staticmethod
    def get(url, **kwargs):
        return _request_with_tls_retry("get", url, **kwargs)

    @staticmethod
    def post(url, **kwargs):
        return _request_with_tls_retry("post", url, **kwargs)




def _get_sentinel(s, did: str, flow: str) -> str:
    """获取指定 flow 的 sentinel token"""
    sen_req_body = json.dumps({"p": "", "id": did, "flow": flow})
    sen_resp = requests.post(
        "https://sentinel.openai.com/backend-api/sentinel/req",
        headers={
            "origin": "https://sentinel.openai.com",
            "referer": "https://sentinel.openai.com/backend-api/sentinel/frame.html?sv=20260219f9f6",
            "content-type": "text/plain;charset=UTF-8",
        },
        data=sen_req_body,
        proxies=getattr(s, "proxies", None),
        impersonate="chrome",
        timeout=15,
    )
    if sen_resp.status_code != 200:
        raise RuntimeError(f"Sentinel {flow} 失败: {sen_resp.status_code}: {sen_resp.text[:200]}")
    token = (sen_resp.json() or {}).get("token", "")
    return json.dumps({"p": "", "t": "", "c": token, "id": did, "flow": flow})


def _list_tempmail_messages(email: str, proxies: Any = None) -> list[dict]:
    encoded_email = urllib.parse.quote(email, safe="")
    resp = requests.get(
        f"{TEMPMAIL_BASE}/emails/{encoded_email}",
        headers={
            "accept": "*/*",
            "referer": "https://tempmail.ing/",
        },
        proxies=proxies,
        impersonate="chrome",
        timeout=15,
    )
    if resp.status_code != 200:
        return []
    data = resp.json()
    messages = data.get("emails") or []
    return messages if isinstance(messages, list) else []

# ==========================================
# tempmail.ing 免费临时邮箱 API
# ==========================================

TEMPMAIL_BASE = "https://api.tempmail.ing/api"

TEMPMAIL_HEADERS = {
    "accept": "*/*",
    "content-type": "application/json",
    "origin": "https://tempmail.ing",
    "referer": "https://tempmail.ing/",
}

# --- 速率控制与策略常量 ---
_GENERATE_MIN_INTERVAL = 10.0+5.0  # /generate 最小调用间隔 (秒) — tempmail.ing 页面限制 10s
_GENERATE_MAX_RETRIES = 3      # /generate 最大重试次数
_GENERATE_RETRY_BACKOFF = 5.0*2  # 重试退避基数 (秒)
_INBOX_POLL_INTERVAL = 4.0     # 收件箱轮询间隔 (秒)
_INBOX_POLL_TIMEOUT = 120.0+30    # 收件箱轮询总超时 (秒)
_RATE_LIMIT_WAIT = 2.0+3.0         # 遇到 429 额外等待 (秒)

# --- 已知被 OpenAI 封禁的临时邮箱域名黑名单 ---
_DOMAIN_BLACKLIST: set[str] = {
    "animatimg.com",
    "tempmail.ing"
    # 发现新的被封域名时在此添加
}
_BLACKLIST_MAX_RETRIES = 5     # 因域名黑名单触发的最大重新生成次数

# --- 线程安全的 /generate 速率限制器 ---
_last_generate_ts = 0.0
_generate_lock = threading.Lock()


def _rate_limited_generate(proxies: Any = None) -> dict:
    """带速率限制和重试的 /generate 调用"""
    global _last_generate_ts

    for attempt in range(1, _GENERATE_MAX_RETRIES + 1):
        with _generate_lock:
            now = time.monotonic()
            wait = _GENERATE_MIN_INTERVAL - (now - _last_generate_ts)
            if wait > 0:
                time.sleep(wait)
            _last_generate_ts = time.monotonic()

        try:
            logger.debug("请求 tempmail /generate: attempt={} duration=10", attempt)
            resp = requests.post(
                f"{TEMPMAIL_BASE}/generate",
                headers=TEMPMAIL_HEADERS,
                json={"duration": 10},
                proxies=proxies,
                impersonate="chrome",
                timeout=15,
            )

            if resp.status_code == 429:
                retry_after = _RATE_LIMIT_WAIT + _GENERATE_RETRY_BACKOFF * attempt
                logger.warning(
                    "tempmail /generate 429: wait={}s attempt={}/{}",
                    int(retry_after),
                    attempt,
                    _GENERATE_MAX_RETRIES,
                )
                time.sleep(retry_after)
                continue

            data = resp.json()
            if resp.status_code == 200 and data.get("success"):
                address = str((data.get("email") or {}).get("address") or "").strip()
                logger.info("tempmail /generate 成功: email={}", address)
                return data

            logger.warning(
                "tempmail /generate 失败: status={} body={}",
                resp.status_code,
                resp.text[:150],
            )
        except Exception as e:
            logger.warning("tempmail /generate 异常: attempt={} error={}", attempt, e)

        if attempt < _GENERATE_MAX_RETRIES:
            backoff = _GENERATE_RETRY_BACKOFF * attempt
            logger.info("tempmail /generate 准备重试: backoff={}s", int(backoff))
            time.sleep(backoff)

    return {}


# 全局变量保存密码
_temp_password = ""


def get_email_and_token(proxies: Any = None) -> tuple:
    """通过 tempmail.ing 创建临时邮箱，返回 (email, email, password)
    自动跳过黑名单域名，最多重试 _BLACKLIST_MAX_RETRIES 次"""
    global _temp_password
    for bl_attempt in range(1, _BLACKLIST_MAX_RETRIES + 1):
        try:
            data = _rate_limited_generate(proxies)
            if not data:
                logger.error("tempmail 创建邮箱失败: 已用尽重试")
                return "", "", ""

            email = str((data.get("email") or {}).get("address") or "").strip()
            if not email:
                logger.error("tempmail /generate 响应缺少 email.address")
                return "", "", ""

            domain = email.rsplit("@", 1)[-1].lower() if "@" in email else ""
            if domain in _DOMAIN_BLACKLIST:
                logger.warning(
                    "命中邮箱域名黑名单: domain={} attempt={}/{}",
                    domain,
                    bl_attempt,
                    _BLACKLIST_MAX_RETRIES,
                )
                continue

            _temp_password = ""
            logger.info("临时邮箱可用: email={} domain={}", email, domain)
            return email, email, ""
        except Exception as e:
            logger.exception("请求 tempmail API 失败")
            return "", "", ""

    logger.error("连续 {} 次命中黑名单域名，放弃本轮邮箱生成", _BLACKLIST_MAX_RETRIES)
    return "", "", ""


def _mail_sender(msg: Dict[str, Any]) -> str:
    return " ".join(
        str(part or "").strip()
        for part in [
            msg.get("from"),
            msg.get("sender"),
            msg.get("from_address"),
            msg.get("from_name"),
        ]
        if str(part or "").strip()
    )


def _mail_content(msg: Dict[str, Any]) -> str:
    return "\n".join(
        str(part or "")
        for part in [
            msg.get("subject"),
            msg.get("text"),
            msg.get("content"),
            msg.get("body"),
            msg.get("html"),
        ]
        if str(part or "")
    )


def _looks_like_openai_mail(msg: Dict[str, Any]) -> bool:
    haystack = f"{_mail_sender(msg)}\n{_mail_content(msg)}".lower()
    return any(keyword in haystack for keyword in ("openai", "chatgpt", "otp@tm1.openai.com"))


def get_oai_code(
    token: str,
    email: str,
    proxies: Any = None,
    *,
    ignore_ids: Optional[set[str]] = None,
    exclude_codes: Optional[set[str]] = None,
) -> str:
    """轮询 tempmail.ing 获取 OpenAI 验证码。
    可忽略已有邮件 ID，并排除已使用过的验证码，便于二次 OTP 登录流程。"""
    del token
    regex = r"(?<!\d)(\d{6})(?!\d)"
    seen_ids: set[str] = set(ignore_ids or set())
    exclude_codes = set(exclude_codes or set())
    deadline = time.monotonic() + _INBOX_POLL_TIMEOUT
    poll_round = 0

    logger.info(
        "开始轮询验证码: email={} timeout={}s interval={}s ignore_ids={} exclude_codes={}",
        email,
        int(_INBOX_POLL_TIMEOUT),
        int(_INBOX_POLL_INTERVAL),
        len(seen_ids),
        len(exclude_codes),
    )

    while time.monotonic() < deadline:
        poll_round += 1
        try:
            messages = _list_tempmail_messages(email, proxies=proxies)
            logger.info("收件箱轮询结果: round={} emails={}", poll_round, len(messages))

            for msg in messages:
                if not isinstance(msg, dict):
                    continue
                msg_id = str(msg.get("id") or msg.get("messageId") or "").strip()
                if msg_id and msg_id in seen_ids:
                    continue
                if msg_id:
                    seen_ids.add(msg_id)

                sender = _mail_sender(msg)
                subject = str(msg.get("subject") or "")
                content = _mail_content(msg)

                logger.info(
                    "发现候选邮件: id={} from={} subject={} keys={}",
                    msg_id or "<no-id>",
                    sender[:120] or "<empty>",
                    subject[:120] or "<empty>",
                    sorted(msg.keys()),
                )

                if not _looks_like_openai_mail(msg):
                    logger.debug("跳过非 OpenAI/ChatGPT 邮件: id={}", msg_id or "<no-id>")
                    continue

                matches = re.findall(regex, content)
                for code in matches:
                    if code in exclude_codes:
                        logger.debug("跳过已排除验证码: id={} code={}", msg_id or "<no-id>", code)
                        continue
                    logger.info(
                        "成功解析验证码: email={} code={} from={} subject={}",
                        email,
                        code,
                        sender[:120],
                        subject[:120],
                    )
                    return code

                logger.warning(
                    "目标邮件已到达但未解析到可用验证码: id={} sender={} subject={} preview={}",
                    msg_id or "<no-id>",
                    sender[:120],
                    subject[:120],
                    content[:200].replace("\n", " "),
                )
        except Exception as e:
            logger.warning(
                "轮询收件箱异常: round={} type={} error={}",
                poll_round,
                type(e).__name__,
                e,
            )

        time.sleep(_INBOX_POLL_INTERVAL)

    logger.error("验证码轮询超时: email={} waited={}s", email, int(_INBOX_POLL_TIMEOUT))
    return ""



# ==========================================
# OAuth 授权与辅助函数
# ==========================================

AUTH_URL = "https://auth.openai.com/oauth/authorize"
TOKEN_URL = "https://auth.openai.com/oauth/token"
CLIENT_ID = "app_EMoamEEZ73f0CkXaXp7hrann"

DEFAULT_REDIRECT_URI = f"http://localhost:1455/auth/callback"
DEFAULT_SCOPE = "openid email profile offline_access"


def _b64url_no_pad(raw: bytes) -> str:
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def _sha256_b64url_no_pad(s: str) -> str:
    return _b64url_no_pad(hashlib.sha256(s.encode("ascii")).digest())


def _random_state(nbytes: int = 16) -> str:
    return secrets.token_urlsafe(nbytes)


def _pkce_verifier() -> str:
    return secrets.token_urlsafe(64)


def _parse_callback_url(callback_url: str) -> Dict[str, Any]:
    candidate = callback_url.strip()
    if not candidate:
        return {"code": "", "state": "", "error": "", "error_description": ""}

    if "://" not in candidate:
        if candidate.startswith("?"):
            candidate = f"http://localhost{candidate}"
        elif any(ch in candidate for ch in "/?#") or ":" in candidate:
            candidate = f"http://{candidate}"
        elif "=" in candidate:
            candidate = f"http://localhost/?{candidate}"

    parsed = urllib.parse.urlparse(candidate)
    query = urllib.parse.parse_qs(parsed.query, keep_blank_values=True)
    fragment = urllib.parse.parse_qs(parsed.fragment, keep_blank_values=True)

    for key, values in fragment.items():
        if key not in query or not query[key] or not (query[key][0] or "").strip():
            query[key] = values

    def get1(k: str) -> str:
        v = query.get(k, [""])
        return (v[0] or "").strip()

    code = get1("code")
    state = get1("state")
    error = get1("error")
    error_description = get1("error_description")

    if code and not state and "#" in code:
        code, state = code.split("#", 1)

    if not error and error_description:
        error, error_description = error_description, ""

    return {
        "code": code,
        "state": state,
        "error": error,
        "error_description": error_description,
    }


def _jwt_claims_no_verify(id_token: str) -> Dict[str, Any]:
    if not id_token or id_token.count(".") < 2:
        return {}
    payload_b64 = id_token.split(".")[1]
    pad = "=" * ((4 - (len(payload_b64) % 4)) % 4)
    try:
        payload = base64.urlsafe_b64decode((payload_b64 + pad).encode("ascii"))
        return json.loads(payload.decode("utf-8"))
    except Exception:
        return {}


def _decode_jwt_segment(seg: str) -> Dict[str, Any]:
    raw = (seg or "").strip()
    if not raw:
        return {}
    pad = "=" * ((4 - (len(raw) % 4)) % 4)
    try:
        decoded = base64.urlsafe_b64decode((raw + pad).encode("ascii"))
        return json.loads(decoded.decode("utf-8"))
    except Exception:
        return {}


def _to_int(v: Any) -> int:
    try:
        return int(v)
    except (TypeError, ValueError):
        return 0


def _post_form(
    url: str,
    data: Dict[str, str],
    timeout: int = 60,
    proxies: Any = None,
    max_retries: int = 3,
) -> Dict[str, Any]:
    """用 curl_cffi 发送 form-urlencoded POST（支持代理），带重试"""
    last_err: Exception | None = None
    for attempt in range(1, max_retries + 1):
        try:
            resp = requests.post(
                url,
                data=data,
                headers={
                    "Content-Type": "application/x-www-form-urlencoded",
                    "Accept": "application/json",
                },
                proxies=proxies,
                impersonate="chrome",
                timeout=timeout,
            )
            if resp.status_code != 200:
                raise RuntimeError(
                    f"token exchange failed: {resp.status_code}: {resp.text[:300]}"
                )
            return resp.json()
        except Exception as e:
            last_err = e
            if attempt < max_retries:
                wait = 3 * attempt
                print(f"[Warn] token 交换失败 (第{attempt}次): {e}, {wait}s 后重试...")
                time.sleep(wait)
    raise last_err


@dataclass(frozen=True)
class OAuthStart:
    auth_url: str
    state: str
    code_verifier: str
    redirect_uri: str


def generate_oauth_url(
    *, redirect_uri: str = DEFAULT_REDIRECT_URI, scope: str = DEFAULT_SCOPE
) -> OAuthStart:
    state = _random_state()
    code_verifier = _pkce_verifier()
    code_challenge = _sha256_b64url_no_pad(code_verifier)

    params = {
        "client_id": CLIENT_ID,
        "response_type": "code",
        "redirect_uri": redirect_uri,
        "scope": scope,
        "state": state,
        "code_challenge": code_challenge,
        "code_challenge_method": "S256",
        "prompt": "login",
        "id_token_add_organizations": "true",
        "codex_cli_simplified_flow": "true",
    }
    auth_url = f"{AUTH_URL}?{urllib.parse.urlencode(params)}"
    return OAuthStart(
        auth_url=auth_url,
        state=state,
        code_verifier=code_verifier,
        redirect_uri=redirect_uri,
    )


def submit_callback_url(
    *,
    callback_url: str,
    expected_state: str,
    code_verifier: str,
    redirect_uri: str = DEFAULT_REDIRECT_URI,
    proxy: Optional[str] = None,
) -> str:
    cb = _parse_callback_url(callback_url)
    if cb["error"]:
        desc = cb["error_description"]
        raise RuntimeError(f"oauth error: {cb['error']}: {desc}".strip())

    if not cb["code"]:
        raise ValueError("callback url missing ?code=")
    if not cb["state"]:
        raise ValueError("callback url missing ?state=")
    if cb["state"] != expected_state:
        raise ValueError("state mismatch")

    proxies_dict = None
    if proxy:
        proxies_dict = {"http": proxy, "https": proxy}

    token_resp = _post_form(
        TOKEN_URL,
        {
            "grant_type": "authorization_code",
            "client_id": CLIENT_ID,
            "code": cb["code"],
            "redirect_uri": redirect_uri,
            "code_verifier": code_verifier,
        },
        timeout=100,
        proxies=proxies_dict,
    )

    access_token = (token_resp.get("access_token") or "").strip()
    refresh_token = (token_resp.get("refresh_token") or "").strip()
    id_token = (token_resp.get("id_token") or "").strip()
    expires_in = _to_int(token_resp.get("expires_in"))

    claims = _jwt_claims_no_verify(id_token)
    email = str(claims.get("email") or "").strip()
    auth_claims = claims.get("https://api.openai.com/auth") or {}
    account_id = str(auth_claims.get("chatgpt_account_id") or "").strip()

    now = int(time.time())
    expired_rfc3339 = time.strftime(
        "%Y-%m-%dT%H:%M:%SZ", time.gmtime(now + max(expires_in, 0))
    )
    now_rfc3339 = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now))

    config = {
        "id_token": id_token,
        "access_token": access_token,
        "refresh_token": refresh_token,
        "account_id": account_id,
        "last_refresh": now_rfc3339,
        "email": email,
        "password": _temp_password,  # 添加邮箱密码
        "proxy_url": proxy,
        "type": "codex",
        "expired": expired_rfc3339,
    }

    return json.dumps(config, ensure_ascii=False, separators=(",", ":"))


# ==========================================
# 核心注册逻辑
# ==========================================


def run(proxy: Optional[str]) -> Optional[str]:
    proxies: Any = None
    if proxy:
        proxies = {"http": proxy, "https": proxy}

    logger.info("开始注册流程: proxy={}", proxy or "直连")
    s = requests.Session(proxies=proxies, impersonate="chrome")

    try:
        trace = s.get("https://cloudflare.com/cdn-cgi/trace", timeout=30)
        trace = trace.text
        loc_re = re.search(r"^loc=(.+)$", trace, re.MULTILINE)
        loc = loc_re.group(1) if loc_re else None
        logger.info("网络检查完成: loc={}", loc)
        if loc in ("CN", "HK", "RU"):
            raise RuntimeError("检查代理哦w - 所在地不支持")
    except Exception as e:
        logger.error("网络连接检查失败: proxy={} error={}", proxy, e)
        return None

    # 保留原来的 tempmail.ing 逻辑：邮箱创建和收件均直连
    email, dev_token, password = get_email_and_token()
    if not email or not dev_token:
        return None
    logger.info("临时邮箱准备完成: email={} dev_token={}", email, dev_token)

    oauth = generate_oauth_url()
    url = oauth.auth_url
    logger.debug("OAuth URL 已生成: redirect_uri={} state={}", oauth.redirect_uri, oauth.state)

    try:
        resp = s.get(url, timeout=100)
        if resp.status_code != 200:
            logger.error("OAuth 授权页请求失败: status={}", resp.status_code)
            return None
        did = s.cookies.get("oai-did")
        if not did:
            logger.error("未获取到 Device ID: oai-did cookie 缺失")
            return None
        logger.info("已获取 Device ID: did={}", did)

        signup_resp = s.post(
            "https://auth.openai.com/api/accounts/authorize/continue",
            headers={
                "referer": "https://auth.openai.com/create-account",
                "accept": "application/json",
                "content-type": "application/json",
                "openai-sentinel-token": _get_sentinel(s, did, "authorize_continue"),
            },
            data=json.dumps({"username": {"value": email, "kind": "email"}, "screen_hint": "signup"}),
        )
        logger.info("提交邮箱步骤完成: status={}", signup_resp.status_code)
        if signup_resp.status_code not in (200, 201):
            logger.error("注册表单被拒绝: body={}", signup_resp.text[:200])
            return None

        global _temp_password
        pwd = secrets.token_urlsafe(16) + "!A1"
        _temp_password = pwd
        reg_resp = s.post(
            "https://auth.openai.com/api/accounts/user/register",
            headers={
                "referer": "https://auth.openai.com/create-account/password",
                "accept": "application/json",
                "content-type": "application/json",
                "openai-sentinel-token": _get_sentinel(s, did, "username_password_create"),
            },
            data=json.dumps({"password": pwd, "username": email}),
        )
        logger.info("密码注册提交完成: status={}", reg_resp.status_code)
        if reg_resp.status_code not in (200, 201):
            logger.error("密码注册提交失败: body={}", reg_resp.text[:300])
            return None

        reg_data = reg_resp.json()
        otp_send_url = (reg_data.get("continue_url") or "").strip()
        logger.info("注册响应解析完成: continue_url={}", otp_send_url or "<empty>")
        if otp_send_url:
            otp_send_resp = s.get(otp_send_url, timeout=30)
            logger.info("验证码发送触发完成: status={}", otp_send_resp.status_code)
            if otp_send_resp.status_code != 200:
                logger.error("验证码发送失败: status={} body={}", otp_send_resp.status_code, otp_send_resp.text[:200])
                return None

        existing_messages = _list_tempmail_messages(email)
        existing_ids = {
            str(msg.get("id") or msg.get("messageId") or "").strip()
            for msg in existing_messages
            if isinstance(msg, dict) and str(msg.get("id") or msg.get("messageId") or "").strip()
        }

        code = get_oai_code(dev_token, email)
        if not code:
            return None

        code_resp = s.post(
            "https://auth.openai.com/api/accounts/email-otp/validate",
            headers={
                "referer": "https://auth.openai.com/email-verification",
                "accept": "application/json",
                "content-type": "application/json",
            },
            json={"code": code},
        )
        logger.info("验证码校验完成: status={}", code_resp.status_code)
        if code_resp.status_code != 200:
            logger.error("验证码校验失败: body={}", code_resp.text[:200])
            return None

        create_account_resp = s.post(
            "https://auth.openai.com/api/accounts/create_account",
            headers={
                "referer": "https://auth.openai.com/about-you",
                "accept": "application/json",
                "content-type": "application/json",
                "openai-sentinel-token": _get_sentinel(s, did, "authorize_continue"),
            },
            json={"name": "Neo", "birthdate": "2000-02-20"},
        )
        logger.info("账户创建完成: status={}", create_account_resp.status_code)
        if create_account_resp.status_code != 200:
            logger.error("账户创建失败: body={}", create_account_resp.text[:300])
            return None

        for login_attempt in range(1, 4):
            try:
                logger.info("开始登录换 token: attempt={}/3", login_attempt)
                s2 = requests.Session(proxies=proxies, impersonate="chrome")
                oauth2 = generate_oauth_url()
                init_resp = s2.get(oauth2.auth_url, timeout=100)
                if init_resp.status_code != 200:
                    raise RuntimeError(f"登录 OAuth 初始化失败: {init_resp.status_code}")

                did2 = s2.cookies.get("oai-did")
                if not did2:
                    raise RuntimeError("登录会话未能获取 oai-did")

                login_resp = s2.post(
                    "https://auth.openai.com/api/accounts/authorize/continue",
                    headers={
                        "referer": "https://auth.openai.com/log-in",
                        "accept": "application/json",
                        "content-type": "application/json",
                        "openai-sentinel-token": _get_sentinel(s2, did2, "authorize_continue"),
                    },
                    data=json.dumps({"username": {"value": email, "kind": "email"}, "screen_hint": "login"}),
                )
                if login_resp.status_code != 200:
                    raise RuntimeError(f"登录失败: {login_resp.status_code}: {login_resp.text[:200]}")

                login_continue_url = str((login_resp.json() or {}).get("continue_url") or "").strip()
                if login_continue_url:
                    s2.get(login_continue_url, timeout=30)

                pw_resp = s2.post(
                    "https://auth.openai.com/api/accounts/password/verify",
                    headers={
                        "referer": "https://auth.openai.com/log-in/password",
                        "accept": "application/json",
                        "content-type": "application/json",
                        "openai-sentinel-token": _get_sentinel(s2, did2, "authorize_continue"),
                    },
                    json={"password": pwd},
                )
                if pw_resp.status_code != 200:
                    raise RuntimeError(f"密码验证失败: {pw_resp.status_code}: {pw_resp.text[:200]}")

                s2.get(
                    "https://auth.openai.com/email-verification",
                    headers={"referer": "https://auth.openai.com/log-in/password"},
                    timeout=30,
                )

                code2 = get_oai_code(dev_token, email, ignore_ids=existing_ids, exclude_codes={code})
                if not code2:
                    raise RuntimeError("未收到登录 OTP")

                val_resp = s2.post(
                    "https://auth.openai.com/api/accounts/email-otp/validate",
                    headers={
                        "referer": "https://auth.openai.com/email-verification",
                        "accept": "application/json",
                        "content-type": "application/json",
                    },
                    json={"code": code2},
                )
                if val_resp.status_code != 200:
                    raise RuntimeError(f"登录 OTP 验证失败: {val_resp.status_code}: {val_resp.text[:200]}")

                val_data = val_resp.json() or {}
                consent_url = str(val_data.get("continue_url") or "").strip()
                if consent_url:
                    s2.get(consent_url, timeout=30)

                auth_cookie = s2.cookies.get("oai-client-auth-session")
                if not auth_cookie:
                    auth_cookie = s2.cookies.get("oai-client-auth-session", domain=".auth.openai.com")
                if not auth_cookie:
                    raise RuntimeError("登录后未能获取 oai-client-auth-session")

                auth_json = _decode_jwt_segment(auth_cookie.split(".")[0])
                workspaces = auth_json.get("workspaces") or []
                if not workspaces:
                    raise RuntimeError(f"Cookie 中无 workspaces: {list(auth_json.keys())}")
                workspace_id = str((workspaces[0] or {}).get("id") or "").strip()
                if not workspace_id:
                    raise RuntimeError("无法解析 workspace_id")

                select_resp = s2.post(
                    "https://auth.openai.com/api/accounts/workspace/select",
                    headers={
                        "referer": consent_url or "https://auth.openai.com/sign-in-with-chatgpt/codex/consent",
                        "accept": "application/json",
                        "content-type": "application/json",
                    },
                    json={"workspace_id": workspace_id},
                )
                if select_resp.status_code != 200:
                    raise RuntimeError(f"选择 workspace 失败: {select_resp.status_code}: {select_resp.text[:300]}")

                sel_data = select_resp.json() or {}
                if sel_data.get("page", {}).get("type", "") == "organization_select":
                    orgs = sel_data.get("page", {}).get("payload", {}).get("data", {}).get("orgs", [])
                    if orgs:
                        org_sel = s2.post(
                            "https://auth.openai.com/api/accounts/organization/select",
                            headers={"accept": "application/json", "content-type": "application/json"},
                            json={
                                "org_id": orgs[0].get("id", ""),
                                "project_id": orgs[0].get("default_project_id", ""),
                            },
                        )
                        if org_sel.status_code != 200:
                            raise RuntimeError(f"选择 organization 失败: {org_sel.status_code}: {org_sel.text[:300]}")
                        sel_data = org_sel.json() or {}

                continue_url = str(sel_data.get("continue_url") or "").strip()
                if not continue_url:
                    raise RuntimeError(f"未能获取 continue_url: {json.dumps(sel_data, ensure_ascii=False)[:500]}")

                current_url = continue_url
                for _ in range(1, 21):
                    final_resp = s2.get(current_url, allow_redirects=False, timeout=30)
                    location = final_resp.headers.get("Location") or ""
                    if location.startswith("http://localhost") and "code=" in location and "state=" in location:
                        return submit_callback_url(
                            callback_url=location,
                            code_verifier=oauth2.code_verifier,
                            redirect_uri=oauth2.redirect_uri,
                            expected_state=oauth2.state,
                            proxy=proxy,
                        )
                    if final_resp.status_code not in [301, 302, 303, 307, 308] or not location:
                        break
                    current_url = urllib.parse.urljoin(current_url, location)

                raise RuntimeError("未能在重定向链中捕获最终 Callback URL")
            except Exception as e:
                logger.warning("登录换 token 失败: attempt={}/3 error={}", login_attempt, e)
                if login_attempt >= 3:
                    logger.exception("登录换 token 连续失败")
                    return None
                time.sleep(2)

        return None

    except Exception:
        logger.exception("注册流程异常")
        return None


def main() -> None:
    parser = argparse.ArgumentParser(description="OpenAI 自动注册脚本")
    parser.add_argument("--proxy", default=None, help="代理地址")
    # 增加这个参数，防止 GitHub Action 报错
    parser.add_argument("--once", action="store_true", help="运行一次")
    
    # 即使 YAML 传了这些参数，我们也给个默认值防止崩溃
    parser.add_argument("--sleep_min", type=int, default=1)
    parser.add_argument("--sleep_max", type=int, default=2)

    args = parser.parse_args()

    # --- 核心修改：在 GitHub Action 模式下，不需要 while True ---
    logger.info("开始单次注册流程: proxy={}", args.proxy or "直连")

    try:
        token_json = run(args.proxy)

        if token_json:
            try:
                t_data = json.loads(token_json)
                fname_email = t_data.get("email", "unknown").replace("@", "_")
            except Exception:
                fname_email = "unknown"

            # 重点：为了匹配你 YAML 里的上传逻辑，文件必须存在 codex/ 目录下
            if not os.path.exists("codex"):
                os.makedirs("codex")
                
            file_name = f"codex/token_{fname_email}_{int(time.time())}.json"

            with open(file_name, "w", encoding="utf-8") as f:
                f.write(token_json)

            logger.info("注册成功: {}", file_name)
            print(f"[*] Success: {file_name}")
        else:
            logger.error("注册失败")
            exit(1) # 返回错误码，让 YAML 的 || true 接手

    except Exception:
        logger.exception("运行异常")
        exit(1)

if __name__ == "__main__":
    main()

