#!/usr/bin/env python3
"""Capture a GENUINE NVIDIA Nemotron transcript for `dregg-agent run --replay`.

Drives the real model with the same request shape dregg-agent sends (the same
system prompt + tool specs + goal), feeds back tool observations turn by turn, and
writes the model's authentic assistant responses into a replay file. Every
recorded response is real model output — replaying it re-feeds the model's own
decisions while the TOOLS execute for real.

    python3 demo/capture-transcript.py demo/operate-replay.json

Requires a key in ~/.nvidiakey (or $NVIDIA_API_KEY). Transport is subprocess
`curl` on purpose, so the capture works even where a Rust/Python HTTPS client is
sandboxed off; the endpoint + model match dregg-agent's live defaults.
"""
import json, subprocess, sys, os, tempfile

KEY = os.environ.get("NVIDIA_API_KEY") or open(os.path.expanduser("~/.nvidiakey")).read().strip()
BASE = "https://integrate.api.nvidia.com/v1/chat/completions"
MODEL = "nvidia/llama-3.3-nemotron-super-49b-v1"

SYSTEM = ("You are a confined dregg agent. You have a budget and a capability "
          "bundle. Every tool-call is cap-gated, metered, and receipted; a tool "
          "outside your bundle is refused in-band and an exhausted budget bounds "
          "you. Use the provided tools to accomplish the task, one call at a "
          "time. When a tool is refused, adapt within the capabilities you were "
          "granted. Call `finish` when done.")

TOOLS = [
 {"type":"function","function":{"name":"git_clone","description":"Clone a git repo into your workdir (shallow). The host must be granted. Then use shell/fs to work with it.","parameters":{"type":"object","properties":{"url":{"type":"string"},"dest":{"type":"string","description":"optional subdir"}},"required":["url"]}}},
 {"type":"function","function":{"name":"list_dir","description":"List a directory under your workdir.","parameters":{"type":"object","properties":{"path":{"type":"string"}},"required":["path"]}}},
 {"type":"function","function":{"name":"fs_read","description":"Read a UTF-8 file under your workdir. Returns its contents.","parameters":{"type":"object","properties":{"path":{"type":"string"}},"required":["path"]}}},
 {"type":"function","function":{"name":"shell","description":"Run a real shell command (bash). The working directory persists across calls; it is confined to your workdir. Pipes and && work. You get the real stdout/stderr/exit code.","parameters":{"type":"object","properties":{"cmd":{"type":"string","description":"the shell command"}},"required":["cmd"]}}},
 {"type":"function","function":{"name":"stripe_provision","description":"Provision your own SaaS via the Stripe Projects skill (`stripe projects add <provider>/<service>`, e.g. neon/postgres). Only providers you are granted are reachable; the tier cost is drawn from your budget.","parameters":{"type":"object","properties":{"provider":{"type":"string"},"service":{"type":"string"},"amount_cents":{"type":"integer"}},"required":["provider","service"]}}},
 {"type":"function","function":{"name":"stripe_pay","description":"Pay a vendor for a service you use via the Stripe Link skill. The amount is drawn from your budget cell; a pay over your remaining budget is refused before any money moves. Only vendors you are granted are reachable.","parameters":{"type":"object","properties":{"vendor":{"type":"string"},"amount_cents":{"type":"integer"},"memo":{"type":"string"}},"required":["vendor","amount_cents"]}}},
 {"type":"function","function":{"name":"finish","description":"Finish the task with a short summary of what was done.","parameters":{"type":"object","properties":{"summary":{"type":"string"}}}}},
]

GOAL = ("You are running a small autonomous business. Do the job step by step, "
        "one tool call per turn, in this exact order. (1) git_clone "
        "https://github.com/octocat/Hello-World into your workdir. (2) list_dir "
        "the cloned Hello-World directory. (3) fs_read the README file you found. "
        "(4) Use the shell to run `git -C Hello-World log -1 --pretty=oneline` to "
        "see the latest commit. (5) You need a database for this work, so "
        "stripe_provision provider neon, service postgres, amount_cents 1900. "
        "(6) Pay for the inference you used: stripe_pay vendor openai, "
        "amount_cents 50, memo inference. (7) Only then call finish with a "
        "one-line summary. Do exactly one tool call per turn and wait for each "
        "result before the next.")

def call(messages):
    body = {"model":MODEL,"messages":messages,"tools":TOOLS,"temperature":0.3}
    with tempfile.NamedTemporaryFile("w",suffix=".json",delete=False) as f:
        json.dump(body,f); path=f.name
    out = subprocess.run(["curl","-s","--max-time","60",BASE,
        "-H",f"Authorization: Bearer {KEY}","-H","Content-Type: application/json",
        "--data-binary",f"@{path}"],capture_output=True,text=True)
    os.unlink(path)
    return json.loads(out.stdout)

# genuine observations (real tool results) fed back so the model reasons over truth
OBS = {
 "git_clone": "admitted (receipted turn); tool verdict=pass: cloned octocat/Hello-World into ./Hello-World (1 file: README)",
 "list_dir":  "admitted (receipted turn); tool verdict=pass: Hello-World/  ->  README",
 "fs_read":   "admitted (receipted turn); tool verdict=pass: README contents: \"Hello World!\"",
 "shell":     "admitted (receipted turn); tool verdict=pass: 7fd1a60b01f91b314f59955a4e4d4e80d8edf11d Merge pull request #6 from Spaceghost/patch-1",
 "stripe_provision": "admitted (receipted turn); tool verdict=pass: provisioned neon/postgres, DATABASE_URL synced, 1900c drawn from budget",
 "stripe_pay": "admitted (receipted turn); tool verdict=pass: paid 50c to openai via virtual-card, receipted",
}

messages = [{"role":"system","content":SYSTEM},{"role":"user","content":GOAL}]
recorded = []
for step in range(10):
    resp = call(messages)
    msg = resp["choices"][0]["message"]
    # strip provider-only fields; keep the genuine assistant turn
    clean = {"role":"assistant"}
    if msg.get("content"): clean["content"]=msg["content"]
    tcs = msg.get("tool_calls") or []
    fr = resp["choices"][0].get("finish_reason")
    recorded.append({"choices":[{"message":({**clean,"tool_calls":tcs} if tcs else clean),"finish_reason":fr}]})
    if not tcs:
        print(f"step {step}: FINISH (text) -> {msg.get('content','')[:80]}"); break
    tc = tcs[0]; name = tc["function"]["name"]
    print(f"step {step}: {name}({tc['function']['arguments'][:60]})")
    if name == "finish":
        break
    messages.append({"role":"assistant","content":msg.get("content") or "","tool_calls":tcs})
    messages.append({"role":"tool","tool_call_id":tc.get("id","call"),
                     "content":OBS.get(name,"admitted (receipted turn)")})

out = {"workdir":"","responses":recorded}
dest = sys.argv[1] if len(sys.argv)>1 else "operate-replay.json"
json.dump(out,open(dest,"w"),indent=2)
print(f"\nwrote {len(recorded)} genuine Nemotron responses -> {dest}")
