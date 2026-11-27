#!/usr/bin/env python3
"""Run extracted GitHub Actions logic in an isolated mocked namespace; never call network."""
import base64,hashlib,json,os,pathlib,textwrap
root=pathlib.Path(__file__).resolve().parents[1]
w=(root/".github/workflows/submit-upstream-pr.yml").read_text()
src=textwrap.dedent(w.split("          python3 - <<'PY'\n",1)[1].rsplit("\n          PY",1)[0])
assert src.rstrip().endswith("main()")
src=src.rstrip()[:-len("main()")]
os.environ.update(UPSTREAM_PR_TOKEN="mock",QUEUE_TOKEN="mock",GITHUB_RUN_ID="0")
ns={};exec(compile(src,"candidate_workflow.py","exec"),ns)
unit="L-meta-9999999";file="lean/PEqualNP/Outside/L_meta_9999999.lean";head="b"*40;base="a"*40;gap={"id":unit,"statement":"True","file":file,"module":"PEqualNP.Outside.L_meta_9999999","imports":["PEqualNP.Defs"]}
proof=b"theorem mock : True := True.intro\n"
q={"unit":unit,"branch":"isolated-proof","head_sha":head,"file":file,"lease":"mock-lease","proof_sha256":hashlib.sha256(proof).hexdigest(),"base_sha":base,"statement_hash":ns["gap_hash"](gap)}
old={"number":77,"title":unit,"state":"open","head":{"sha":"c"*40},"user":{"login":"vipox233"},"html_url":"https://example.invalid/pr/77"}
calls=[]
def mock_gh(path,method="GET",data=None,token=None,expected=(200,)):
 calls.append((method,path))
 if path.startswith("/search/issues?"):return 200,{"total_count":1,"items":[{"title":unit,"user":{"login":"vipox233"},"number":77}]}
 if path.endswith("/pulls/77"):return 200,old
 raise AssertionError("unexpected call "+path)
ns["contents"]=lambda path,ref="pr-queue":(404,None)
ns["gh"]=mock_gh
ns["existing"]=lambda *a:None
assert ns["process"](q)["status"]=="DUPLICATE"
assert all(x[0]=="GET" for x in calls)
ns["contents"]=lambda path,ref="pr-queue":(200,[{"name":unit+"-prior.json"}])
ns["read_json"]=lambda path:("sha",{"status":"SUBMITTED","pr":77})
calls.clear();assert ns["process"](q)["status"]=="DUPLICATE";assert not any("/search/" in x[1] for x in calls)
ns["existing"]=lambda *a:dict(old,head={"sha":head})
calls.clear();assert ns["process"](q)["already_exists"] and not calls
ns["existing"]=lambda *a:None
ns["account_existing"]=lambda unit:None
ns["contents"]=lambda path,ref="pr-queue":(200,{"type":"file","size":len(proof),"encoding":"base64","content":base64.b64encode(proof).decode()})
def gh(path,method="GET",data=None,token=None,expected=(200,)):
 calls.append((method,path))
 if path.endswith("contents/STOP?ref=main"):return 404,None
 if "/branches/" in path:return 200,{"commit":{"sha":head}}
 if "/compare/" in path:return 200,{"ahead_by":1,"commits":[{"sha":head,"parents":[{"sha":base}]}],"files":[{"status":"added","filename":file}]}
 if path.endswith("/pulls") and method=="POST":return 201,dict(old,head={"sha":head})
 raise AssertionError(path)
def request(url,method="GET",**kw):
 calls.append((method,url))
 if "/row?" in url:return 200,{"gaps":[gap]}
 if "/step?" in url:return 200,{"state":"pr_open"}
 if "/beat?" in url:return 200,{"lease":{"id":"mock-lease"}}
 if "/release?" in url:return 200,{"released":True}
 raise AssertionError(url)
ns["gh"]=gh;ns["request"]=request
for field,bad in [("proof_sha256","0"*64),("base_sha","0"*40),("statement_hash","0"*64)]:
 calls.clear()
 try:ns["process"](dict(q,**{field:bad}));raise AssertionError("accepted bad "+field)
 except RuntimeError:assert not any(x[0]=="POST" for x in calls)
calls.clear();res=ns["process"](q);assert res["status"]=="SUBMITTED" and res["lease_released"] and sum(x[0]=="POST" and x[1].endswith("/pulls") for x in calls)==1
# Inline proof: mock all fork Git data operations, validate exact parent and bytes.
inline=dict(q,proof_content_b64=base64.b64encode(proof).decode())
inline.pop("branch");inline.pop("head_sha")
branch="hub/"+unit+"-"+base[:12]+"-"+q["proof_sha256"][:16]
forkcalls=[]
def fork_gh(path,method="GET",data=None,token=None,expected=(200,)):
 forkcalls.append((method,path,data))
 if "/git/ref/heads/" in path:return 404,None
 if path.endswith("/git/commits/"+base):return 200,{"tree":{"sha":"c"*40}}
 if path.endswith("/git/blobs") and method=="POST":
  assert base64.b64decode(data["content"])==proof
  return 201,{"sha":"d"*40}
 if path.endswith("/git/trees") and method=="POST":
  assert data["base_tree"]=="c"*40 and data["tree"]==[{"path":file,"mode":"100644","type":"blob","sha":"d"*40}]
  return 201,{"sha":"e"*40}
 if path.endswith("/git/commits") and method=="POST":
  assert data["parents"]==[base] and data["tree"]=="e"*40
  return 201,{"sha":head}
 if path.endswith("/git/refs") and method=="POST":
  assert data=={"ref":"refs/heads/"+branch,"sha":head}
  return 201,{"object":{"sha":head}}
 raise AssertionError(path)
ns["gh"]=fork_gh
assert ns["inline_branch"](inline)==(branch,head)
assert sum(m=="POST" for m,p,d in forkcalls)==4
forkcalls.clear()
try:ns["inline_branch"](dict(inline,proof_sha256="0"*64));raise AssertionError("bad inline hash accepted")
except RuntimeError:assert not forkcalls
ns["gh"]=lambda *a,**k:(200,{"object":{"sha":head}})
assert ns["inline_branch"](inline)==(branch,head)
ns["gh"]=gh
ns["inline_branch"]=lambda q:(branch,head)
calls.clear();assert ns["process"](inline)["status"]=="SUBMITTED"
print(json.dumps({"ok":True,"duplicate_search":True,"duplicate_ledger":True,"same_head_idempotent":True,"proof_hash_mismatch":True,"base_mismatch":True,"statement_mismatch":True,"mock_racing_submit":True,"inline_git_data":True,"inline_hash_guard":True,"inline_retry_ref":True,"inline_process":True,"real_pr_created":False}))
