// Notes-aware AI assistant: local retrieval over the notebook + chat with a choice of providers.
// Retrieval runs entirely in the browser; only the excerpts chosen for a question are sent to the model.
// Providers: Anthropic (Claude), OpenAI, Ollama (local), any OpenAI-compatible server (LM Studio etc.).
// The project is plain browser ES modules without a bundler or package manager, so requests are made
// with fetch against the documented HTTP APIs.

// ---------- retrieval ----------
const CJK=/[぀-ヿ㐀-鿿豈-﫿ｦ-ﾟ]/;
export function terms(text){
 const s=String(text||'').toLowerCase().normalize('NFKC'),out=[];
 for(const w of s.match(/[a-z0-9][a-z0-9._:/@-]*/g)||[])if(w.length>=2)out.push(w);
 // Japanese / Chinese: character bigrams (no dictionary needed), plus single kanji for one-character words
 const runs=s.match(/[぀-ヿ㐀-鿿豈-﫿ｦ-ﾟー]+/g)||[];
 for(const r of runs){if(r.length===1){out.push(r);continue;}for(let i=0;i<r.length-1;i++)out.push(r.slice(i,i+2));}
 return out;
}
const STOP=new Set(['して','する','した','です','ます','ます','こと','もの','ので','から','まで','には','では','とは','ってい','てい','いる','ある','この','その','あの','どう','なに','何を','何が','教え','えて','てく','くだ','ださ','さい','につ','つい','いて','ください','about','what','the','and','for','with']);
export function pageText(p){return [p.title||'',...(p.blocks||[]).filter(b=>b.type==='text'&&b.text).map(b=>b.text)].join('\n').trim();}
// docs: [{id,title,where,updatedAt,text}]
export function searchDocs(docs,query,{limit=6}={}){
 const q=[...new Set(terms(query))].filter(t=>!STOP.has(t));
 const n=docs.length||1;
 const df=new Map();
 const prepared=docs.map(d=>{const body=d.text.toLowerCase().normalize('NFKC'),title=String(d.title||'').toLowerCase().normalize('NFKC');return {d,body,title};});
 for(const t of q){let c=0;for(const x of prepared)if(x.body.includes(t))c++;df.set(t,c);}
 const scored=prepared.map(x=>{
  let score=0;
  for(const t of q){
   const c=df.get(t);if(!c)continue;const idf=Math.log(1+n/c);
   let k=0,i=-1;while((i=x.body.indexOf(t,i+1))>=0&&k<8)k++;
   if(k)score+=idf*(1+Math.log(k));
   if(x.title.includes(t))score+=idf*2;
  }
  return {doc:x.d,score};
 }).filter(x=>x.score>0).sort((a,b)=>b.score-a.score||((b.doc.updatedAt||0)-(a.doc.updatedAt||0)));
 return {hits:scored.slice(0,limit),terms:q};
}
// Pick the text to send: whole pages when everything fits, otherwise windows around the matches.
export function buildContext(docs,query,{budget=20000,perDoc=4000,limit=6}={}){
 const total=docs.reduce((s,d)=>s+d.text.length,0);
 const {hits,terms:q}=searchDocs(docs,query,{limit});
 let chosen;
 if(total<=budget){ // small notebook: send all of it, best matches first
  const order=new Map(hits.map((h,i)=>[h.doc.id,i]));
  chosen=[...docs].filter(d=>d.text).sort((a,b)=>(order.has(a.id)?order.get(a.id):1e6)-(order.has(b.id)?order.get(b.id):1e6)||((b.updatedAt||0)-(a.updatedAt||0))).map(d=>({doc:d,text:d.text}));
 } else {
  const list=hits.length?hits.map(h=>h.doc):[...docs].sort((a,b)=>(b.updatedAt||0)-(a.updatedAt||0)).slice(0,3); // nothing matched: newest pages
  let left=budget;chosen=[];
  for(const d of list){if(left<300)break;const take=Math.min(perDoc,left);chosen.push({doc:d,text:excerpt(d.text,q,take)});left-=chosen.at(-1).text.length;}
 }
 const sources=chosen.map((c,i)=>({n:i+1,id:c.doc.id,title:c.doc.title||'名称未設定',where:c.doc.where||''}));
 const text=chosen.map((c,i)=>'['+(i+1)+'] 「'+(c.doc.title||'名称未設定')+'」'+(c.doc.where?'（'+c.doc.where+'）':'')+(c.doc.updatedAt?' 更新 '+new Date(c.doc.updatedAt).toLocaleDateString('ja-JP'):'')+'\n'+c.text).join('\n\n---\n\n');
 return {text,sources,matched:hits.length>0};
}
export function excerpt(text,q,max){
 if(text.length<=max)return text;
 const low=text.toLowerCase().normalize('NFKC'),spots=[];
 for(const t of q){let i=-1,k=0;while((i=low.indexOf(t,i+1))>=0&&k<20){spots.push(i);k++;}}
 if(!spots.length)return text.slice(0,max)+'…';
 spots.sort((a,b)=>a-b);
 const win=Math.max(200,Math.floor(max/Math.min(6,spots.length))),ranges=[];
 for(const s of spots){const a=Math.max(0,s-Math.floor(win/2)),b=Math.min(text.length,a+win);const last=ranges.at(-1);if(last&&a<=last[1])last[1]=Math.max(last[1],b);else ranges.push([a,b]);}
 let out='',used=0;
 for(const [a,b] of ranges){if(used>=max)break;const piece=text.slice(a,Math.min(b,a+max-used));out+=(a>0?'…':'')+piece+(b<text.length?'…':'')+'\n';used+=piece.length;}
 return out.trim();
}

// ---------- prompts ----------
export const SYSTEM_PROMPT=`あなたは手書きメモアプリ「余白ノート」のアシスタントです。利用者のノートの抜粋が【ノート】として渡されます。
- 質問には、まず【ノート】の内容を根拠に、日本語で簡潔に答えてください。
- 根拠にした抜粋は、文中や文末に [1] のように番号で示してください。番号は【ノート】の見出しの番号です。
- 【ノート】に答えが無いときは「ノートには見当たりません」とはっきり書いてください。そのうえで一般的な知識で補う場合は、ノートの内容と区別して「一般的には」と書いてください。
- 手書きの絵や線の内容は【ノート】に含まれていません。`;
export function userTurn(question,context,scopeLabel){
 return '【ノート】（範囲：'+scopeLabel+'）\n'+(context.text||'（該当する文章はありません）')+'\n\n【質問】\n'+question;
}

// ---------- providers ----------
export const PROVIDERS={
 anthropic:{label:'Claude（Anthropic・クラウド）',cloud:true,needsKey:true,endpoint:'https://api.anthropic.com',models:['claude-opus-5-5','claude-sonnet-5-5','claude-haiku-5-5'],budget:40000},
 openai:{label:'OpenAI（クラウド）',cloud:true,needsKey:true,endpoint:'https://api.openai.com/v1',models:['gpt-5-mini','gpt-5','gpt-5-nano'],budget:40000},
 ollama:{label:'Ollama（この PC のローカルLLM）',cloud:false,needsKey:false,endpoint:'http://localhost:11434',models:['qwen3:8b','gemma3:12b','llama3.1:8b'],budget:9000},
 compat:{label:'LM Studio（この PC のローカルLLM・OpenAI 互換）',cloud:false,needsKey:false,endpoint:'http://localhost:1234/v1',models:[],budget:9000},
 // Subscriptions (Claude Pro/Max, ChatGPT Plus/Pro) have no API for other apps: the app copies the question with the
 // note excerpts, opens the chat site, and the user pastes; the answer is pasted back to keep it with its sources.
 'claude-web':{label:'Claude（契約中のサブスクで・コピーして開く）',cloud:true,manual:true,site:'https://claude.ai/new',siteName:'Claude',models:[],budget:40000},
 'chatgpt-web':{label:'ChatGPT（契約中のサブスクで・コピーして開く）',cloud:true,manual:true,site:'https://chatgpt.com/',siteName:'ChatGPT',models:[],budget:40000},
};
// One self-contained message for a chat site: the instructions, the earlier turns, the excerpts and the question.
export function manualPrompt(history,question,context,scopeLabel){
 const earlier=history.length?'【これまでのやり取り】\n'+history.map(m=>(m.role==='user'?'質問：':'答え：')+m.content).join('\n')+'\n\n':'';
 return SYSTEM_PROMPT+'\n\n'+earlier+userTurn(question,context,scopeLabel);
}
// Anthropic models that accept the server-side refusal fallback in its "default" form.
const FALLBACK_MODELS=new Set(['claude-opus-5-5','claude-sonnet-5-5','claude-opus-5','claude-fable-5-1']);

async function* sseLines(res){ // yields "data:" payloads of a Server-Sent Events stream
 const reader=res.body.getReader(),dec=new TextDecoder();let buf='';
 for(;;){
  const {value,done}=await reader.read();if(done)break;
  buf+=dec.decode(value,{stream:true});let i;
  while((i=buf.search(/\r?\n/))>=0){const line=buf.slice(0,i);buf=buf.slice(i+(buf[i]==='\r'?2:1));if(line.startsWith('data:'))yield line.slice(5).trim();}
 }
 if(buf.startsWith('data:'))yield buf.slice(5).trim();
}
async function* ndjson(res){
 const reader=res.body.getReader(),dec=new TextDecoder();let buf='';
 for(;;){const {value,done}=await reader.read();if(done)break;buf+=dec.decode(value,{stream:true});let i;while((i=buf.indexOf('\n'))>=0){const line=buf.slice(0,i).trim();buf=buf.slice(i+1);if(line)yield JSON.parse(line);}}
 if(buf.trim())yield JSON.parse(buf);
}
async function failure(res,provider){
 let detail='';try{const t=await res.text();try{const j=JSON.parse(t);detail=j.error?.message||j.error||j.message||t;}catch{detail=t;}}catch{}
 const hint=res.status===401||res.status===403?'（API キーを確認してください）':res.status===404?'（モデル名や接続先を確認してください）':res.status===429?'（利用上限か混雑です。少し待ってください）':'';
 return new Error(PROVIDERS[provider]?.label+' の応答 '+res.status+hint+(detail?'：'+String(detail).slice(0,200):''));
}
// messages: [{role:'user'|'assistant', content:string}]; onText(delta) is called as text streams in.
export async function chat(settings,{system,messages,onText=()=>{},signal,fetchImpl=(...a)=>fetch(...a)}){
 const p=settings.provider,cfg=settings[p]||{},model=(cfg.model||PROVIDERS[p].models[0]||'').trim();
 if(PROVIDERS[p].manual)throw new Error('この方式は「コピーして開く」で使います。');
 const base=String(cfg.endpoint||PROVIDERS[p].endpoint).replace(/\/+$/,'');
 if(!model)throw new Error('モデル名を設定してください。');
 if(PROVIDERS[p].needsKey&&!cfg.key)throw new Error('API キーを設定してください。');
 let out='';const emit=t=>{if(t){out+=t;onText(t);}};
 if(p==='anthropic'){
  const headers={'content-type':'application/json','x-api-key':cfg.key,'anthropic-version':'2023-06-01','anthropic-dangerous-direct-browser-access':'true'};
  const body={model,max_tokens:16000,stream:true,system,messages};
  if(FALLBACK_MODELS.has(model)){headers['anthropic-beta']='server-side-fallback-2026-07-01';body.fallbacks='default';}
  const res=await fetchImpl(base+'/v1/messages',{method:'POST',headers,body:JSON.stringify(body),signal});
  if(!res.ok)throw await failure(res,p);
  let stop=null;
  for await(const data of sseLines(res)){
   let ev;try{ev=JSON.parse(data);}catch{continue;}
   if(ev.type==='content_block_delta'&&ev.delta?.type==='text_delta')emit(ev.delta.text);
   else if(ev.type==='message_delta'&&ev.delta?.stop_reason)stop=ev.delta.stop_reason;
   else if(ev.type==='error')throw new Error('Claude の応答エラー：'+(ev.error?.message||''));
  }
  if(stop==='refusal'&&!out)throw new Error('この質問には答えられないと判断されました。言い方を変えてお試しください。');
  if(stop==='max_tokens')emit('\n（長さの上限で途中までになりました）');
  return out;
 }
 if(p==='ollama'){
  const res=await fetchImpl(base+'/api/chat',{method:'POST',headers:{'content-type':'application/json'},body:JSON.stringify({model,stream:true,messages:[{role:'system',content:system},...messages]}),signal});
  if(!res.ok)throw await failure(res,p);
  for await(const j of ndjson(res)){if(j.error)throw new Error('Ollama：'+j.error);emit(j.message?.content||'');}
  return out;
 }
 // openai / OpenAI-compatible: Chat Completions with streaming
 const headers={'content-type':'application/json'};if(cfg.key)headers.authorization='Bearer '+cfg.key;
 const res=await fetchImpl(base+'/chat/completions',{method:'POST',headers,body:JSON.stringify({model,stream:true,messages:[{role:'system',content:system},...messages]}),signal});
 if(!res.ok)throw await failure(res,p);
 for await(const data of sseLines(res)){if(data==='[DONE]')break;let j;try{j=JSON.parse(data);}catch{continue;}if(j.error)throw new Error(j.error.message||'エラー');emit(j.choices?.[0]?.delta?.content||'');}
 return out;
}
// Model list for the local servers (and OpenAI-compatible ones).
export async function listModels(settings,{fetchImpl=(...a)=>fetch(...a)}={}){
 const p=settings.provider,cfg=settings[p]||{},base=String(cfg.endpoint||PROVIDERS[p].endpoint).replace(/\/+$/,'');
 if(p==='ollama'){const r=await fetchImpl(base+'/api/tags');if(!r.ok)throw await failure(r,p);const j=await r.json();return (j.models||[]).map(m=>m.name||m.model).filter(Boolean);}
 if(p==='compat'||p==='openai'){const h={};if(cfg.key)h.authorization='Bearer '+cfg.key;const r=await fetchImpl(base+'/models',{headers:h});if(!r.ok)throw await failure(r,p);const j=await r.json();return (j.data||[]).map(m=>m.id).filter(Boolean);}
 return PROVIDERS[p].models.slice();
}
export function defaultSettings(){return {provider:'anthropic',anthropic:{model:'claude-opus-5-5',key:''},openai:{model:'gpt-5-mini',key:''},ollama:{model:'',endpoint:PROVIDERS.ollama.endpoint},compat:{model:'',endpoint:PROVIDERS.compat.endpoint,key:''},'claude-web':{},'chatgpt-web':{}};}
