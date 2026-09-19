import { DEFAULT_TEXT_COLOR, MIN_FONT, MAX_FONT, normalizeRuns } from './model.mjs';
const BLOCK_TAGS=new Set(['DIV','P','LI','UL','OL','H1','H2','H3','H4','H5','H6','BLOCKQUOTE','PRE','TABLE','TR','SECTION','ARTICLE']);
export function toHex(color) {
 if(!color)return null;const c=String(color).trim().toLowerCase();
 let m=c.match(/^#([0-9a-f]{6})$/);if(m)return '#'+m[1];
 m=c.match(/^#([0-9a-f])([0-9a-f])([0-9a-f])$/);if(m)return '#'+m[1]+m[1]+m[2]+m[2]+m[3]+m[3];
 m=c.match(/^rgba?\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)/);if(m)return '#'+[m[1],m[2],m[3]].map(n=>Math.min(255,Number(n)).toString(16).padStart(2,'0')).join('');
 return null;
}
function formatOf(el,inherited) {
 const f={...inherited},tag=el.tagName,st=el.style;
 if(tag==='B'||tag==='STRONG'||/^(bold|bolder|[6-9]00)$/.test(st.fontWeight))f.bold=true;
 else if(/^(normal|[1-5]00)$/.test(st.fontWeight))delete f.bold;
 if(/px$/.test(st.fontSize)){const size=Math.round(parseFloat(st.fontSize));if(size>=MIN_FONT&&size<=MAX_FONT)f.size=size;}
 const color=toHex(st.color||(tag==='FONT'?el.getAttribute('color'):null));
 if(color){if(color===DEFAULT_TEXT_COLOR)delete f.color;else f.color=color;}
 return f;
}
// Read the editor DOM back into runs. Line breaks become "\n" inside runs; <hr> becomes {hr:true}.
export function domToRuns(root) {
 const runs=[];
 const atLineStart=()=>{const last=runs.at(-1);return !last||last.hr||last.text.endsWith('\n');};
 const push=(text,f)=>{if(!text)return;const run={text};if(f.bold)run.bold=true;if(f.size)run.size=f.size;if(f.color)run.color=f.color;runs.push(run);};
 const walk=(node,f)=>{
  for(const child of node.childNodes){
   if(child.nodeType===3){push(child.data.replace(/\u00a0/g,' '),f);continue;}
   if(child.nodeType!==1)continue;
   const tag=child.tagName;
   if(tag==='BR'){push('\n',f);continue;}
   if(tag==='HR'){runs.push({hr:true});continue;}
   if(tag==='SCRIPT'||tag==='STYLE'||tag==='TEMPLATE')continue;
   if(BLOCK_TAGS.has(tag)&&!atLineStart())push('\n',f);
   walk(child,formatOf(child,f));
  }
 };
 walk(root,{});
 return normalizeRuns(runs);
}
// Build the editor DOM from runs using DOM APIs only (no HTML strings).
export function runsToDom(editor,runs) {
 editor.replaceChildren();
 for(const r of runs){
  if(r.hr){editor.append(document.createElement('hr'));continue;}
  const lines=r.text.split('\n');
  lines.forEach((line,i)=>{
   if(i>0)editor.append(document.createElement('br'));
   if(!line)return;
   let node=document.createTextNode(line);
   if(r.size||r.color){const span=document.createElement('span');if(r.size)span.style.fontSize=r.size+'px';if(r.color)span.style.color=r.color;span.append(node);node=span;}
   if(r.bold){const b=document.createElement('b');b.append(node);node=b;}
   editor.append(node);
  });
 }
 const last=runs.at(-1);
 if(last&&(last.hr||last.text.endsWith('\n')))editor.append(document.createElement('br'));
}
