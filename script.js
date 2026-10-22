const PRESETS={
ideal:"add $t1, $s0, $s1\nsub $t2, $s2, $s3\nand $t3, $s4, $s5\nor $t4, $s6, $s7\nadd $t5, $s0, $s2",
raw:"add $t1, $s0, $s1\nsub $t2, $t1, $s3\nand $t3, $t1, $t2\nor $t4, $t1, $t3",
load:"lw $t1, 0($s0)\nadd $t2, $t1, $s1\nsub $t3, $t2, $s2\nsw $t3, 4($s0)",
branch:"addi $t1, $zero, 5\nbeq $t1, $t2, done\nadd $t3, $s0, $s1\nsub $t4, $s2, $s3\ndone: or $t5, $s4, $s5"};
const OPS=["add","sub","and","or","slt","addi","lw","sw","beq","bne","nop"];
const ST=["IF","ID","EX","MEM","WB"];
const $=id=>document.getElementById(id);
let R=[],total=0,cur=0,timer=null,log=[];

function parse(text){
  const out=[];
  text.split("\n").forEach((raw,n)=>{
    let l=raw.replace(/#.*/,"").replace(/^\s*\w+:/,"").trim();
    if(!l)return;
    const m=l.match(/^(\w+)\s*(.*)$/),op=m[1].toLowerCase();
    if(!OPS.includes(op))throw new Error("Line "+(n+1)+": unknown instruction “"+m[1]+"”.");
    const regs=(m[2].match(/\$\w+/g)||[]).filter(r=>true);
    const z=r=>r&&!/^\$(zero|0)$/i.test(r);
    const need={lw:2,sw:2,beq:2,bne:2,nop:0,addi:2}[op]??3;
    if(regs.length<need)throw new Error("Line "+(n+1)+": “"+op+"” needs "+need+" register"+(need===1?"":"s")+".");
    let dst=null,srcs=[],data=null;
    if(op==="lw"){dst=regs[0];srcs=[regs[1]]}
    else if(op==="sw"){data=regs[0];srcs=[regs[1]]}
    else if(op==="beq"||op==="bne"){srcs=regs.slice(0,2)}
    else if(op!=="nop"){dst=regs[0];srcs=regs.slice(1)}
    out.push({text:l.replace(/\s+/g," "),op,dst:z(dst)?dst:null,srcs:srcs.filter(z),data:z(data)?data:null,load:op==="lw",br:op==="beq"||op==="bne"});
  });
  if(!out.length)throw new Error("Add at least one instruction.");
  if(out.length>16)throw new Error("Please use 16 instructions or fewer.");
  return out;
}

function schedule(ins,fwd,brStall){
  const rs=[],writer={};log=[];
  ins.forEach((x,i)=>{
    const prev=rs[i-1];
    let IFn=i?prev.idS:1,bub=[];
    if(prev&&prev.ins.br&&brStall&&prev.ex+1>IFn){for(let c=IFn;c<prev.ex+1;c++)bub.push(c);IFn=prev.ex+1;
      log.push({t:"c",m:"I"+(i)+" ("+prev.ins.op+") is a branch: the next fetch waits until EX finishes, costing "+bub.length+" bubble cycles."});}
    const idS=Math.max(IFn+1,prev?prev.idE+1:0);
    let idE=idS;
    const deps=[];
    const regsToCheck=x.srcs.concat(fwd?[]:(x.data?[x.data]:[]));
    [...new Set(regsToCheck)].forEach(r=>{
      const j=writer[r];if(j===undefined)return;
      const p=rs[j],need=fwd?(p.ins.load?p.mem:0):p.wb;
      idE=Math.max(idE,need);deps.push({r,j,p});
    });
    const r={ins:x,i,IF:IFn,idS,idE,ex:idE+1,mem:idE+2,wb:idE+3,bub,fw:[]};
    rs.push(r);
    deps.forEach(({r:reg,j,p})=>{
      const why=p.ins.load?"load-use":"read-after-write";
      if(fwd&&p.wb>idE){
        r.fw.push(p.ins.load?"EX":"EX");
        if(!(idE>idS&&p.ins.load))log.push({t:"f",m:"I"+(i+1)+" needs "+reg+" from I"+(j+1)+" ("+why+"). Forwarded from "+(p.ins.load?"MEM":"EX")+", no stall."});
      }
      if(idE>idS&&(fwd?p.ins.load&&p.mem===idE:p.wb===idE)){
        log.push({t:"s",m:"I"+(i+1)+" needs "+reg+" from I"+(j+1)+" ("+why+"). "+(fwd?"Even with forwarding, the loaded value only exists after MEM":"Without forwarding it must wait for WB")+", so it stalls "+(idE-idS)+" cycle"+(idE-idS>1?"s":"")+"."});
      }
    });
    if(x.dst)writer[x.dst]=i;
  });
  return rs;
}

function cell(r,c){
  if(c>=r.IF&&c<r.idS)return{s:"IF",st:c>r.IF};
  if(c>=r.idS&&c<=r.idE)return{s:"ID",st:c<r.idE};
  if(c===r.ex)return{s:"EX",fw:r.fw.length>0};
  if(c===r.mem)return{s:"MEM"};
  if(c===r.wb)return{s:"WB"};
  if(r.bub.includes(c))return{bub:true};
  return null;
}

function run(){
  $("err").textContent="";
  let ins;
  try{ins=parse($("prog").value)}catch(e){$("err").textContent=e.message;return}
  stop();
  R=schedule(ins,$("fwd").checked,$("br").value==="stall");
  total=Math.max(...R.map(r=>r.wb));
  cur=total;
  const stalls=R.reduce((a,r)=>a+(r.idE-r.idS)+r.bub.length,0);
  $("sCyc").textContent=total;$("sStall").textContent=stalls;
  $("sCpi").textContent=(total/R.length).toFixed(2);
  $("sSpd").textContent=((5*R.length)/total).toFixed(2)+"×";
  const ul=$("log");ul.innerHTML="";
  if(!log.length){const li=document.createElement("li");li.className="f";li.textContent="No hazards found in this program: the pipeline never waits.";ul.append(li)}
  log.forEach(h=>{const li=document.createElement("li");li.className=h.t;li.textContent=h.m;ul.append(li)});
  draw();
}

function draw(){
  let h="<tr><th style='text-align:left;padding:0 10px;position:sticky;left:0;z-index:2'>Instruction</th>";
  for(let c=1;c<=total;c++)h+="<th class='"+(c===cur?"cur":"")+"'>"+c+"</th>";
  h+="</tr>";
  R.forEach(r=>{
    h+="<tr><td class='ins'><small>I"+(r.i+1)+"</small>"+esc(r.ins.text)+"</td>";
    for(let c=1;c<=total;c++){
      const x=cell(r,c),fut=c>cur?" fut":"";
      if(!x)h+="<td class='"+fut+"'></td>";
      else if(x.bub)h+="<td class='bub"+fut+"' title='Bubble: waiting for branch'>×</td>";
      else if(x.st)h+="<td class='st"+fut+"' title='Stalled in "+x.s+"'>"+x.s+"</td>";
      else h+="<td class='c "+x.s+(x.fw?" fw":"")+fut+"'"+(x.fw?" title='Receives a forwarded value'":"")+">"+x.s+"</td>";
    }
    h+="</tr>";
  });
  $("tbl").innerHTML=h;
  $("clk").textContent="Cycle "+cur+" of "+total;
  const colors={IF:"--if",ID:"--id",EX:"--ex",MEM:"--mem",WB:"--wb"};
  $("strip").innerHTML=ST.map(s=>{
    const r=R.find(r=>{const x=cell(r,cur);return x&&x.s===s});
    const x=r&&cell(r,cur);
    return "<div class='"+(r?"":"empty")+"' style='background:var("+colors[s]+")"+(x&&x.st?";outline:3px dashed var(--stall);outline-offset:-3px":"")+"'><b>"+s+"</b>"+(r?esc(r.ins.op)+" (I"+(r.i+1)+")"+(x.st?"<br>stalled":""):"idle")+"</div>";
  }).join("");
  $("play").textContent=timer?"Pause":"Play";
}
const esc=s=>s.replace(/[&<>]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;"}[c]));
function stop(){if(timer){clearInterval(timer);timer=null}}

$("play").onclick=()=>{
  if(timer){stop();draw();return}
  if(cur>=total)cur=0;
  cur=Math.max(cur,0);
  timer=setInterval(()=>{if(cur>=total){stop();draw();return}cur++;draw()},700);
  if(cur===0){cur=1}draw();
};
$("step").onclick=()=>{stop();cur=cur>=total?1:cur+1;draw()};
$("reset").onclick=()=>{stop();cur=1;draw()};
$("all").onclick=()=>{stop();cur=total;draw()};
$("prog").addEventListener("input",run);$("fwd").onchange=run;$("br").onchange=run;
document.querySelectorAll("[data-p]").forEach(b=>b.onclick=()=>{$("prog").value=PRESETS[b.dataset.p];if(b.dataset.p==="branch")$("br").value="stall";run()});

const QS=[
{q:"Which instruction pair causes a stall even when forwarding is enabled?",o:["add followed by sub using add’s result","lw followed by add using the loaded value","sub followed by and with no shared registers","sw followed by lw"],a:1,w:"A load’s data only exists after MEM, so the next instruction cannot get it in time through EX forwarding. One stall cycle is needed."},
{q:"Five instructions run on an ideal five-stage pipeline with no hazards. How many cycles do they take?",o:["5","9","10","25"],a:1,w:"Total cycles are n + 4 for n instructions: 5 + 4 = 9."},
{q:"What kind of hazard is a branch whose outcome is not yet known?",o:["Structural","Data","Control","Memory-ordering"],a:2,w:"A control hazard arises because the next instruction to fetch depends on the branch result."},
{q:"What does forwarding do?",o:["Skips the WB stage","Sends a result from a later stage straight to the ALU input","Fetches two instructions at once","Predicts branch direction"],a:1,w:"Forwarding bypasses the register file so a dependent instruction can use a result before it is written back."},
{q:"With no forwarding, add $t1,… is followed by sub $t2,$t1,…. How many stall cycles occur?",o:["0","1","2","3"],a:2,w:"The sub must reach ID in the same cycle as the add’s WB. That is two cycles later than normal, so two stalls."}];
let done=0,right=0;
$("quizBox").innerHTML=QS.map((x,qi)=>"<div class='q' id='q"+qi+"'><p>"+(qi+1)+". "+x.q+"</p>"+x.o.map((o,oi)=>"<button data-q='"+qi+"' data-o='"+oi+"'>"+o+"</button>").join("")+"<p class='why'></p></div>").join("");
document.querySelectorAll(".q button").forEach(b=>b.onclick=()=>{
  const qi=+b.dataset.q,box=$("q"+qi);
  if(box.dataset.done)return;box.dataset.done=1;
  const x=QS[qi],oi=+b.dataset.o;
  box.querySelectorAll("button").forEach((bb,i)=>{if(i===x.a)bb.classList.add("ok");else if(i===oi)bb.classList.add("no")});
  box.querySelector(".why").textContent=(oi===x.a?"Correct. ":"Not quite. ")+x.w;
  done++;if(oi===x.a)right++;
  $("score").textContent=done===QS.length?"You scored "+right+" out of "+QS.length+".":"Answered "+done+" of "+QS.length+".";
});

$("prog").value=PRESETS.load;run();
