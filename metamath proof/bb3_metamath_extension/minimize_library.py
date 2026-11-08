"""Untrusted, reproducible consolidation; outputs require official verification.

Merge only earlier assertions with identical expressions and mandatory
hypothesis expressions, and no stronger mandatory disjointness constraints.
Rewrite/recompress proof references, then retain the dependency closure of
the selected general interfaces and the unchanged trusted core.
"""
from pathlib import Path
from collections import Counter,defaultdict
import hashlib,itertools,json,re,sys,time

ROOT=Path(__file__).resolve().parent
ROOTS=[
 'orbit-sound',
 'translated-affine-sound',
 'cps-modulus-sound',
 'wide-gate-sound',
 'annotated-cps-linked-certificate-sound',
 'annotated-cps-letter-certificate-projection',
]

def parse(source):
    records=[];rules={};variables=set();floats=[];essential=[]
    adjacency=defaultdict(set);scopes=[]
    iterator=iter(m for m in re.finditer(r'\$\([\s\S]*?\$\)|\S+',source) if not m.group().startswith('$('))
    for match in iterator:
        token=match.group();start=match.start()
        if token=='${':
            scopes.append((len(floats),len(essential),[]));records.append({'kind':'{','start':start,'end':match.end()});continue
        if token=='$}':
            nf,ne,added=scopes.pop();floats=floats[:nf];essential=essential[:ne]
            for x,y in added:adjacency[x].remove(y);adjacency[y].remove(x)
            records.append({'kind':'}','start':start,'end':match.end()});continue
        if token in ('$c','$v','$d'):
            fields=[]
            for end in iterator:
                if end.group()=='$.':break
                fields.append(end.group())
            kind=token[1:];record={'kind':kind,'expr':fields,'start':start,'end':end.end()};records.append(record)
            if kind=='v':variables.update(fields)
            if kind=='d':
                assert len(fields)==len(set(fields)), 'Self-disjoint declaration'
                for x,y in itertools.combinations(fields,2):
                    if y in adjacency[x]:continue
                    adjacency[x].add(y);adjacency[y].add(x)
                    if scopes:scopes[-1][2].append((x,y))
            continue
        label=token
        assert label not in rules, 'Duplicate Metamath label: '+label
        kind=next(iterator).group();expr=[];proof=None
        for end in iterator:
            if end.group() in ('$.','$='):break
            expr.append(end.group())
        if kind=='$p':
            assert end.group()=='$=';proof=[]
            for end in iterator:
                if end.group()=='$.':break
                proof.append(end.group())
        else:assert end.group()=='$.'
        record={'label':label,'kind':kind[1:],'expr':expr,'proof':proof,'start':start,'end':end.end()}
        if kind=='$f':floats.append(label)
        if kind=='$e':essential.append(label)
        if kind in ('$p','$a'):
            used=set(expr)&variables
            for e in essential:used.update(set(rules[e]['expr'])&variables)
            record['hyps']=[f for f in floats if rules[f]['expr'][1] in used]+essential.copy()
            record['dv']=frozenset((x,y) for x in used for y in adjacency[x]&used if x<y)
        records.append(record);rules[label]=record
    assert not scopes
    return records,rules,variables

def numbers(body):
    value=0
    for ch in ''.join(body):
        if 'A'<=ch<='T':yield value*20+ord(ch)-ord('A')+1;value=0
        elif 'U'<=ch<='Y':value=value*5+ord(ch)-ord('U')+1
        elif ch=='Z':assert value==0;yield 'Z'
        else:raise ValueError('Incomplete/invalid compressed proof character '+ch)
    assert value==0

def encode(value):
    out=chr(65+(value-1)%20);value=(value-1)//20
    while value:out=chr(85+(value-1)%5)+out;value=(value-1)//5
    return out

def rewrite(record,alias):
    proof=record['proof'];mandatory=record['hyps']
    if proof[0]!='(':
        rewritten=[alias.get(x,x) for x in proof]
        assert '?' not in rewritten
        return ' '.join(rewritten),set(rewritten)|set(mandatory)
    close=proof.index(')');old=proof[1:close];oldbase=len(mandatory)+len(old)
    sequence=list(numbers(proof[close+1:]));usedindices={x-len(mandatory)-1 for x in sequence if x!='Z' and len(mandatory)<x<=oldbase}
    explicit=[];lookup={}
    for i,label in enumerate(old):
        if i not in usedindices:continue
        label=alias.get(label,label)
        if label not in lookup:lookup[label]=len(mandatory)+len(explicit)+1;explicit.append(label)
    newbase=len(mandatory)+len(explicit);out=[]
    for n in sequence:
        if n=='Z':out.append(n)
        elif n<=len(mandatory):out.append(encode(n))
        elif n<=oldbase:out.append(encode(lookup[alias.get(old[n-len(mandatory)-1],old[n-len(mandatory)-1])]))
        else:out.append(encode(newbase+n-oldbase))
    body=''.join(out)
    return '( '+' '.join(explicit)+' )\n  '+'\n  '.join(body[i:i+100] for i in range(0,len(body),100)),set(explicit)|set(mandatory)

def main():
    began=time.time();sourcepath=ROOT/'BB3-deciders-annotated.mm';source=sourcepath.read_text();core=(ROOT/'core.mm').read_text()
    assert source.startswith(core)
    records,rules,variables=parse(source);print('Parsed',len(rules),'labelled statements',flush=True)
    corelabels={r['label'] for r in records if 'label' in r and r['end']<=len(core)}
    alias={};candidates=defaultdict(list);merged=[]
    for rec in records:
        if rec['kind'] not in ('a','p'):continue
        label=rec['label'];key=(tuple(rec['expr']),tuple(tuple(rules[h]['expr']) for h in rec['hyps']))
        choices=candidates[key]
        earlier=next((x for x in choices if rules[x]['dv']<=rec['dv']),None)
        if earlier is not None and label not in corelabels and rec['kind']=='p':
            alias[label]=earlier;merged.append({'removed':label,'canonical':earlier,'same_mandatory_dv':rules[earlier]['dv']==rec['dv']})
        else:candidates[key].append(label)
    print('Safely mergeable duplicate assertions:',len(merged),flush=True)
    dependencies={};rewritten={}
    for label,rec in rules.items():
        if rec['kind']=='p' and label not in alias:
            rewritten[label],dependencies[label]=rewrite(rec,alias)
        elif rec['kind']=='a':dependencies[label]=set(rec['hyps'])
    roots=[alias.get(x,x) for x in ROOTS];keep=set(corelabels);todo=list(roots)
    while todo:
        label=todo.pop()
        if label in keep:continue
        keep.add(label);todo.extend(dependencies.get(label,()))
    # Core is retained byte-for-byte; its dependencies must also be available.
    for label in corelabels:assert all(x in corelabels for x in dependencies.get(label,()))
    livevars=set()
    for label in keep:
        livevars.update(set(rules[label]['expr'])&variables)
    active=set();scopes=[];emitted_declarations=0
    # Establish active core disjointness exactly as its declarations specify.
    for rec in records:
        if rec['end']>len(core):break
        if rec['kind']=='{':scopes.append(set(active))
        elif rec['kind']=='}':active=scopes.pop()
        elif rec['kind']=='d':active.update(tuple(sorted(pair)) for pair in itertools.combinations(rec['expr'],2))
    result=[core.rstrip()+'\n\n$( Consolidated and dependency-pruned; see minimization-report.json. $)\n']
    for rec in records:
        if rec['end']<=len(core):continue
        kind=rec['kind'];label=rec.get('label')
        if kind=='{':scopes.append(set(active));result.append('${\n');continue
        if kind=='}':active=scopes.pop();result.append('$}\n');continue
        if kind=='p':
            if label not in keep or label in alias:continue
            result.append(label+' $p '+' '.join(rec['expr'])+' $=\n  '+rewritten[label]+' $.\n')
        elif kind=='a':raise AssertionError('Unexpected axiom outside unchanged core')
        elif kind in ('f','e'):
            if label in keep:result.append(source[rec['start']:rec['end']]+'\n')
        elif kind=='v':
            fields=[x for x in rec['expr'] if x in livevars]
            if fields:result.append('$v '+' '.join(fields)+' $.\n');emitted_declarations+=1
        elif kind=='d':
            fields=[x for x in rec['expr'] if x in livevars]
            needed={tuple(sorted(pair)) for pair in itertools.combinations(fields,2)}-active
            if not needed:continue
            if 4*len(needed)<len(fields)+3:
                result.extend('$d '+x+' '+y+' $.\n' for x,y in sorted(needed));emitted_declarations+=len(needed)
            else:result.append('$d '+' '.join(fields)+' $.\n');emitted_declarations+=1
            active.update(needed)
        elif kind=='c':result.append(source[rec['start']:rec['end']]+'\n')
    assert not scopes
    output='\n'.join(result)
    # Prefer descriptive public names to generated DAG names when a root
    # was merged with its earlier identical proof.
    renames={alias[x]:x for x in ROOTS if x in alias and alias[x] not in corelabels}
    if renames:
        pattern=r'(?<!\S)('+ '|'.join(re.escape(x) for x in sorted(renames,key=len,reverse=True))+r')(?!\S)'
        output=re.sub(pattern,lambda match:renames[match.group()],output)
    path=ROOT/'BB3-deciders-pruned.mm';path.write_text(output)
    original_proofs={k for k,v in rules.items() if v['kind']=='p'}
    retained=original_proofs&keep
    unreachable=original_proofs-set(alias)-retained
    superseded=[x for x in [
        'cps11-certificate-verifier-correct','cps22-certificate-verifier-correct',
        'cps33-certificate-verifier-correct','regular16-certificate-verifier-correct'] if x not in keep]
    report={'input':sourcepath.name,'output':path.name,'input_sha256':hashlib.sha256(source.encode()).hexdigest(),
            'output_sha256':hashlib.sha256(output.encode()).hexdigest(),'input_bytes':len(source.encode()),
            'output_bytes':len(output.encode()),'input_proofs':len(original_proofs),'output_proofs':len(retained),
            'merged_duplicate_assertions':len(alias),'pruned_unreachable_assertions':len(unreachable),
            'unchanged_core_bytes':len(core.encode()),'trusted_declarations':93,'public_roots':[renames.get(x,x) for x in roots],
            'canonical_roots_before_renaming':roots,'canonical_renaming':renames,
            'superseded_public_interfaces_removed':superseded,'merge_aliases':merged,
            'retained_labels':sorted(retained),'unreachable_labels':sorted(unreachable),
            'retained_prefix_counts':dict(Counter(x.split('-')[0] for x in retained)),
            'elapsed_seconds':time.time()-began,'official_verification':'pending'}
    assert len(original_proofs)==len(alias)+len(unreachable)+len(retained)
    (ROOT/'minimization-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('merge_aliases','retained_labels','unreachable_labels')},indent=2),flush=True)
if __name__=='__main__':main()
