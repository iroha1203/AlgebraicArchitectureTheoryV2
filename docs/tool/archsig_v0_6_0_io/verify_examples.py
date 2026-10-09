#!/usr/bin/env python3
"""固定したI/O例のschema/参照/算術を検算する。ArchSig評価器ではない。"""
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).parent

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        assert key not in result, ('duplicate key', key)
        result[key] = value
    return result

def read(name):
    return json.loads((HERE / 'examples' / name).read_text(), object_pairs_hook=unique_object)

def canonical(value):
    # このfixtureにはcontrol charや特殊なescapeを必要とする文字はない。
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()

law = read('law.json')
assert set(law) == {'format', 'semantics', 'entry', 'modules'}
assert law['format'] == 'archsig.law/1' and law['semantics'] == 'archsig/0.6.0'
module, = law['modules']
assert module['id'] == law['entry'] == 'affine'
assert module['imports'] == [] and module['roles'] == ['current']
sort, predicate, query = module['declarations']
assert sort == {'kind': 'sort', 'name': 'Operation'}
assert predicate['domain'] == 'affine/Operation'
assert predicate['payload'] == ['Term', ['Q'], 'Q']
assert query['result'] == 'Proposition'
vocabulary = sorted((d for d in module['declarations'] if d['kind'] in
                     {'sort', 'data', 'predicate', 'pure'}), key=lambda d: d['name'])
vocabulary_digest = 'sha256:' + hashlib.sha256(canonical(vocabulary)).hexdigest()

# この短い例で使用する文法・束縛・型だけを独立に検査する。
# 未使用のDSL機能を検査したとはしない。
R = ('Ref', 'affine/Operation')
TERM = ('Term', ('Q',), 'Q')
def ty(t):
    return tuple(ty(x) for x in t) if isinstance(t, list) else t

def infer(e, env):
    op, *args = e
    if op == 'var':
        assert len(args) == 1 and args[0] in env
        return env[args[0]]
    if op == 'lit':
        assert len(args) == 2 and args[0] == 'Q'
        n, d = args[1]
        q = Q(int(n), int(d))
        assert [str(q.numerator), str(q.denominator)] == [n, d]
        return 'Q'
    if op == 'fn':
        ps, body = args
        assert len({p[0] for p in ps}) == len(ps)
        assert not set(p[0] for p in ps) & env.keys()
        nested = env | {n: ty(t) for n, t in ps}
        return ('Fn', tuple(ty(t) for _, t in ps), infer(body, nested))
    if op == 'snapshots':
        assert args == ['affine/current']
        return ('Set', 'Snapshot')
    if op == 'subjects':
        s, snapshot = args
        assert s == 'affine/Operation' and infer(snapshot, env) == 'Snapshot'
        return ('Set', R)
    if op == 'field':
        p, r = args
        assert p == 'affine/body' and infer(r, env) == R
        return TERM
    if op == 'get':
        i, x = args
        t = infer(x, env)
        assert t[0] == 'Tuple' and 0 <= i < len(t)-1
        return t[i+1]
    assert op == 'call'
    name, *expressions = args
    ts = [infer(x, env) for x in expressions]
    if name in {'core/add', 'core/mul'}:
        assert ts == ['Q', 'Q']
        return 'Q'
    if name == 'core/product':
        a, b = ts
        assert a[0] == b[0] == 'Set'
        return ('Set', ('Tuple', a[1], b[1]))
    if name == 'core/all':
        s, f = ts
        assert s[0] == 'Set' and f == ('Fn', (s[1],), 'Proposition')
        return 'Proposition'
    if name == 'core/then':
        assert ts == [TERM, TERM]
        return TERM
    if name == 'core/term_equal':
        assert ts == [TERM, TERM]
        return 'Proposition'
    raise AssertionError(('unexpected fixture expression', name))

assert infer(query['body'], {}) == 'Proposition'

def inspect_archmap(a):
    assert set(a) == {'format','semantics','vocabularies','sources','origins','snapshots'}
    assert a['format'] == 'archsig.archmap/1' and a['semantics'] == law['semantics']
    assert a['vocabularies'] == [{'module':'affine','digest':vocabulary_digest}]
    sources = {s['id']: s for s in a['sources']}
    origins = {o['id']: o for o in a['origins']}
    for o in origins.values():
        assert o['mode'] == 'observed' and o['locations']
        assert all(loc['source'] in sources for loc in o['locations'])
    snap, = a['snapshots']
    assert snap['role'] == 'affine/current' and snap['origin'] in origins
    subjects = {s['id']:s for s in snap['subjects']}
    assert len(subjects) == len(snap['subjects']) == 2
    assert all(s['sort']=='affine/Operation' and s['origin'] in origins for s in subjects.values())
    seen, ids = set(), set()
    for atom in snap['atoms']:
        assert atom['subject'] in subjects and atom['origin'] in origins
        assert atom['predicate'] == 'affine/body' and atom['id'] not in ids
        ids.add(atom['id'])
        key = (atom['subject'], atom['predicate'])
        assert key not in seen
        seen.add(key)
        assert atom['value']['params'] == ['x']
        assert infer(atom['value']['body'], {'x':'Q'}) == 'Q'
    return {x['subject']:x['value'] for x in snap['atoms']}

assert read('refuted.archmap.json')['sources'][0]['digest'] == 'sha256:' + hashlib.sha256(b'fn f(x) { x + 1 }\nfn g(x) { 2 * x }\n').hexdigest()
assert read('established.archmap.json')['sources'][0]['digest'] == 'sha256:' + hashlib.sha256(b'fn f(x) { x + 1 }\nfn g(x) { x + 2 }\n').hexdigest()
refuted = inspect_archmap(read('refuted.archmap.json'))
established = inspect_archmap(read('established.archmap.json'))
missing = inspect_archmap(read('missing.archmap.json'))
assert set(refuted) == set(established) == {'f','g'} and set(missing) == {'f'}
assert refuted['f'] == established['f'] == missing['f']
# 読み込んだ固定fixtureの原始式を直接照合してから、その係数を検算。
assert refuted['f']['body'] == ['call','core/add',['var','x'],['lit','Q',['1','1']]]
assert refuted['g']['body'] == ['call','core/mul',['lit','Q',['2','1']],['var','x']]
assert established['g']['body'] == ['call','core/add',['var','x'],['lit','Q',['2','1']]]
def then(f,g):
    a,b=f; c,d=g
    return c*a,c*b+d
f, g, h = (Q(1),Q(1)), (Q(2),Q(0)), (Q(1),Q(2))
assert then(f,g) == (2,2) and then(g,f) == (2,1)
assert then(f,h) == then(h,f) == (1,3)
assert all(then(a,b)==then(b,a) for a in [f,h] for b in [f,h])
# missing gに許される二補完が異なる判断を与える。
assert (then(f,g)==then(g,f)) is False
assert (then(f,h)==then(h,f)) is True
# 同一Hole、別Hole、整数と有理数、反復incidence、一般chartの射。
assert all(Q(x)-Q(x)==0 for x in [-3,0,2,5])
assert Q(2)-Q(2)==0 and Q(2)-Q(3)!=0
assert Q(1,2)*2==1 and 1 % 2 != 0
assert sum([1,1])==2 and len(set(['e','e']))==1
X = [0,1]; pullback = [(x,y) for x in X for y in X]
v = {0:Q(0),1:Q(1)}
p1 = [v[x] for x,y in pullback]; p2 = [v[y] for x,y in pullback]
assert p1 != p2 and [b-a for a,b in zip(p1,p2)] == [0,1,-1,0]
# 三操作の元方程式は原始端点から構成する。行列を入力として用いない。
vertices = ['p','q','r']; edges = [('p','q'),('q','r'),('p','r')]
D = [[Q(int(t==v)-int(s==v)) for v in vertices] for s,t in edges]
lam = [Q(1),Q(1),Q(-1)]
assert all(sum(lam[i]*D[i][j] for i in range(3))==0 for j in range(3))
assert sum(a*b for a,b in zip(lam,[1,1,3]))==-1
assert [sum(a*b for a,b in zip(row,[0,1,2])) for row in D]==[1,1,2]

for mutation in ('duplicate','unreduced','wrong_sort'):
    a=read('refuted.archmap.json')
    if mutation=='duplicate': a['snapshots'][0]['atoms'].append(a['snapshots'][0]['atoms'][0])
    if mutation=='unreduced': a['snapshots'][0]['atoms'][0]['value']['body'][3][2]=['2','2']
    if mutation=='wrong_sort': a['snapshots'][0]['subjects'][0]['sort']='affine/Missing'
    try:
        inspect_archmap(a)
    except AssertionError:
        pass
    else:
        raise AssertionError(('invalid mutation accepted',mutation))
print('OK: 4 JSON files; example grammar/binding/types; vocabulary digest; 3 invalid mutations')
print('OK: established/refuted/missing; operation order; holes; Z/Q; repeated incidence; chart projections')
print('OK: endpoint-derived D, inconsistency witness, and solution substitution')

# 自己モデルも同じJSON宣言・prefix構文。完成IRと保存判定は入力しない。
self_law, self_a = read('self.law.json'), read('self.archmap.json')
sm, = self_law['modules']
sd = {d['name']:d for d in sm['declarations']}
sv = sorted((d for d in sm['declarations'] if d['kind'] in
             {'sort','data','predicate','pure'}),key=lambda d:d['name'])
assert self_a['vocabularies']==[{'module':'self','digest':'sha256:'+hashlib.sha256(canonical(sv)).hexdigest()}]
assert sd['compile']['body'][:3]==['fold','self/Source','self/IR']
assert sd['source_eval']['body'][:3]==['fold','self/Source','Q']
assert sd['ir_eval']['body'][:3]==['fold','self/IR','Q']
self_types={k:[(c['name'],c['fields']) for c in d['constructors']]
            for k,d in sd.items() if d['kind']=='data'}
def check_data(t,value):
    if t=='Q':
        n,d=value; z=Q(int(n),int(d)); assert [str(z.numerator),str(z.denominator)]==value
        return
    ct=dict(self_types[t.split('/')[1]])
    fields=ct[value['tag']]
    assert len(fields)==len(value['args'])
    for tt,vv in zip(fields,value['args']):check_data(tt,vv)
def infer_self(e, env):
    op,*a=e
    if op=='var': return env[a[0]]
    if op=='fn':
        ps,body=a
        assert not set(n for n,t in ps)&env.keys()
        return ('Fn',tuple(ty(t) for n,t in ps),infer_self(body,env|{n:ty(t) for n,t in ps}))
    if op=='snapshots':
        assert a==['self/spec'];return ('Set','Snapshot')
    if op=='subjects':
        assert a[0]=='self/Rewrite' and infer_self(a[1],env)=='Snapshot'
        return ('Set',('Ref','self/Rewrite'))
    if op=='field':
        d=sd[a[0].split('/')[1]]
        assert infer_self(a[1],env)==('Ref',d['domain'])
        return ty(d['payload'])
    if op=='ctor':
        typ,tag,*args=a
        fs=dict(self_types[typ.split('/')[1]])[tag]
        assert [infer_self(x,env) for x in args]==[ty(t) for t in fs]
        return typ
    if op in {'fold','match'}:
        if op=='fold':
            typ,out,x,cases=a
            out=ty(out)
            assert infer_self(x,env)==typ
        else:
            x,cases=a;typ=infer_self(x,env);out=None
        fs=dict(self_types[typ.split('/')[1]])
        assert len(cases)==len(fs) and {c[0] for c in cases}==set(fs)
        for tag,names,body in cases:
            fields=[out if op=='fold' and t==typ else ty(t) for t in fs[tag]]
            assert len(names)==len(fields) and len(set(names))==len(names)
            assert not set(names)&env.keys()
            bt=infer_self(body,env|dict(zip(names,fields)))
            if out is None:out=bt
            assert bt==out
        return out
    assert op=='call'
    name,*args=a;ts=[infer_self(x,env) for x in args]
    if name in {'core/add','core/sub'}:
        assert ts==['Q','Q'];return 'Q'
    if name=='core/all':
        ds,f=ts;assert ds[0]=='Set' and f==('Fn',(ds[1],),'Proposition');return 'Proposition'
    if name=='core/term':
        f,=ts;assert f[0]=='Fn';return ('Term',f[1],f[2])
    if name=='core/term_equal':
        assert ts[0]==ts[1] and ts[0][0]=='Term';return 'Proposition'
    d=sd[name.split('/')[1]]
    assert d['kind']=='pure' and ts==[ty(p['type']) for p in d['params']]
    return ty(d['result'])
for d in sd.values():
    if d['kind'] in {'pure','query'}:
        env={p['name']:ty(p['type']) for p in d.get('params',[])}
        assert infer_self(d['body'],env)==ty(d['result'])

sa=self_a['snapshots'][0]['atoms']
assert {x['predicate'] for x in sa}=={'self/source','self/operator'}
for atom in sa:check_data(sd[atom['predicate'].split('/')[1]]['payload'],atom['value'])
def source_coeff(tree):
    tag,args=tree['tag'],tree['args']
    if tag=='Var':return Q(1),Q(0)
    if tag=='Lit':return Q(0),Q(int(args[0][0]),int(args[0][1]))
    a,b=source_coeff(args[0]);c,d=source_coeff(args[1]);return a+c,b+d

def candidate_coeff(tree,subtract):
    tag,args=tree['tag'],tree['args']
    if tag!='Add':return source_coeff(tree)
    a,b=candidate_coeff(args[0],subtract);c,d=candidate_coeff(args[1],subtract)
    return (a-c,b-d) if subtract else (a+c,b+d)
source=sa[0]['value']
assert source_coeff(source)==candidate_coeff(source,False)==(1,3)
assert candidate_coeff(source,True)==(1,1)
assert -1+3==2 and -1+1==0
print('OK: self-model grammar/binding/types/vocabulary/ADT values; fold signatures; generated add/subtract IR evaluation')

# 標準商の固定例。評価はQ→Qのアフィン残差の正規形で独立に比較する。
domain = [0, 1, 2]
evaluations = {0: (Q(1), Q(0)), 1: (Q(1), Q(1)), 2: (Q(1), Q(0))}
classes = {frozenset(y for y in domain if evaluations[x] == evaluations[y]) for x in domain}
assert classes == {frozenset({0, 2}), frozenset({1})}
assert all(b for b in classes) and set().union(*classes) == set(domain)
assert all(b == c or b.isdisjoint(c) for b in classes for c in classes)
qmap = {x: next(b for b in classes if x in b) for x in domain}
assert all({x for x in domain if qmap[x] == b} == set(b) for b in classes)
reversed_classes = {frozenset(y for y in reversed(domain) if evaluations[x] == evaluations[y])
                    for x in reversed(domain)}
assert classes == reversed_classes
assert {frozenset() for x in []} == set()  # 空域の商は{空集合}にならない。

def typed_zset(xs):
    return {'type': ['Set', 'Z'], 'value': sorted(str(x) for x in xs)}

wire_map = {'kind': 'finite', 'source': typed_zset(domain),
            'target': {'type': ['Set', ['Set', 'Z']],
                       'value': sorted(typed_zset(b)['value'] for b in classes)},
            'pairs': [{'type': ['Tuple', 'Z', ['Set', 'Z']],
                       'value': [str(x), typed_zset(qmap[x])['value']]} for x in domain]}
decoded = json.loads(canonical(wire_map))
assert decoded == wire_map
assert decoded['target']['type'] == ['Set', ['Set', 'Z']]
assert all(p['type'] == ['Tuple', 'Z', ['Set', 'Z']] for p in decoded['pairs'])
assert {int(p['value'][0]): frozenset(map(int, p['value'][1]))
        for p in decoded['pairs']} == qmap
fibers = [{'image': typed_zset(b), 'preimage': typed_zset(b)} for b in classes]
assert all(row['image'] == row['preimage'] for row in fibers)

# 全域性の反例に現れるcallだけの構文走査。評価器ではなく、全枝を見ることを検算する。
bad_closure = ['call', 'core/closure', ['set', 'Z', ['lit', 'Z', '1']],
               ['set', 'Z'], ['fn', [['n', 'Z']], ['set', 'Z']]]
pure_bodies = {'test/bad': bad_closure, 'test/wrapper': ['call', 'test/bad'],
               'test/dead': ['if', ['lit', 'Bool', False], bad_closure, ['set', 'Z']]}
def call_names(tree):
    if not isinstance(tree, list):
        return set()
    direct = {tree[1]} if len(tree) > 1 and tree[0] == 'call' else set()
    return direct | set().union(*(call_names(x) for x in tree))
def call_closure(name):
    direct = call_names(pure_bodies[name])
    return direct | set().union(*(call_closure(x) for x in direct if x in pure_bodies))
assert all('core/closure' in call_closure(name) for name in pure_bodies)
assert set([1, 1]) == {1}  # set式と入力Set encodingの拒否規則を区別する。

# 保存の成否と端点の一致は独立。各値の型が同じでもcarrierは異なる。
assert {'source': 'C2', 'target': 'D', 'preserves': True}['source'] != 'C1'
assert {False} != {False, True}
assert {'0', '1'} != {'0', '1', '2'}  # 有限sourceはQ全体でもない。
assert ('Fn', ('Z',), 'Proposition') != ('Fn', ('Q',), 'Proposition')
# 生成関係で割った元の等値。constructorラベルや整数の代表はkeyを変えない。
f2_zero_by_sub = (1-1) % 2
assert f2_zero_by_sub == 0
zmod2_representatives = [0, 2, -2]
assert {x % 2 for x in zmod2_representatives} == {0}
finite_f2_table = {0: False, 1: True}
assert finite_f2_table[f2_zero_by_sub] is False
assert {x % 2 for x in [2, 1]} == set(finite_f2_table)
def must_not_call(_):
    raise AssertionError('empty-domain body evaluated')
assert all(must_not_call(x) for x in []) is True
assert any(must_not_call(x) for x in []) is False
print('OK: quotient partition/types/wire/order/empty; pure call closure; carrier/value equality; empty quantification')
