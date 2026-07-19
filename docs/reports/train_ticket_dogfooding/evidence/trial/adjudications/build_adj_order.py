#!/usr/bin/env python3
"""Build adj-order.json for ts-order-service dual-pass adjudication."""
import json, glob, os

RUN = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def load(pass_letter):
    atoms = {}
    for f in sorted(glob.glob(os.path.join(RUN, f'candidates/pass-{pass_letter}-chunk-0*.json'))):
        for a in json.load(open(f))['candidateAtoms']:
            atoms[a['id']] = a
    return atoms

A = load('a')
B = load('b')

cons = json.load(open(os.path.join(RUN, 'extraction-consistency.json')))
PREF = 'src:ts-order-service/'
entriesA = {e['key']: e for e in cons['onlyInPassA'] if e['refs'][0].startswith(PREF)}
entriesB = {e['key']: e for e in cons['onlyInPassB'] if e['refs'][0].startswith(PREF)}

# decision table: key -> (pass, decision, basis, canonical_spec)
# canonical_spec: None, or ('A'/'B', atom_id, extra_refs_from_other_side or [])
KA = list(entriesA)
KB = list(entriesB)

def akey(sub): return [k for k in KA if sub in k][0]
def bkey(sub): return [k for k in KB if sub in k][0]

rows = []       # (key, decision, basis)
canon = []      # atom dicts

def canonical(src, atom_id, union_refs=None):
    atom = dict((A if src == 'A' else B)[atom_id])
    if union_refs:
        refs = list(atom['refs'])
        for r in union_refs:
            if r not in refs:
                refs.append(r)
        atom['refs'] = refs
    canon.append(atom)
    return atom

# ---- authority (4 merged pairs, canonical = pass B verbatim) ----
c = canonical('B', 'atom:authority:ts-order-service.SecurityConfig:checksPermission:jwt-filter')
basis = ("Reread order/config/SecurityConfig.java:85: addFilterBefore(new JWTFilter(), "
         "UsernamePasswordAuthenticationFilter.class); same fact both passes; kept " + c['id'] + " (pass B).")
rows.append((akey('checksPermission|jwt-filter'), 'merged', basis))
rows.append((bkey('checksPermission|jwt-filter'), 'merged', basis))

c = canonical('B', 'atom:authority:ts-order-service.SecurityConfig:checksPermission:permit-all-order-subtree')
basis = ("Reread order/config/SecurityConfig.java:80: antMatchers(\"/api/v1/orderservice/order/**\").permitAll() "
         "declared after the role matchers at lines 75-79; kept " + c['id'] + " (pass B, records the declaration order).")
rows.append((akey('permit-all:/api/v1/orderservice/order/**'), 'merged', basis))
rows.append((bkey('permit-all:/api/v1/orderservice/order/**'), 'merged', basis))

c = canonical('B', 'atom:authority:ts-order-service.SecurityConfig:requiresRole:order-write-admin-or-user',
              union_refs=['src:ts-order-service/src/main/java/order/config/SecurityConfig.java:77'])
basis = ("Reread order/config/SecurityConfig.java:75-77: POST/PUT/DELETE on /api/v1/orderservice/order require "
         "hasAnyRole(ADMIN, USER); kept " + c['id'] + " (pass B), refs unioned with pass A.")
rows.append((akey('requiresRole|ADMIN-or-USER'), 'merged', basis))
rows.append((bkey('requiresRole|ADMIN-or-USER'), 'merged', basis))

c = canonical('B', 'atom:authority:ts-order-service.SecurityConfig:requiresRole:order-admin-routes-admin',
              union_refs=['src:ts-order-service/src/main/java/order/config/SecurityConfig.java:79'])
basis = ("Reread order/config/SecurityConfig.java:78-79: POST/PUT on /api/v1/orderservice/order/admin require "
         "hasAnyRole(ADMIN); kept " + c['id'] + " (pass B), refs unioned with pass A.")
rows.append((akey('requiresRole|ADMIN:POST-PUT'), 'merged', basis))
rows.append((bkey('requiresRole|ADMIN on POST/PUT'), 'merged', basis))

# ---- restTemplate bean: A component <-> B relation (same declaration) ----
c = canonical('A', 'atom:component:ts-order-service.OrderApplication.restTemplate')
basis = ("Reread order/OrderApplication.java:29-31: single @LoadBalanced @Bean RestTemplate declaration observed "
         "by both passes (component vs dependsOn rendering); kept " + c['id'] + " (pass A component).")
rows.append((akey('component|ts-order-service.OrderApplication.restTemplate'), 'merged', basis))
rows.append((bkey('dependsOn|load-balanced-rest-template-bean'), 'merged', basis))

# ---- contracts ----
c = canonical('A', 'atom:contract:ts-order-service.OrderAlterInfo:shapedAs:account-previousorder-logintoken-neworder',
              union_refs=['src:ts-order-service/src/main/java/order/entity/OrderAlterInfo.java:25'])
basis = ("Reread order/entity/OrderAlterInfo.java:21-29: fields accountId, previousOrderId, loginToken, "
         "newOrderInfo; kept " + c['id'] + " (pass A, field-exact object), refs unioned.")
rows.append((akey('OrderAlterInfo|specification|shapedAs'), 'merged', basis))
rows.append((bkey('OrderAlterInfo|specification|shapedAs'), 'merged', basis))

c = canonical('A', 'atom:contract:ts-order-service.OrderController.queryOrders:shapedAs:orderinfo-request-body')
basis = ("Reread order/controller/OrderController.java:58: queryOrders takes @RequestBody OrderInfo; kept "
         + c['id'] + " (pass A, subject-exact; the refresh use at line 66 is a different method).")
rows.append((akey('OrderController.queryOrders|specification|shapedAs'), 'merged', basis))
rows.append((bkey('OrderController.queryOrders|specification|shapedAs'), 'merged', basis))

c = canonical('B', 'atom:contract:ts-order-service.OrderInfo:shapedAs:order-query-filter-dto',
              union_refs=['src:ts-order-service/src/main/java/order/entity/OrderInfo.java:51'])
basis = ("Reread order/entity/OrderInfo.java:12-51: DTO carries date/state filters with enable* flags; kept "
         + c['id'] + " (pass B, clearer object), refs unioned.")
rows.append((akey('OrderInfo|specification|shapedAs'), 'merged', basis))
rows.append((bkey('OrderInfo|specification|shapedAs'), 'merged', basis))

c = canonical('B', 'atom:contract:ts-order-service.OrderServiceImpl.create:requires:order-not-duplicated-for-account')
basis = ("Reread order/service/OrderServiceImpl.java:89-92: create rejects when findByAccountId(...).contains(order); "
         "kept " + c['id'] + " (pass B, subject-exact ref; pass A's extra ref 427 is addNewOrder, a matched capability).")
rows.append((akey('OrderServiceImpl.create|specification|requires'), 'merged', basis))
rows.append((bkey('OrderServiceImpl.create|specification|requires'), 'merged', basis))

c = canonical('A', 'atom:contract:ts-order-service.OrderServiceImpl.deleteOrder:requires:uuid-formatted-order-id')
basis = ("Reread order/service/OrderServiceImpl.java:410: UUID.fromString(orderId) precedes lookup, so orderId "
         "must parse as UUID; kept " + c['id'] + " (pass A).")
rows.append((akey('OrderServiceImpl.deleteOrder|specification|requires'), 'merged', basis))
rows.append((bkey('OrderServiceImpl.deleteOrder|specification|requires'), 'merged', basis))

c = canonical('A', 'atom:contract:ts-order-service.Order:ensures:default-constructor-status-paid')
basis = ("Reread order/entity/Order.java:84: default constructor sets status = OrderStatus.PAID.getCode(); same "
         "single fact both passes (contract vs semantic rendering); kept " + c['id'] + " (pass A contract).")
rows.append((akey('Order|specification|ensures|default-constructor-sets-status-paid'), 'merged', basis))
rows.append((bkey('constructor-default-status-paid'), 'merged', basis))

c = canonical('B', 'atom:contract:ts-order-service.SecurityConfig:ensures:stateless-session')
basis = ("Reread order/config/SecurityConfig.java:70-72: csrf().disable() then "
         "sessionCreationPolicy(STATELESS); a configured guarantee, so ensures fits; kept " + c['id'] + " (pass B).")
rows.append((akey('SecurityConfig|specification|requires|stateless-session-policy'), 'merged', basis))
rows.append((bkey('SecurityConfig|specification|ensures|stateless-session-policy-with-csrf-disabled'), 'merged', basis))

basis = ("Reread order/service/OrderServiceImpl.java:334: missing order returns Response(0, orderNotFound, \"-1.0\"); "
         "only pass B saw it; adopted verbatim.")
canonical('B', 'atom:contract:ts-order-service.OrderServiceImpl.getOrderPrice:ensures:minus-one-sentinel-on-missing-order')
rows.append((bkey('getOrderPrice|specification|ensures'), 'adopted', basis))

basis = ("Reread order/service/OrderServiceImpl.java:372-379: initOrder saves only when findById(order.getId()) is "
         "absent; only pass B saw it; adopted verbatim.")
canonical('B', 'atom:contract:ts-order-service.OrderServiceImpl.initOrder:requires:order-id-not-already-present')
rows.append((bkey('initOrder|specification|requires'), 'adopted', basis))

basis = ("Reread order/service/OrderServiceImpl.java:66,69,256,262: service methods return Response code 1 on "
         "success and 0 on not-found/no-content; only pass A saw the service-level contract; adopted verbatim.")
canonical('A', 'atom:contract:ts-order-service.OrderServiceImpl:ensures:response-code-1-success-0-not-found-or-no-content')
rows.append((akey('response-code-1-success-0-not-found-or-no-content'), 'adopted', basis))

# ---- effect / relation ----
basis = ("Reread order/service/OrderServiceImpl.java:208-217: queryForStationId posts to "
         "ts-station-service /api/v1/stationservice/stations/namelist via restTemplate; adopted verbatim.")
canonical('A', 'atom:effect:ts-order-service.OrderServiceImpl.queryForStationId:callsProvider:ts-station-service-stations-namelist')
rows.append((akey('effect|ts-order-service.OrderServiceImpl.queryForStationId'), 'adopted', basis))

c = canonical('B', 'atom:relation:ts-order-service.InitData:calls:OrderService-initOrder')
basis = ("Reread order/init/InitData.java:45,82: service.initOrder(...) invoked on seed orders; kept "
         + c['id'] + " (pass B, method-precise object).")
rows.append((akey('relation|ts-order-service.InitData|relation|calls|ts-order-service.OrderService'), 'merged', basis))
rows.append((bkey('relation|ts-order-service.InitData|relation|calls|ts-order-service.OrderService.initOrder'), 'merged', basis))

c = canonical('A', 'atom:relation:ts-order-service.OrderApplication:dependsOn:service-discovery')
basis = ("Reread order/OrderApplication.java:23: @EnableDiscoveryClient on the application class; kept "
         + c['id'] + " (pass A, catalog relation axis).")
rows.append((akey('relation|ts-order-service.OrderApplication|relation|dependsOn|service-discovery-client'), 'merged', basis))
rows.append((bkey('restriction|dependsOn|spring-cloud-discovery-client'), 'merged', basis))

c = canonical('A', 'atom:relation:ts-order-service.OrderController:calls:OrderService')
basis = ("Reread order/controller/OrderController.java:26,47: @Autowired OrderService and delegation from handlers; "
         "kept " + c['id'] + " (pass A, catalog relation axis).")
rows.append((akey('relation|ts-order-service.OrderController|relation|calls|ts-order-service.OrderService'), 'merged', basis))
rows.append((bkey('relation|ts-order-service.OrderController|restriction|calls'), 'merged', basis))

c = canonical('A', 'atom:relation:ts-order-service.OrderServiceImpl:calls:ts-station-service')
basis = ("Reread order/service/OrderServiceImpl.java:208-213: restTemplate.exchange against ts-station-service; "
         "kept " + c['id'] + " (pass A); the endpoint detail stays in the adopted "
         "atom:effect:ts-order-service.OrderServiceImpl.queryForStationId:callsProvider:ts-station-service-stations-namelist.")
rows.append((akey('relation|ts-order-service.OrderServiceImpl|relation|calls|ts-station-service'), 'merged', basis))
rows.append((bkey('relation|ts-order-service.OrderServiceImpl|relation|calls|ts-station-service:/api/v1/stationservice/stations/namelist'), 'merged', basis))

c = canonical('B', 'atom:effect:ts-order-service.OrderServiceImpl:writesTo:order-store')
basis = ("Reread order/service/OrderServiceImpl.java:95,260,351,464: orderRepository.save calls; same write fact "
         "both passes; kept " + c['id'] + " (pass B effect kind); pass A's delete ref 418 is covered by adopted "
         "atom:effect:ts-order-service.OrderServiceImpl:writesTo:order-store-delete.")
rows.append((akey('relation|ts-order-service.OrderServiceImpl|relation|writesTo|order-jpa-repository'), 'merged', basis))
rows.append((bkey('effect|ts-order-service.OrderServiceImpl|effect|writesTo|order-store'), 'merged', basis))

basis = ("Reread order/service/OrderServiceImpl.java:418: orderRepository.deleteById(orderUuid) in deleteOrder; "
         "only pass B split the delete write out; adopted verbatim.")
canonical('B', 'atom:effect:ts-order-service.OrderServiceImpl:writesTo:order-store-delete')
rows.append((bkey('writesTo|order-store-delete'), 'adopted', basis))

basis = ("Reread order/init/InitData.java:28-45: CommandLineRunner run() seeds three orders through "
         "service.initOrder; only pass B saw the startup write effect; adopted verbatim.")
canonical('B', 'atom:effect:ts-order-service.InitData:writesTo:startup-seed-orders')
rows.append((bkey('effect|ts-order-service.InitData|effect|writesTo|startup-seed-orders'), 'adopted', basis))

# ---- semantic ----
basis = ("Reread order/service/OrderServiceImpl.java:398-401: boughtDate parsed and compared to the one-hour "
         "window to count recent purchases; adopted verbatim.")
canonical('A', 'atom:semantic:ts-order-service.Order.boughtDate:meansInUse:recent-purchase-rate-window')
rows.append((akey('Order.boughtDate'), 'adopted', basis))

c = canonical('B', 'atom:semantic:ts-order-service.Order:identifiedBy:business-field-equality',
              union_refs=['src:ts-order-service/src/main/java/order/entity/Order.java:114'])
basis = ("Reread order/entity/Order.java:89-122: equals compares business fields without id while hashCode uses "
         "id only; kept " + c['id'] + " (pass B captures both sides), refs unioned.")
rows.append((akey('Order.equals|semantic|identifiedBy'), 'merged', basis))
rows.append((bkey('semantic|ts-order-service.Order|semantic|identifiedBy'), 'merged', basis))

basis = ("Reread order/entity/Order.java:27-29: @Id @Column(length = 36) @GeneratedValue(generator = \"jpa-uuid\"); "
         "adopted verbatim.")
canonical('A', 'atom:semantic:ts-order-service.Order.id:identifiedBy:jpa-uuid-36-char-string')
rows.append((akey('Order.id'), 'adopted', basis))

c = canonical('B', 'atom:semantic:ts-order-service.Order.status:meansInUse:seed-initial-status-zero',
              union_refs=['src:ts-order-service/src/main/java/order/init/InitData.java:62'])
basis = ("Reread order/init/InitData.java:43,62,80: all three seed orders call setStatus(0); kept "
         + c['id'] + " (pass B, names the startup-seed context), refs unioned.")
rows.append((akey('Order.status|semantic|meansInUse|initial-seed-status-zero'), 'merged', basis))
rows.append((bkey('startup-seed-orders-created-with-status-0'), 'merged', basis))

basis = ("Reread order/entity/Order.java:69,84: int status holds OrderStatus enum codes (e.g. PAID.getCode()); "
         "distinct general-meaning alias, adopted verbatim.")
canonical('A', 'atom:semantic:ts-order-service.Order.status:meansInUse:order-status-code-from-orderstatus-enum')
rows.append((akey('order-lifecycle-status-code-from-orderstatus-enum'), 'adopted', basis))

basis = ("Reread order/controller/OrderController.java:106-110: @PathVariable int status is passed to "
         "modifyOrder as the target status code; adopted verbatim.")
canonical('A', 'atom:semantic:ts-order-service.OrderController.modifyOrder:meansInUse:status-path-variable-sets-order-status-code')
rows.append((akey('OrderController.modifyOrder|semantic'), 'adopted', basis))

c = canonical('B', 'atom:semantic:ts-order-service.OrderInfo.state:meansInUse:target-status-filter')
basis = ("Reread order/entity/OrderInfo.java:75-78 and order/service/OrderServiceImpl.java:139: state carries the "
         "target status compared against order.getStatus() in queryOrders; kept " + c['id'] + " (pass B).")
rows.append((akey('OrderInfo.state|semantic|meansInUse|order-status-filter-target'), 'merged', basis))
rows.append((bkey('OrderInfo.state|semantic|meansInUse|target-order-status-filter-for-queryOrders'), 'merged', basis))

c = canonical('B', 'atom:semantic:ts-order-service.OrderStatus.CHANGE:statusGates:sold-ticket-count-exclusion')
basis = ("Reread order/service/OrderServiceImpl.java:274: orders with status >= OrderStatus.CHANGE.getCode() are "
         "skipped in the sold-ticket count; kept " + c['id'] + " (pass B, constant-precise subject).")
rows.append((akey('OrderStatus|semantic|statusGates|sold-ticket-exclusion-at-or-above-change'), 'merged', basis))
rows.append((bkey('OrderStatus.CHANGE|semantic|statusGates'), 'merged', basis))

c = canonical('B', 'atom:semantic:ts-order-service.OrderStatus:statusGates:valid-order-count')
basis = ("Reread order/service/OrderServiceImpl.java:393-396: NOTPAID/PAID/COLLECTED statuses count as valid "
         "orders in checkSecurityAboutOrder; kept " + c['id'] + " (pass B, names the applying check).")
rows.append((akey('OrderStatus|semantic|statusGates|valid-order-count-notpaid-paid-collected'), 'merged', basis))
rows.append((bkey('valid-order-count-notpaid-paid-collected-in-security-check'), 'merged', basis))

basis = ("Reread order/service/OrderServiceImpl.java:66,69 and ts-payment-service PaymentServiceImpl.java:41,44: "
         "Response first argument is 1 on the success branch and 0 on the rejected/empty branch; adopted verbatim.")
canonical('B', 'atom:semantic:edu.fudan.common.Response.status:meansInUse:envelope-code-1-success-0-rejected-or-empty')
rows.append((bkey('edu.fudan.common.Response.status'), 'adopted', basis))

basis = ("Reread order/service/OrderServiceImpl.java:338 and order/init/InitData.java:25: price is a String fare "
         "amount (e.g. \"100.0\") returned by getOrderPrice; adopted verbatim.")
canonical('B', 'atom:semantic:ts-order-service.Order.price:meansInUse:string-encoded-fare-amount')
rows.append((bkey('Order.price'), 'adopted', basis))

basis = ("Reread order/service/OrderServiceImpl.java:111,259: OrderStatus.CANCEL.getCode() is the target state of "
         "both cancelOrder and alterOrder; constant-meaning aspect distinct from the transition atoms; adopted verbatim.")
canonical('B', 'atom:semantic:ts-order-service.OrderStatus.CANCEL:meansInUse:cancelled-order-state-target')
rows.append((bkey('OrderStatus.CANCEL|semantic|meansInUse'), 'adopted', basis))

basis = ("Reread order/service/OrderServiceImpl.java:350: OrderStatus.PAID.getCode() is the target state of "
         "payOrder; constant-meaning aspect distinct from the transition atom; adopted verbatim.")
canonical('B', 'atom:semantic:ts-order-service.OrderStatus.PAID:meansInUse:paid-order-state-target')
rows.append((bkey('OrderStatus.PAID|semantic|meansInUse'), 'adopted', basis))

# ---- state transitions ----
c = canonical('A', 'atom:state:ts-order-service.Order.status:transitionsTo:caller-specified-on-modifyOrder')
basis = ("Reread order/service/OrderServiceImpl.java:322: modifyOrder sets order.setStatus(status) from the "
         "caller; kept " + c['id'] + " (pass A, operation-qualified object).")
rows.append((akey('transitionsTo|caller-specified-on-modifyOrder'), 'merged', basis))
rows.append((bkey('transitionsTo|caller-specified-status'), 'merged', basis))

ca = canonical('A', 'atom:state:ts-order-service.Order.status:transitionsTo:cancel-on-alterOrder')
cc = canonical('A', 'atom:state:ts-order-service.Order.status:transitionsTo:cancel-on-cancelOrder')
rows.append((akey('transitionsTo|cancel-on-alterOrder'), 'merged',
             "Reread order/service/OrderServiceImpl.java:111: alterOrder sets OrderStatus.CANCEL.getCode(); pass B "
             "recorded the same transition without the operation split; kept " + ca['id'] + "."))
rows.append((akey('transitionsTo|cancel-on-cancelOrder'), 'merged',
             "Reread order/service/OrderServiceImpl.java:259: cancelOrder sets OrderStatus.CANCEL.getCode(); pass B "
             "recorded the same transition without the operation split; kept " + cc['id'] + "."))
rows.append((bkey('transitionsTo|OrderStatus.CANCEL'), 'merged',
             "Reread order/service/OrderServiceImpl.java:111,259: single pass B atom covers two operations; kept the "
             "operation-split pass A atoms " + ca['id'] + " and " + cc['id'] + "."))

c = canonical('A', 'atom:state:ts-order-service.Order.status:transitionsTo:paid-on-payOrder')
basis = ("Reread order/service/OrderServiceImpl.java:350: payOrder sets OrderStatus.PAID.getCode(); kept "
         + c['id'] + " (pass A, operation-qualified object).")
rows.append((akey('transitionsTo|paid-on-payOrder'), 'merged', basis))
rows.append((bkey('transitionsTo|OrderStatus.PAID'), 'merged', basis))

# ---- persistence ----
basis = ("Reread order/repository/OrderRepository.java:16: OrderRepository extends JpaRepository<Order, String>; "
         "adopted verbatim (table mapping is already the matched table:orders atom).")
canonical('A', 'atom:state:ts-order-service.Order:persistsIn:order-jpa-repository')
rows.append((akey('state|ts-order-service.Order|static|persistsIn|order-jpa-repository'), 'adopted', basis))

c = canonical('A', 'atom:state:ts-order-service:persistsIn:mysql-order-datasource')
basis = ("Reread src/main/resources/application.yml:12-13: jdbc:mysql datasource with default database ts; same "
         "datasource fact both passes; kept " + c['id'] + " (pass A, service-level subject); the entity-level side "
         "is covered by matched table:orders and adopted atom:state:ts-order-service.Order:persistsIn:order-jpa-repository.")
rows.append((akey('state|ts-order-service|static|persistsIn|mysql-order-datasource'), 'merged', basis))
rows.append((bkey('state|ts-order-service.Order|static|persistsIn|mysql-ts-database'), 'merged', basis))

basis = ("Reread order/entity/Order.java:63: @Column(name = \"from_station\") on field from; adopted verbatim.")
canonical('B', 'atom:state:ts-order-service.Order.from:persistsIn:from-station-column')
rows.append((bkey('Order.from'), 'adopted', basis))

basis = ("Reread order/entity/Order.java:66: @Column(name = \"to_station\") on field to; adopted verbatim.")
canonical('B', 'atom:state:ts-order-service.Order.to:persistsIn:to-station-column')
rows.append((bkey('Order.to'), 'adopted', basis))

# ---- assemble ----
all_keys = set(entriesA) | set(entriesB)
row_keys = [k for k, _, _ in rows]
assert len(row_keys) == len(set(row_keys)), 'duplicate adjudication keys'
missing = all_keys - set(row_keys)
extra = set(row_keys) - all_keys
assert not missing, f'missing: {missing}'
assert not extra, f'extra: {extra}'

# canonical atom sanity: unique ids
ids = [a['id'] for a in canon]
assert len(ids) == len(set(ids)), 'duplicate canonical atom ids'

out = {
    'service': 'ts-order-service',
    'adjudications': [{'key': k, 'decision': d, 'basis': b} for k, d, b in rows],
    'canonicalAtoms': canon,
    'coverage': {
        'assignedEntryCount': len(all_keys),
        'adjudicatedEntryCount': len(row_keys),
    },
}
dest = os.path.join(RUN, 'adjudications', 'adj-order.json')
json.dump(out, open(dest, 'w'), indent=2, ensure_ascii=False)
print('entries', len(all_keys), 'rows', len(row_keys))
from collections import Counter
print(Counter(d for _, d, _ in rows))
print('canonical atoms', len(canon))
