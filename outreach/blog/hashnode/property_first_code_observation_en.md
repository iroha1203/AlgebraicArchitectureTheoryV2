# Code Review Starts with What Must Stay True

Software development has long assumed that people will read and understand the code. We choose clear names and break up long functions so that the next person can follow our intent.

But when AI produces code continuously, human reading speed becomes a bottleneck. Reviewing a change means looking beyond the diff: surrounding logic and existing requirements matter too. The amount we need to read keeps growing.

We need a way to observe code. Start by deciding which properties a change must preserve, then extract the information needed to check them. The aim is to judge a change by what it preserves and what it alters, without requiring someone to read the entire implementation.

## Express the properties you care about as Laws

A **Law** states a property we want software to satisfy: how it should behave, how it should be structured, or what should remain true after a change.

Specifications describe behavior. Design rules constrain structure and dependencies. Compatibility requirements identify behavior that must survive a change. All express something we want to be true of the software. Laws generalize these different requirements so we can work with them in a common framework.

Once the subject and conditions are clear, familiar requirements can be written as Laws.

| Where the requirement comes from | Property to preserve | What to examine |
| --- | --- | --- |
| Functional specification | Create order lines in basket order | The code that creates order lines |
| Design rule | The UI layer must not call the persistence layer directly | Calls and layer membership |
| API compatibility policy | Preserve existing response fields after a change | Response definitions before and after the change |
| Business rule | A refund must not exceed the amount paid | The relationship between payment and refund amounts |

## Define an Atom vocabulary for checking those Laws

To check a Law, we need to decide what to look for in the code and how to record it. **Atom definitions** provide that vocabulary. Each fact we extract is recorded as an Atom using those definitions.

For “the UI layer must not call the persistence layer directly,” we record who calls whom and which layer each belongs to. For order-line sequencing, we record the kind of operation and its processing order. The same code calls for different observations depending on the property we want to check.

An **ArchMap** collects the facts extracted from the code in this vocabulary.

| Element | Role |
| --- | --- |
| Law | States a property the subject must satisfy |
| Atom definitions | Define the kinds of subjects and values we can record |
| ArchMap | Records observed facts in that vocabulary, with references to the source |

We ask AI to observe the code, then check whether the values in the ArchMap satisfy the Laws.

The Law and Atom vocabulary is independent of any particular language or framework. If we define operations by their meaning, such as “create an order line” or “allocate stock,” we can use the same Laws for Python and Java implementations. AI reads each implementation and records what it finds in the shared vocabulary.

It can also interpret what a piece of code does in business terms. It might follow a sequence of calls across several functions and record, “this is where stock is allocated.” Observations can include meaning that is difficult to capture from syntax and type information alone.

## A real example: fixing stock allocation changed the display order

[django-oscar](https://github.com/django-oscar/django-oscar), an e-commerce framework built with Python and Django, has a useful example of a stock-allocation change affecting the order in which purchased items appeared.

When an order is placed, the application creates order lines from the basket and allocates stock. Originally, both operations ran in one loop. In pseudocode:

```python
for line in basket_lines:
    create_order_line(line)
    allocate_stock(line)
```

A change introduced a consistent processing order for stock allocation. The aim was to acquire stock locks in the same order when multiple orders were placed concurrently. Basket lines were sorted by their stock records before entering the loop:

```python
for line in sort_by_stockrecord(basket_lines):
    create_order_line(line)
    allocate_stock(line)
```

This aligned the stock-allocation order. It also changed the order in which order lines were created, because both operations were still in the same loop.

Suppose a basket contains a notebook followed by a pen, but their stock records sort in the opposite order. The code now creates the pen's order line first. Since django-oscar retrieved order lines in primary-key order, the change affected how items appeared in order details, invoices, and emails.

### Write down the two Laws

There are two properties to check:

| Law | Property |
| --- | --- |
| L1 | Allocate stock in stock-record order |
| L2 | Create order lines in basket order |

L1 is what the change is meant to achieve. L2 is what it must preserve.

### Ask AI to extract the operations and their order

To check these Laws, we need the kind of each operation and the order in which it runs. We define the following Atom fields:

| Field | What to record |
| --- | --- |
| `kind` | Order-line creation or stock allocation |
| `sequence` | Basket order or stock-record order |
| `loop` | Which loop contains the operation |

Recording `loop` also helps explain why the two operations were reordered together.

I gave AI these definitions and Laws and asked it to read the code before and after the sorting change. The resulting ArchMap contained these observations:

| Version | Operation | Order | Loop |
| --- | --- | --- | --- |
| Before the change | Create order line | Basket order | 1 |
| Before the change | Allocate stock | Basket order | 1 |
| After sorting | Create order line | Stock-record order | 1 |
| After sorting | Allocate stock | Stock-record order | 1 |

The ArchMap also records source locations, so a value can be checked against the code it came from.

### Check both Laws with ArchSig

**ArchSig** is a tool under development that checks observed information against Laws. Passing the Atom definitions, Laws, and ArchMaps to v0.6.0 produced these results:

| Version | L1: allocate in stock-record order | L2: create order lines in basket order |
| --- | --- | --- |
| Before the change | Not satisfied | Satisfied |
| After sorting | Satisfied | Not satisfied |

The stock-allocation order was fixed, but the order-line sequence changed with it. An effect that is easy to miss when reviewing only the intended fix becomes something we can explicitly check once the property is written as a Law.

### Split the loop to satisfy both Laws

The observations show that both operations are in the same loop. That is why changing the stock-allocation order also changed order-line creation. Splitting the loop lets each operation use the order it needs:

```python
for line in basket_lines:
    create_order_line(line)

for line in sort_by_stockrecord(basket_lines):
    allocate_stock(line)
```

This is also how django-oscar was fixed. PR #4594 introduced the stock-ordering change; PR #4598 separated the loops.

Observing the repaired code with the same fields gave:

| Operation | Order | Loop |
| --- | --- | --- |
| Create order line | Basket order | 1 |
| Allocate stock | Stock-record order | 2 |

Checking this ArchMap showed that both L1 and L2 were satisfied. Stock allocation now followed the required order, while order lines still followed the basket.

### Treat specifications and conventions as properties to preserve

This example brings together an internal requirement about stock processing and a user-visible requirement about display order. Software also has design rules, compatibility commitments, and business rules. Some live in specifications; others are conventions shared by the team.

Thinking of all of them as properties to preserve lets us put them on the same list of things to check after a change. That is the value of generalizing them as Laws: we can consider what we want to fix alongside what we need to keep.

For each requirement, ask what must be true, and of what. The information needed to check it becomes clearer. Laws turn specifications and conventions into questions we can investigate in the code.

## Treat Laws as equations and explore the solution space

If a Law is not satisfied, what should change? Expressing Laws as equations lets us look for repairs among their solutions. Software that satisfies several Laws at once can be viewed as a solution to a large system of simultaneous equations.

Let \\(x\\) be a tuple of variables, and express the Laws as:

$$
f_1(x)=0,\quad f_2(x)=0,\quad\ldots,\quad f_m(x)=0.
$$

The tuples satisfying every equation form a solution set:

$$
\mathcal S=\{x\mid f_1(x)=\cdots=f_m(x)=0\}.
$$

Diagnosis asks whether the current values belong to \\(\mathcal S\\). If they do not, we can search within \\(\mathcal S\\) for a state to move to. The same Laws support both finding a problem and repairing it.

### Each equation narrows the choices

Take two rational-valued variables, \\(u\\) and \\(v\\), and one equation:

$$
u+v=2.
$$

There are infinitely many solutions, including \\((u,v)=(0,2),(1,1),(2,0)\\). In general, a solution has the form \\((t,2-t)\\), with \\(t\\) free to vary.

Now add \\(u-v=0\\):

$$
\begin{cases}
u+v=2,\\
u-v=0.
\end{cases}
$$

Adding the equations gives \\(2u=2\\), so the solution is uniquely \\((u,v)=(1,1)\\). If we also require \\(u=0\\), no solution satisfies all three equations.

### View the solutions geometrically

Treating the variables as coordinates gives the solutions a geometric shape. The equations \\(u+v=2\\) and \\(u-v=0\\) describe lines, and \\((1,1)\\) is their intersection. Each additional equation narrows the candidates to points satisfying all the conditions.

Algebraic geometry develops this idea using polynomials and rings. Specifying the values, operations, and relations lets us study spaces of solutions and maps between them.

**Algebraic Architecture Theory (AAT)** brings this approach to software structure. It constructs Law equations and solution spaces from data describing states and operations. Studying these spaces gives us a way to reason about diagnosis, change, and repair. ArchSig applies this theory to software analysis.

### The allowed changes determine where we can search

A repair does not necessarily allow every variable to change. Let \\(x_0\\) be the current state, and let \\(\mathcal A(x_0)\\) contain the states reachable through permitted changes. A repair candidate must also satisfy the Laws, so it lies in:

$$
\mathcal A(x_0)\cap\mathcal S.
$$

If this intersection is empty, the permitted changes cannot produce a repair. Otherwise, its elements are candidate repaired states.

The system above had the solution \\((1,1)\\). Starting from \\((0,2)\\), we cannot reach it if \\(u\\) must stay at zero and only \\(v\\) may change. If both can change, we can choose \\((1,1)\\). Whether a repair exists depends on what we are allowed to change, even when the Laws stay the same.

## Build one structure from Atoms and Laws

AAT brings Atoms and Laws together with the available operations and the relationships between parts. Its distinguishing idea is to use this common structure for diagnosis, repair, and comparison of changes. The foundations are developed in [Foundations of Algebraic Architecture Theory: A Rising Sea of Geometry, Transport, Comparison, and Reconstruction](https://arxiv.org/abs/2609.27638).

### Bring facts, operations, and conditions together

AAT starts mathematically from Atoms. Giving relationships to Atoms that represent components and operations lets us treat a software structure as a mathematical object. Laws specify the equations that object must satisfy.

We also include the allowed operations and the states they can produce. This lets us ask whether Laws still hold after an operation and what is preserved by a change.

To study a large object in parts, we specify the parts and what they share. We include the data for each part and how discrepancies between parts are measured. The paper calls the resulting structure a *full geometry*.

### Use the same structure to ask different questions

Several familiar software questions can then be studied within that structure:

| Software question | Mathematical question |
| --- | --- |
| Can individually correct parts conflict when combined? | Can local states be glued into a global state? |
| Can we omit detail and still detect the same problems? | Is diagnosis preserved when the reading changes? |
| Do different orders of changes or migration paths remain consistent? | Do the structures and operations obtained along different paths correspond? |
| What changes preserve the requirements? | Can we classify structure-preserving maps? |
| Can descriptions from separate teams determine the overall design and its changes? | Can we reconstruct objects and maps from local data? |

For example, suppose we want to change a data format while keeping the same operations available. Let \\(X\\) and \\(Y\\) be the objects before and after conversion, \\(h\\) the conversion map, and \\(T_X,T_Y\\) the respective operations. We can express the required relationship as:

$$
h(T_X(x))=T_Y(h(x)).
$$

Operating and then converting must give the same result as converting and then operating. We can check not just that values correspond, but that the conversion respects the operations on them.

## When can we omit detail without changing the diagnosis?

Call a way of extracting information from an object a *reading*. A reading can omit detail and still be sufficient to evaluate a Law. Combining cases without retaining every distinction is called *coarse-graining*.

But if an object satisfying the Law and one violating it produce the same observation, we have discarded information we needed.

### Can the observation alone determine whether the Law holds?

Let \\(x\\) be an object, \\(q\\) a reading, and \\(L\\) the evaluation of a Law. If \\(\bar{L}\\) evaluates the Law using only the observed information \\(q(x)\\), we need:

$$
L(x)=\bar{L}(q(x)).
$$

The observed information must give the same evaluation as examining the whole object.

Suppose \\(x=(u,v)\\) and we observe only \\(q(u,v)=u+v\\). That is enough to decide whether \\(u+v=2\\). It is not enough to decide whether \\(u=v\\): both \\((0,2)\\) and \\((1,1)\\) produce an observation of 2, but only the latter satisfies \\(u=v\\).

The same principle applies to software. To check that the UI layer never directly calls the persistence layer, call relationships and layer membership are enough. We do not need to inspect every calculation inside those functions. But that information cannot tell us whether a refund exceeds the payment. Choosing the Law first helps us decide what we can leave out.

### The Atlas theorem connects observation detail to diagnosis

Some discrepancies between parts can be removed by adjusting the values in each part. Others remain. Cohomology captures this distinction, with persistent discrepancies represented by *obstruction classes*.

Consider discrepancies between three parts, A, B, and C. Suppose they sum to 1 when followed around the cycle from A to B, B to C, and C back to A.

Adjust the values at the three parts by \\(u_A,u_B,u_C\\). The discrepancies on the edges change by \\(u_B-u_A\\), \\(u_C-u_B\\), and \\(u_A-u_C\\). But those adjustments sum to zero:

$$
(u_B-u_A)+(u_C-u_B)+(u_A-u_C)=0.
$$

Adjusting the individual values changes the discrepancies along the edges, but not their sum around the cycle. The original discrepancy of 1 remains: these adjustments cannot remove it.

The Atlas theorem gives conditions under which these persistent discrepancies correspond between a detailed reading and a coarser one. Both readings must support evaluation of the Laws, and the overlaps between parts and the calculations of discrepancies must correspond as well. Under those conditions, omitting detail neither hides an obstruction nor creates an extra one.

Suppose we want to examine a large codebase at module level rather than function level. If that grouping satisfies the Atlas conditions, it preserves the diagnosis of discrepancies for the Laws being studied. We gain a basis for deciding how much to inspect: this information is enough for this diagnosis.

## Local repairs do not automatically fit together

When a large system of equations is split into parts, each part may have a solution without those solutions fitting together. Shared variables must agree.

Suppose one part solves \\(u+v=2\\) and chooses \\((u,v)=(0,2)\\). Another solves \\(v+w=3\\) and chooses \\((v,w)=(1,2)\\). Both satisfy their own equations, but they disagree on \\(v\\), so they cannot form a single solution. Keeping the first solution, we can choose \\((v,w)=(2,1)\\) for the second and obtain the global solution \\((u,v,w)=(0,2,1)\\).

Combining local solutions that agree on their shared parts is called *gluing*. AAT uses sheaves and cohomology to study gluing and the discrepancies that obstruct it.

### SAGA: use equations to find what prevents a repair

Solving equations changes variable values. Repairing software changes settings or structures through permitted operations. To use a calculation for repair, we must connect those operations to changes in values.

The SAGA comparison theorem connects obstructions constructed from repair operations with obstructions constructed from equations. When that correspondence meets the theorem's conditions, we can use the equations to determine whether an obstruction to repair remains.

For example, several services might each admit a fix, yet disagree about shared data or configuration. Those fixes cannot all be applied together. Once the permitted repairs and shared conditions are represented by the corresponding equations, a nonzero obstruction means the repairs cannot be made compatible within those operations. With the additional gluing conditions in place, a zero obstruction means a compatible global repair exists.

### Ariadne: find a repair within the allowed scope

Ariadne lets us specify what may change and what must stay fixed. It asks whether a repair is possible within that scope and finds candidates when it is.

Suppose two parts share a correction \\(u\\). One requires \\(u=x\\), and the other requires \\(u=y\\), where \\(x,y\\) are given target values:

$$
\begin{cases}
u=x,\\
u=y.
\end{cases}
$$

A solution exists only when \\(x=y\\). Subtracting the first equation from the second leaves zero on the left and \\(y-x\\) on the right. If that difference is nonzero, no choice of \\(u\\) can repair the system.

Now allow an additional correction \\(v\\) in the second part:

$$
\begin{cases}
u=x,\\
u+v=y.
\end{cases}
$$

We can choose \\(u=x\\) and \\(v=y-x\\). Broadening the allowed changes makes the target reachable.

Ariadne works with finite linear models, constructing repairs from the conditions on each part. When repair is impossible, it identifies what prevents it.

Software fixes often have constraints such as “leave the shared configuration unchanged; modify only this service's settings.” If the settings and Laws can be expressed in this model, we can determine whether that scope admits a repair before repeatedly trying patches. If it does, we can compute candidate values. If it does not, we can broaden the scope, perhaps allowing changes to shared configuration, and check again.

### Observe the information needed for a concrete repair

The system with the additional correction \\(v\\) has a solution for every \\(x,y\\). We can therefore answer “a repair exists” without knowing their values. Returning actual values for \\(u,v\\), however, requires knowing \\(x\\) and \\(y-x\\).

Deciding whether a solution exists and producing one require different information. If we read \\(x\\) and \\(y\\) separately, we need both values. If \\(x\\) is already known, only \\(y\\) remains to be observed.

If choosing a repair requires a missing configuration value, we can ask AI to inspect that configuration. The repair equations can also guide what to observe next.

## Reconstruct the whole from local descriptions

When work on a large codebase is divided among several people or agents, we may want to assemble an overall structure or change from their separate descriptions.

The local reconstruction theorem in the Rising Sea paper gives conditions for doing this. Local descriptions include operations, Laws, and agreement on shared parts, alongside information about individual components. When the required conditions hold, we can reconstruct both the overall structure and changes that preserve it.

Suppose several AI agents investigate different modules and propose changes. We put their descriptions into the form required by the theorem and check that shared parts agree and operations correspond. If the conditions hold, their local changes can be assembled into a global change. We can ask whether proposals that look reasonable individually actually fit together.

This ability to address diagnosis, repair, comparison of changes, and reconstruction through a common structure built from Atoms and Laws is AAT's central strength.

## Connections to formal verification and development with proofs

Making desired properties explicit and checking them is also central to formal methods such as [TLA+](https://proofs.tlapl.us/) and [Alloy](https://alloytools.org/about). TLA+ describes system behavior in specifications whose properties can be checked through model checking and proof. Alloy describes relations and constraints, then searches for satisfying examples or counterexamples to properties. When these models are written separately from the implementation, keeping the two aligned as code changes takes work.

[Bend 2](https://github.com/bendlang/bend) takes an approach in which rules and their proofs are written alongside the code. Rules are declared as `law`s, and the compiler checks their proofs.

A strength of applying AAT through ArchSig is that source code remains the single source of truth about the implementation, with diagnosis added afterward. Desired properties are written as Laws; the state of the implementation is observed from the current code. An ArchMap can be regenerated with each observation, so it need not be maintained by hand in parallel with the code.

AI can keep writing code while we observe and diagnose it at the points we choose. Each implementation change need not wait for a separate model or proof to be completed. This lets us check changes while retaining the speed of AI-assisted development.

[Rice's theorem](https://cs.stanford.edu/people/trevisan/cs154-12/noterice.pdf) establishes a limit on automatic analysis. Consider a property of the function a program computes. If some programs satisfy it and others do not, no algorithm can always terminate and correctly decide that property for every program. That makes the choice of Laws and models important. Within a suitable finite model or a system of linear equations, we can compute diagnoses and repairs for that scope.

## From reading code to observing it through Laws

The next step I want for ArchSig is to let users specify what may change, then find candidate repairs that satisfy the Laws within the model. If no candidate exists, the tool should identify what prevents one. If information is missing, AI can read the relevant code or specification. We can then apply a candidate to the code, observe it again, and test the result.

Where several candidates exist, people can choose among them based on performance, maintainability, and the cost of migration.

The starting point is to write down what must remain true after a change. Express it as Laws, ask AI to extract the information needed to check them, and use mathematics to reason about diagnosis and repair. That is the kind of development I want to make possible: judging changes without depending on someone reading every line.

---

Repository: [AlgebraicArchitectureTheoryV2](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2)
