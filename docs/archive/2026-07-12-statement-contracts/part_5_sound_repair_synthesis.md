# Part V theorem 13.4 statement contract

Issue #3196で固定する定理13.4のLean statement。synthesis ruleは各stateで
`step` / `cleared` / `noSolution`のいずれかをconstructor evidence付きで返す。
well-founded recursionがこのruleから有限runを構成し、sound traceとterminal
outputを同じrunから導く。

## Material premises

- `P : RepairComparisonProfile`: 本文のwell-founded repair comparison profile。
- `rule : (state : P.State) -> SynthesisDecision P state`: 本文のselected
  synthesis rule。各constructorがstep、cleared、certificateの証拠を保持する。
- `start : P.State`: synthesis開始state。

trace soundness、finite termination、cleared / certificate outputは独立fieldや
外部packageから受け取らず、`rule`と`P.wellFounded_ltRep`から構成する。

## Referenced definitions

```lean
inductive SynthesisDecision (P : RepairComparisonProfile)
    (state : P.State) where
  | step (next : P.State) (hstep : P.step state next)
  | cleared (hcleared : P.targetCleared state)
  | noSolution (hcertificate : P.noSolutionCertificate state)

inductive SynthesisRun (P : RepairComparisonProfile) : P.State -> Type where
  | cleared {state : P.State} (hcleared : P.targetCleared state)
  | noSolution {state : P.State}
      (hcertificate : P.noSolutionCertificate state)
  | step {state next : P.State} (hstep : P.step state next)
      (tail : SynthesisRun P next)

def SynthesisRun.trace : SynthesisRun P start -> List P.State
def SynthesisRun.depth : SynthesisRun P start -> Nat
def SynthesisRun.outputState : SynthesisRun P start -> P.State

def SynthesisRun.TraceEmitsOnlySoundSteps
    (P : RepairComparisonProfile) : List P.State -> Prop

noncomputable def synthesize
    (P : RepairComparisonProfile)
    (rule : (state : P.State) -> SynthesisDecision P state)
    (start : P.State) : SynthesisRun P start
```

## Target statements

```lean
theorem synthesize_eq
    (P : RepairComparisonProfile)
    (rule : (state : P.State) -> SynthesisDecision P state)
    (start : P.State) :
    synthesize P rule start =
      match rule start with
      | .step next hstep => .step hstep (synthesize P rule next)
      | .cleared hcleared => .cleared hcleared
      | .noSolution hcertificate => .noSolution hcertificate

theorem soundRepairSynthesis
    (P : RepairComparisonProfile)
    (rule : (state : P.State) -> SynthesisDecision P state)
    (start : P.State) :
    let run := synthesize P rule start
    SynthesisRun.TraceEmitsOnlySoundSteps P run.trace ∧
      run.trace.length = run.depth + 1 ∧
        (P.targetCleared run.outputState ∨
          P.noSolutionCertificate run.outputState)
```

## Premise classification

- `P.wellFounded_ltRep`: 本文のwell-founded comparison premise。
- `SynthesisDecision.step.hstep`: selected stepであり、
  `P.step_decreases`からstrict decreaseを構成する。
- `cleared` / `noSolution` constructor evidence: ruleのterminal constructorが
  本文どおり保持するoutput evidence。
- finite trace: `WellFounded.fix`が構成する有限inductive `SynthesisRun`から導く。
- trace soundness: 各`SynthesisRun.step`の`P.step state next`と
  `P.step_decreases`による`P.ltRep next state`を、隣接trace全体へ帰納する。

`True`、結論相当Prop field、certificate escape、structure-field escapeは用いない。
solver completeness、最短repair、global optimality、全law universe同時改善は
主張しない。
