# ArchSig AG measurement evidence contract

この文書は、AG measurement fixtureの`sourceRef.section`が指す恒久contractである。
各sectionはfixtureが供給する入力の意味を固定し、測定結果そのものは固定しない。

## R3

有限site、cover、restriction、law witnessを持つ基礎AG measurement入力。

## R4

observed square-free forbidden supportとrepair候補を結ぶ入力。宣言された生成元と
minimal hitting setはlaw surfaceから決まり、選択されたArchMapは各生成元の
`supportAtomRefs`と構造verdictを観測する。宣言された生成元が選択されたArchMapで
生起しない場合、構造verdictは`measured_zero`となり、未生起は`silence_by_design`
statementとして残る。未生起の生成元はviewer cageを生成しない。

## R5

common ambient law pairとTor conflictを計測する入力。

### B.5-checkout

対象artifact checkoutのsource inventory。

### B.5-inventory

law generatorとcommon ambient pairのsource inventory。

## R6

有限cochain、boundary、Laplacianを持つsheaf measurement入力。

### R6-left

左patchのsection carrier。

### R6-right

右patchのsection carrier。

### R6-boundary

overlap boundaryのsection carrierとrestriction。

## R7

period pairingとStokes auditを持つ入力。

### R7-period-alpha

第一cycleのperiod pairing。

### R7-period-beta

第二cycleのperiod pairing。

### R7-stokes-boundary

Stokes comparisonのboundary chain。

### R7-stokes-domega

Stokes comparisonのdifferential cochain。

## R8

support-localized transferとground costを持つ入力。

### R8-ground-api

ground-cost evaluatorのsource API。

### R8-ground-data

ground-cost matrixのsource data。

### R8-repair-path

selected repair pathのsource evidence。

### R8-transfer-api

support-transfer evaluatorのsource API。

### R8-transfer-data

source/target supportとpairing data。

## B.8

finite Čech obstruction fixture family。

### B.8.1

zeroまたはcover-shape exclusionを確認するtoy fixture。

### B.8.2

nonzero H1 cocycle supportを可視化可能にするfinite fixture。

## M2

source/target generatorとambient comparison context。

### M2 source generator

source側law generator。

### M2 target generator

target側law generator。

## M3

section factorizationとminimal forbidden support。

### M3 section

section carrier。

### M3 minimal forbidden support

selected minimal forbidden support。

### M3 total section assignment A

第一total assignment。

### M3 total section assignment B

第二total assignment。

### M3 partial section

partial assignment。

### M3 assignment without raw support

raw supportを欠くnegative fixture。

## M5

triple-overlap coherence input。

## M6

Mayer–Vietoris boundary-residue input。

### M6 core patch

core patchのsection。

### M6 feature patch

feature patchのsection。

### M6 boundary patch

overlap patchのsection。

### M6 patch role

各patchのrole evidence。

### M6 Mayer-Vietoris d0

selected degree-zero differential。

### M6 boundary section

boundary section value。

## AC-M10

AG measurement fixtureが同一入力からbyte-identical artifactを生成する決定性contract。
