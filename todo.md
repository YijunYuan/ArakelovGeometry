# `bost.pdf` 的 Chen–Moriwaki 依赖覆盖审计

审计日期：2026-11-11。基准为本仓库 `lite` 分支的
`86cf85672a45934c1cf63278904fadd5cf1e0388`，包括已经接入的 HarderNarasimhan 库。
以下“已有覆盖”依据实际 Lean 定义、定理及其假设判断；没有把 README 中的章节说明当作证明。

## 范围与阅读方式

- 论文：本地 `bost.pdf`，*Rectangular Specht lattices and tensor semistability —
  A proposed proof over adelic curves of characteristic zero*，修订日期 2026-11-10，35 页。
  SHA256：`2b8639841b17e421a9a62bf32d158e1bb5529dfe37d286a0dc830e35019a4c57`。
  下文论文页码同时是 PDF 页码和印刷页码。
- 书：论文参考文献 **[2]**，Chen–Moriwaki，*Arakelov Geometry over Adelic Curves*
  （2020）。核对的是[作者提供的 PDF](https://chenhuayi.lab.westlake.edu.cn/Recherche/adelic_curve.pdf)，
  正文标注 2019-10-05、Version 1.2 的预印版本，共 466 页。下文书中页码均指印刷页码；
  第 5 章的 PDF 页码为印刷页码加 16。
- 论文参考文献 **[3]** 是两位作者的另一本书 *Positivity in Arakelov Geometry over
  Adelic Curves*（2024），**不属于此次范围**。其他作者的结果也不列入待办。
- **A 部分**列主定理 1.1 证明实际需要、当前尚未完整覆盖的书中输入，包括前置引理所用的输入。
  区分“直接引用”“书中定理的前提/表述转换”和“已有组件尚缺的数学兼容性定理”。
  **B 部分**逐组记录主证明已覆盖的输入，避免重复开发。
  **C 部分**单列仅用于比较、策略说明或背景特例的引用，不把它们当成主证明的阻塞项。
- “尚未覆盖”不等于“没有同名声明”。已有等价结论或可以直接组合的基础结论，均注明复用路径。
  新增某个 `structure`、替换记号或封装一句话推论，本身不算数学缺口。

这是依赖覆盖审计，不是对论文提出的证明作正确性认证，也不是论文全部形式化工作的清单。

**实施范围更新（2026-11-11）。** 按用户明确要求，`lite` 分支只以论文主定理 1.1
的实际消费者为目标，不以恢复 Chen–Moriwaki 原定理的全部一般性为目标。
§7 优先实现二元情形；有限族主结论由二元结论迭代。允许给出足够的特例、单向结论，
或经完整证明的替代论证。已完成的较强结果继续复用；额外的一般化不再阻塞验收。
主定理的可数特征零域、proper adelic curve 和实际 Hermitian 完备范数范围不缩减。

**状态说明。** 以下初始覆盖分析保留上述基准提交的审计记录，不能当作当前未完成清单。
各项“完成记录／部分进展”和 [README 的 Bost 对照表](README.md) 记录实施状态及允许的精简。
目前 A1–A7 的保留范围已完成；A8、A9 的最终原域消费者仍在组合，不提前勾选。

## A. 主定理所需输入与实施状态

主证明的使用链是：§2 的 adelic/HN 基础 → §6 引理 6.1 与定理 6.2 的几何斜率不等式
→ 对偶商形式 (43) → §7 的滤过、分次范数和变分论证 → 定理 1.1。
下面的待办只截取这条链上的 Chen–Moriwaki 输入。

### A1. 正交张量与对偶、重排的完整范数兼容性

- [x] 补齐 Hermitian 正交张量的规范对偶等距，并将它与现有有限张量和完备化接口连接。

**完成记录（2026-11-11）。** `013447a`、`76ee302` 已认证实际完备纤维上的二元和有限张量对偶等距、
交换/结合、有限分组/重索引、张量幂重组及 evaluation/base-change 相容性。
`Tensor.HermitianDual` 内核检查、42 项传递公理检查及独立审查通过。
论文的具体二指标块转置由已证有限分组和重索引接口组装，不另称已公开同名专用定理。

**书中出处。** §1.2.9，pp.77–78，公式 (1.48) 后的未编号断言：Hilbert–Schmidt
张量范数的对偶等于对偶空间上的正交张量范数；规范交换、结合同构保持范数。
有限位的对应结果为推论 1.2.20，p.54。

**论文实际使用。** p.26 的 (40) 及其后的
`Ψ_d = j_d^∨ ∘ i^{⊗d} ∘ ι_V`，p.27 的逐处压缩估计 (41)，以及 p.28 从
`Q^∨ ⊂ W^∨` 推出商版本 (43)。这里需要识别整个张量空间的范数，不能只检验纯张量。

**初始审计覆盖及缺口。**
[Tensor/DualNorm.lean](ArakelovGeometry/AdelicVectorBundle/Tensor/DualNorm.lean) 的
`mixedTensorPair_dual_norm_eq_injective`、`mixedTensorPair_dual_pullback`
处理的是 mixed/projective 与 injective 范数。
[Tensor/Hermitian.lean](ArakelovGeometry/AdelicVectorBundle/Tensor/Hermitian.lean) 已有真正的
`orthogonalTensorPair`；[HermitianTensor.lean](ArakelovGeometry/Analysis/Tensor/HermitianTensor.lean)
已有 `orthogonalTensorCoordinates`、`orthogonalTensorCore_tprod` 和
`norm_tensorDualEval_le_orthogonal`。这些尚未给出 Hilbert 张量上任意对偶张量的规范等距式。
有限位可复用现有 mixed/injective 对偶式及 ultrametric 双对偶结果；主要新增局部证明在无穷位。

**验收内容。** 对有限维 Hermitian 因子，在规范代数同构下证明

$$
  (E\otimes_{\perp}F)^\vee\simeq_{\mathrm{isom}}
  E^\vee\otimes_{\perp}F^\vee.
$$

范数等式必须作用于实际完备纤维中的任意元素。结合、交换、有限族推广及张量幂重组作为
这一接口的组装工作，须与 `tensorBaseChangeEquiv` 和代数 evaluation 相容。
可以先补二元结果再迭代；不必为论文另外定义一套张量范数。
商对偶等距、对偶度数变号已经覆盖，见 B2、B3，不属于本项。

### A2. 主证明使用的几何半稳定性定义及两种表述的对应

- [x] 建立 Plücker 不变量形式的几何半稳定性，并证明它与书中用于商空间的半稳定性表述相容。

**完成记录（2026-11-11）。** `InvariantTheory/{Semistability,QuotientDeterminant,Linearization,Plucker,Projective}.lean`
已实现有限维情形的齐次不变量、生成元独立性、实际商行列式射影点、标量扩张作用兼容性及
SL 与行列式扭曲 GL 表述的对应。`Projective` 内核检查与 19 项传递公理检查通过；
认证记录见 `.archon-horizon/runs/0002/sessions/0006-horizon-A2/A2Verification.json`。
这不包含任意进一步扩域的半稳定性下降，也不包含 A8 的数值判据。以下“当前覆盖及缺口”保留原始审计背景。

**书中出处。** §5.2，尤其定理 5.2.7、定义 5.2.8，pp.305–306；
注记 5.2.9、推论 5.2.10，pp.306–309 中商空间行列式点及其线性化。

**论文实际使用。** p.26 在代数闭包上取正次数齐次不变量多项式，要求它在
`det(V) ⊂ ∧^s W` 的非零向量上不为零；p.27 据此取出 `p` 并构造 `q`。
p.28 把商 `W ↠ Q` 的几何半稳定性定义为对偶子空间 `Q^∨ ⊂ W^∨` 的 Plücker
半稳定性。p.31 随后把这个条件交给书中定理 5.4.3。

**初始审计覆盖及缺口。**
[HN/Destabilizing.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Destabilizing.lean)
的 `IsMeanSlopeSemistable` 是算术斜率半稳定性。
已有的代数扩域斜率比较也属于算术理论，不能代替群作用下的 GIT 半稳定性。
当前项目及其依赖中未找到完成上述 Plücker 不变量定义与商线性化对应的定理。
外幂、行列式、线性群、代数闭包等基础对象应直接复用 mathlib。

**验收内容。**

1. 对 `∏ SL(E_j)` 在 `W = ⊗ E_j` 上的作用，定义论文实际使用的 Plücker
   几何半稳定性；证明不依赖行列式线非零生成元的选择，并明确标量扩张及对偶作用。
2. 对非零商 `Q`，连接其对偶 Plücker 形式与书中
   `W^{⊗r} ↠ det(Q)` 所确定的射影点，`r = dim Q`。
3. 连接论文的 `∏ SL(E_j)` 形式与书中的 `∏ GL(E_j)` 行列式扭曲线性化。
   若 `a_j = dim E_j`、`A = ∏ a_j`、`b_j = A/a_j`，书中的线性化是
   `O(A) ⊗ π* (⊗ det(E_j^∨)^{⊗ r b_j})`。应检查中心的权重、对偶方向及符号，
   不能仅因两处都称“semistable”就直接应用定理。

只需建立此有限维表示情形及必要的标量扩张兼容性；无需把整节概形 GIT 全部复制进项目。
论文 p.26 的 null-cone 旁述和参考文献 [4] 中的额外结论不计为本项的待证 CM 定理，见 D。

### A3. 两个任意有限实滤过的共同适配基

- [x] 证明两个有限实滤过存在同一个适配基，并提供对两个滤过同时有效的坐标刻画。

**完成补记（2026-11-11）。**
[CommonAdaptedBasis.lean](ArakelovGeometry/LinearAlgebra/CommonAdaptedBasis.lean)
与 [Norm/CommonAdaptedBasis.lean](ArakelovGeometry/AdelicVectorBundle/Examples/Trivial/Norm/CommonAdaptedBasis.lean)
已给出共同基、两组实权重、所有阈值的张成及坐标判据，以及实际完备纤维上的两个范数公式，包含零维情形。
`Submodule.exists_common_weighted_basis` 的实际范数消费者为
`exists_common_orthogonal_basis_ofTrivialFiltration`。窄模块核检查、八项传递公理检查及独立审查均通过；
认证提交为 `22978d0`，加入公开入口后的全项目构建也已通过。下述“当前覆盖及缺口”保留原审计基准的记录。

**书中出处。** 命题 5.1.3，p.300：平凡赋值域上两个超度量范数有共同正交基；
推论 5.1.4，p.301：两个有限旗有共同适配基。两种形式通过 §5.1 的范数—滤过对应连接。

**论文实际使用。** p.28 定义滤过配对；pp.29–32 在共同适配基上记录两个权重并作变分。

**初始审计覆盖及缺口。**
[FiniteFiltration.lean](ArakelovGeometry/LinearAlgebra/FiniteFiltration.lean) 的
`Submodule.exists_strictMono_flag_and_jumps_of_antitone` 已经从反单调、上下端取到及左局部常值
提取有限严格旗、跳跃及右极限。
[Filtration/Inverse.lean](ArakelovGeometry/AdelicVectorBundle/Examples/Trivial/Filtration/Inverse.lean)
已有任意此类滤过的 `ofTrivialFiltration` 和双向还原定理。
[Norm/AdaptedBasis.lean](ArakelovGeometry/AdelicVectorBundle/Examples/Trivial/Norm/AdaptedBasis.lean)
的 `exists_basis_adapted_trivialFiltration`、`exists_basis_orthogonal_trivialFiltration`
只给单个滤过的适配基。分别选择两个基并不能得到共同适配基。

**验收内容。** 对任意两个这样的实滤过，返回一个基及两组权重，使每个滤过步骤都是对应权重
不小于阈值的基向量的张成。零维情形应有明确约定；后续归一化配对只用于正维空间。
不把“实滤过”“有限跳跃”“单个适配基”整体重写成缺失项。

### A4. 任意滤过的分次期望、配对、范数与归一化

- [x] 补齐与基选择无关的滤过数值运算，以及固定共同适配基上的权重运算公式。

**完成记录（2026-11-11）。** 实际期望、配对与变分接口已由 `9681df1`、`1701739`
认证；两个终端模块内核检查及 60 项传递公理检查通过。A7 已实际消费这些接口。

**书中出处。** 定义 5.1.1、命题 5.1.2(2)，p.298；§5.4 及命题 5.4.1，pp.312–313。

**论文实际使用。** p.28 定义 `gr`、`Σ`、`e`、配对、范数、归一化及平凡滤过；
pp.31–32 用它们定义并变分 `Θ`。其中

$$
 \operatorname{gr}_{\mathcal F}^{t}E
   =\mathcal F^tE/\mathcal F^{>t}E,\qquad
 e(\mathcal F)=\frac{1}{\dim E}\sum_t t\dim\operatorname{gr}_{\mathcal F}^{t}E,
$$
$$
 \langle\mathcal F,\mathcal G\rangle
   =\frac{1}{\dim E}\sum_i x_i y_i,\qquad
 \|\mathcal F\|^2=\langle\mathcal F,\mathcal F\rangle.
$$

**初始审计覆盖及缺口。** 已有任意滤过到平凡位 adelic bundle 的构造、实际 degree/slope，
以及 HN 专用的分次对象和加权和；例如
[Hermitian/Degree.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Hermitian/Degree.lean)
的 `sum_hermitianHNFactor_rank_mul_slope_eq_degree`。
这些没有给出两个任意滤过的配对及共同适配基无关性。
`e(F)` 可以复用关联平凡位 bundle 的 slope，缺的是其分次/基权重公式及兼容性，
无需另造一个算术斜率概念。

**验收内容。**

1. 一般滤过分次商和有限支集；证明期望等于基权重的平均值，也等于关联平凡位 bundle 的斜率。
2. 证明命题 5.4.1 的分次度数公式，从而使配对不依赖 A3 中基的选择。
   这里分次商上使用的是另一个滤过诱导的平凡赋值范数，不能混成原 adelic 范数。
3. 自配对非负，等于零当且仅当滤过平凡；所有权重减去 `e(F)` 后得到期望零的滤过。
4. 在固定共同适配基上，把权重 `x_i` 改为 `x_i + ε y_i` 时，给出期望的线性公式和
   自配对的二次展开。只在这个共同基所确定的运算中使用这些恒等式，不能假设所有滤过天然构成向量空间。

依赖 A3。论文自身的商期望单侧导数引理不是命题 5.4.1，见 D。

### A5. 张量滤过、商滤过及规范分次张量分解

- [x] 构造二元情形任意给定实权重的张量/商滤过，证明它们与范数实现及规范分次映射相容。

**商部分完成补记（2026-11-11）。**
[Norm/Quotient.lean](ArakelovGeometry/AdelicVectorBundle/Examples/Trivial/Norm/Quotient.lean)
与 [Filtration/Quotient.lean](ArakelovGeometry/AdelicVectorBundle/Examples/Trivial/Filtration/Quotient.lean)
已证明实际完备商范数的最小 lift 存在，并证明
`trivialFiltration_pushforward_ofTrivialFiltration` 的逐阈值像等式，保留闭端点与零维情况。
两个模块的核检查、五项传递公理检查及独立审查通过，认证提交为 `824afb3`、`f065fb0`。
二元张量范数对应、规范分次直和及其自然性也已完成；`98a77f7` 认证 14 个蓝图节点，
最终内核检查及 66 项传递公理检查通过。已有的有限族权重和商公式保留复用；
任意有限族的额外分次细化不属于二元主证明的验收门槛。

**书中出处。** 定义 5.1.5、注记 5.1.6，p.301；定义 5.1.1，p.298；
命题 5.5.5，p.318。商滤过与商范数的对应也用于例 5.2.6 和推论 5.2.10。

**论文实际使用。** pp.28–29 定义

$$
 (\mathcal F_Q)^t=q(\mathcal F^t),\qquad
 (\mathcal P_E\otimes\mathcal P_F)^\gamma
   =\sum_{t+u\ge\gamma}\mathcal P_E^t\otimes\mathcal P_F^u,
$$

并使用 (44) 的规范同构

$$
 \bigoplus_{t+u=\gamma}
   \operatorname{gr}_{\mathcal P_E}^{t}E\otimes
   \operatorname{gr}_{\mathcal P_F}^{u}F
 \simeq
   \operatorname{gr}_{\mathcal P_E\otimes\mathcal P_F}^{\gamma}(E\otimes F).
$$

**初始审计覆盖及缺口。**
[Degree/Flag/Basic.lean](ArakelovGeometry/AdelicVectorBundle/Degree/Flag/Basic.lean) 的
`flagQuotientOfMeasurableBase` 和 HN 的 `hermitianHNGradedPiece` 已有实际子商；
一般滤过已有右极限及重构，范数族已有实际 `pushforward`/quotient。
mathlib 的 `TensorProduct.quotientTensorQuotientEquiv`
（`Mathlib/LinearAlgebra/TensorProduct/Quotient.lean`）可处理底层商张量代数。
尚缺张量权重公式、规范分次分解及这些对象之间的兼容性证明。
特别地，商滤过对象本身已经可以构造成
`trivialFiltration (pushforward (ofTrivialFiltration F) q)`，其有限性、分离性及左局部常值性
由已有定理给出。商这部分缺的是它与 `t ↦ (F t).map q` 的精确对应，而不是新的商范数或一般商滤过存在理论。
可利用 `finite_range_trivialSeminorm`、`pushforward_norm_eq_sInf` 和
`trivialCompletedTensorEquiv_baseChange`，在平凡赋值的有限范数值集合上证明 lift 的最小值取到。

**验收内容。**

1. 商像和张量权重和仍满足有限实滤过条件；保持原来的权重，允许某些商分次消失或总权重重合。
2. 证明张量适配基的权重可相加、上述张成公式与平凡赋值下的 ε 张量范数对应；
   商滤过对应实际商范数。不能用“重新计算商的算术 HN 滤过”代替给定滤过的商。
3. 构造 (44) 的规范线性同构，以及到 `gr^γ(Q)` 的规范满射，并证明与限制、商和张量映射交换。
4. 如采用书中的细化旗实现，保留每个细化因子的原始总权重，再正确合并同权重因子。

命题 5.5.5 的正式陈述是“存在细化，其相邻子商是各因子分次的张量”；
上面的整层分次直和同构出现在该命题的证明中。二者应明确连接，不能混淆细化步骤与原滤过步骤。
本项是代数和滤过部分，范数估计另见 A6。

### A6. 分次张量分量压缩与有限像旗的 HN 度数估计

- [x] 证明 A5 的二元规范分次分量映射及其商复合逐处压缩，并由有限共同像的 HN 旗推出主证明所需度数界。

**完成记录（2026-11-11）。** `434d725` 的 `Tensor/Graded`、`Degree/Flag/ImageHN`、
`Tensor/GradedDegree` 已证明实际完备纤维分量压缩、有限像 HN 度数界，以及同一组 HN 提升／基上的
`N(ε) ≤ N(0) + εδ` 和 `δ ≤ μ(Q)`。63 项传递公理检查、独立审查及 A6→A9 直接消费者检查通过。
这一单侧估计足够供 Bost pp.29–32 使用；不额外要求整正交和压缩、精确仿射恒等式或完整 CM (5.13)。
严格小秩张量 HN 兼容性仍是显式的主定理归纳条件；完整 HN 识别和 Bost 主定理不在本项完成声明中。

**书中出处。** 注记 5.5.6，p.319；其局部依据包括命题 1.1.58、1.1.60、
1.2.36、1.2.57–1.2.58 的限制/商张量范数比较。

**论文实际使用。** p.29 在 (44) 左侧取张量范数的正交直和，右侧取张量 bundle 的实际子商范数，
断言规范同构逐处压缩；复合到 `gr^γ(Q)` 的满射也压缩。
引理 7.1 由此比较度数；引理 7.2，p.30，必须区分来自 `C_γ` 的商范数和来自 `Q`
的实际子商范数，才能使用式 (45)。

**初始审计覆盖及缺口。**
[Tensor/PairMap.lean](ArakelovGeometry/AdelicVectorBundle/Tensor/PairMap.lean) 已有
`orthogonalTensorPair_restrict_map_norm_le`、
`orthogonalTensorPair_map_norm_le_of_norm_eq`，以及有限族 projective/injective 张量映射的压缩估计。
现有实际商范数也有商映射的压缩性质。
缺的是 A5 的规范分次映射与这些范数的兼容性，尤其是同时包含多个同总权重分次的正交直和。

**采用的较弱路线。** 原书注记 5.5.6 陈述每个细化因子的压缩，论文则使用同总权重
整个正交直和的压缩。本项目改写引理 7.1、7.2 的消费者：只证各分量实际压缩，
再按它们的像累加为有限旗，用满射斜率比较和实际 Hermitian 旗度数加性得到所需界。
这不声称逐分量压缩推出 ℓ² 和映射压缩，也不要求先构造整个直和的范数。

具体地，若有限个压缩映射 `f_i : C_i → Q` 的像共同张成 `Q`，令
`S^λ Q = Σ_i f_i(HN(C_i)^λ)`。固定 `λ` 后，各非零源 HN 分次均半稳定且斜率为 `λ`，
它们诱导压缩映射到 `gr_S^λ Q` 并共同张成；累加像旗使每个非零相邻实际子商的斜率至少为 `λ`。
两次旗度数加性给出 `deg(Q) ≥ Σ_λ λ dim(gr_S^λ Q)`，即正秩时 `μ(Q) ≥ e(S)`。
引理 7.2 中由较小秩的张量 HN 归纳假设识别 `S` 为论文的次权重像滤过，再得到所需单侧期望上界和斜率界。
该替代路线的 Lean 实现与消费者已完成；不另要求论文中更强的精确仿射恒等式。

**验收内容。** 使用现有 `NormFamily` 构造的真实限制、商和正交张量范数，
证明每个规范分次分量映射在每个完备纤维的**所有向量**上满足范数不增，并证明商复合的同样性质。
此外证明上述有限共同像 HN 度数引理，包含严格右极限与有限像和交换、诱导实际子商压缩、
次权重滤过识别及零像处理。较小秩的张量 HN 归纳假设须显式标明，不能隐藏为无条件结论。
不得只给抽象线性同构、只检查纯张量，或把所需压缩性作为额外假设。
对于 (44) 的同构、或同一个 `Q_γ` 上两种范数的比较，所得等秩度数比较可复用
[Degree/Supermodular.lean](ArakelovGeometry/AdelicVectorBundle/Degree/Supermodular.lean)
中的 `degree_le_of_completed_contraction`。
若 `C_γ ↠ Q_γ` 降秩，则应使用
[Slope/LinearMap.lean](ArakelovGeometry/AdelicVectorBundle/Slope/LinearMap.lean) 中的
`minimalSlope_le_slope_add_mapHeight_of_surjective`，结合高度不大于零和源的半稳定性；
不能直接套用要求线性等价的等秩度数定理。

### A7. 子商滤过的提升及期望、配对公式

- [x] 实现书中的滤过提升，证明它诱导指定的子商滤过，并给出所需加权度数公式。

**完成记录（2026-11-11）。** `bbe6695`、`82d0594` 已认证实际子商滤过提升与 HN 专门化。
`exists_hermitianHN_quotient_lift` 构造所需基和提升，并返回每个实际商切片相等、期望及配对恒等式；
`HNLift` 内核检查、27 项传递公理检查及独立审查通过。

**书中出处。** §5.5、注记 5.5.1、定义 5.5.2，p.317。
定义 5.5.3 和注记 5.5.4 的细化构造仅在组织旗及分次时需要，不额外要求实现整套未使用的细化理论。

**论文实际使用。** p.29 对 `P_E` 的每个分次 `E_t` 取其 HN 适配基并提升到 `E`，
得到 `R_E`；对 `F` 同样操作。p.32 使用

$$
 e(R_E)=\widehat\mu(E),\qquad
 (\dim E)\langle P_E,R_E\rangle
   =\sum_i t_i\widehat{\deg}(U_i/U_{i-1}).
$$

**初始审计覆盖及缺口。** 已有真实子商、每个子商的 HN 滤过与适配基，以及
[Degree/Flag/Hermitian.lean](ArakelovGeometry/AdelicVectorBundle/Degree/Flag/Hermitian.lean)
中的 `sum_flagQuotient_degree_eq_of_isHermitian`。
尚缺把指定的多个分次滤过提升为一个环境滤过，并证明上述兼容性和配对公式。
环境空间自身的 HN 滤过一般不是这里选出的提升。

**验收内容。** 给定有限旗及每个相邻子商上的滤过，提升其适配基并赋予原子商权重；
返回与原旗共同适配的基，证明诱导的每个子商滤过确实等于输入，并证明提升的 degree/expectation
加和公式及与原旗权重的配对公式。再将输入专门化为各子商的实际 HN 滤过，得到论文显示的两个恒等式。
此提升依赖基和 lift 的选择，不能宣称它是规范唯一的。
依赖 A3–A5 和已有的 Hermitian 旗度数加性。

### A8. 几何半稳定性与滤过数值判据的连接

- [ ] 补齐数值判据在 A9 中所用的方向：几何不稳定性产生严格负值的归一化滤过。

**部分进展（2026-11-11）。** Laurent／一般 DVR Cartan、实际商行列式负权重、SL 张量幂半单性、
二元有界多项式轨道分离、实际轨道到 DVR 群元素、原系数剩余域下降及代数闭域负滤过均已检查。
`Rationality.lean` 另已证明实际闭域负候选向任意特征零原域的条件性下降，允许无限代数扩张且不预设 Galois 稳定性。
最后仍需将任意模块坐标运输与同一商的 A2 几何不稳定假设接通，得到原域单位负滤过；A8 保持未完成。
完整一般表示理论、双向实权重 HM 判据及不变量环有限生成不属于当前验收。

**书中出处。** 定理 5.2.7（Hilbert–Mumford 判据），注记 5.2.9，
推论 5.2.10，pp.305–309。

**在主证明中的角色。** 论文没有单独调用编号 5.2.10；它是 p.31 实际调用的
定理 5.4.3 从几何不稳定性得到负数值滤过的书中依据，也是 A2 与 A9 的接口。
因此属于主证明引用链上的输入，而不是论文的独立新结论。

**原书完整形式。** 对特征零域上的非零有限维因子和非零商 `q : ⊗ E_j ↠ Q`，
书中相应行列式点半稳定，当且仅当对任意实滤过 `F_j`，

$$
 e((\bigotimes_j F_j)_Q)\ \ge\ \sum_j e(F_j).
$$

这里所有 `e` 来自**平凡赋值下的滤过范数**，不是原 adelic bundle 的算术斜率。
书中假设域 perfect，论文的特征零条件足以满足它。

**保留的验收范围。** 不能只由斜率游戏、HN 理论或实滤过范数转换宣称这个 GIT 数值判据已证。
主证明只要求二元 `SL(E) × SL(F)` 的具体张量行列式表示；利用 A2–A5 连接整数权重的一参数子群、
行列式权重和商期望。整数或有理权重初始负候选已足够，不必另证一般实权重的双向数值判据。
主证明需要的是不稳定方向：得到一组滤过，使上述不等式严格反向；将各因子权重中心化后仍为负。
完整双向等价可以一并实现，但不把未使用的方向另列为主证明要求。
实现时可以把本项作为 A9 的内部引理，不强制公开一个全概形版本的 Hilbert–Mumford 定理。

### A9. 几何不稳定商的最优归一化滤过

- [ ] 形式化定理 5.4.3 在论文使用范围内的“负的全局最小值取到”结论。

**部分进展（2026-11-11）。** 已检查跨所有实际基支集的条件性有限族全局极小值与唯一性、
二元直接优化器、实际 HN 提升变分下界，以及 `80769f9` 的严格秩和下降／同组数据算术组合。
后两项的 4 个传递公理根与独立数学、消费者、诚实性审查通过；完整 CM (5.13) 由所需单侧 HN 方向替代。
最终必须实际调用 A8 原域输出并公开同一商的几何不稳定→全局最优消费者，故本项尚不勾选。
算术组合保留真实的小秩 HN 归纳条件，不把该条件或 Bost 主定理称为已证。

**书中出处。** 定理 5.4.3，pp.314–316。

**论文实际使用。** §7.3，p.31：若 `q : E ⊗ F ↠ Q` 几何不半稳定，取期望为零、
不同时平凡的 `P_E,P_F`，全局极小化

$$
 \Theta(T_E,T_F)=
 \frac{e((T_E\otimes T_F)_Q)}
 {\sqrt{\|T_E\|^2+\|T_F\|^2}}.
$$

其分母 `L` 严格正，最小值 `c` 严格负。pp.31–32 的变分论证使用的是这个真正的全局极小性。

**初始审计覆盖及缺口。**
[Order/HarderNarasimhan/Slope.lean](ArakelovGeometry/Order/HarderNarasimhan/Slope.lean) 和
[HN/Game/Payoff.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Game/Payoff.lean)
处理子模格上的度数/斜率 payoff 与 HN 旗。
它们没有群作用、Plücker 半稳定性、归一化滤过空间及 `Θ` 的最小化。
接入了 HarderNarasimhan 库不意味着已经覆盖此处的最优不稳定滤过定理。

**验收内容。** 以 A2 的真实几何不稳定性为输入，返回满足归一化、非平凡性、负值和
对所有允许滤过对的极小性条件的滤过。不能只给一个负值滤过、下确界、近似极小序列，
也不能把极小值取到作为额外假设。A8 给负值候选，A3–A5 给优化对象及数值函数。
书中引理 5.4.2 的有限维最小化论证可作实现依据，但它不是论文额外直接引用的一项输入。

原定理还给出对所有比较滤过的更强不等式 (5.13)。论文没有将 (5.13) 作为黑箱，
而是自行证明引理 7.2 的单侧变分比较；因此完整 (5.13) 不列为本次主证明必须覆盖的另一项。
公开的最优唯一性也不属于本项验收；若 A8 的有理下降采用唯一性，则保留必要的内部中点引理。
优化须跨所有实际基的可实现行列式支集，不能只在一组固定基中取极小值。
实际 HN 斜率和右变分方向通常为实数，故 A4–A7、A9 继续支持实权重。

### 实施顺序与边界

A1 可独立补齐。A3 是 A4 的基础；A4、A5 支持 A7–A9；A5 的代数比较必须先于 A6 的范数比较。
A2 与 A8 负责把论文的几何条件送入 A9。A6、A7 再与已有 HN/度数理论一起支持论文 §7 的自证引理。

优先检查当前 mathlib 的线性代数、商、外幂、范数和表示论设施；已有对象能表达时直接复用。
是否新增统一的滤过结构是实现设计选择，不另计缺口。不得把“place 空间的 σ-代数离散”“数域”或
“非平凡赋值”加入只需要可数特征零域的主证明；尤其要保留平凡赋值的情形。

## B. 主证明已经覆盖的 CM 输入

以下为已核对的引用对应表，不是待办。部分论文形式需要短的组合推论；列出的实际定理已提供其数学内容。

### B1. 曲线、范数族及 adelic 条件

| 论文使用位置；书中出处 | 当前代码依据及结论 |
| --- | --- |
| §2.1，pp.3–4；§3.1、命题 3.1.1–3.1.2 | [AdelicCurve/Defs.lean](ArakelovGeometry/AdelicCurve/Defs.lean) 的 `AdelicStructure`、`IsProper`；[Basic.lean](ArakelovGeometry/AdelicCurve/Basic.lean) 的 `measurableSet_Ωinf`、`integrable_κ`；[NormFamily/Basis.lean](ArakelovGeometry/AdelicVectorBundle/NormFamily/Basis.lean) 的 `v_Ωinf_lt_top_of_isRCLike` 给有限的 `m∞`。 |
| §2.2，p.4；定义 4.1.1、4.1.2、4.1.28 | [NormFamily/Basic.lean](ArakelovGeometry/AdelicVectorBundle/NormFamily/Basic.lean)、[Domination/Basic.lean](ArakelovGeometry/AdelicVectorBundle/NormFamily/Domination/Basic.lean)、[bundle Basic.lean](ArakelovGeometry/AdelicVectorBundle/Basic.lean) 已有范数族、原/对偶控制性、`IsAdelic`、`AdelicVectorBundle`；[Hermitian/Basic.lean](ArakelovGeometry/AdelicVectorBundle/NormFamily/Hermitian/Basic.lean) 的 `IsHermitian` 含真实内积范数与有限位超度量条件。 |
| p.4 式 (6)，p.25 常数辅助束的控制性；推论 4.1.10、注记 4.1.12 | [BasisComparison.lean](ArakelovGeometry/AdelicVectorBundle/NormFamily/BasisComparison.lean) 的 `isStronglyDominated_iff_localDist_ofBasisMixed` 及全称/存在基版本；[Strong.lean](ArakelovGeometry/AdelicVectorBundle/NormFamily/Domination/Strong.lean) 的 `isStronglyDominated_iff_isDominated_of_ultrametric`；[Hermitian/Basis.lean](ArakelovGeometry/AdelicVectorBundle/NormFamily/Hermitian/Basis.lean) 的 `ofBasisHermitian_localDist_hasIntegrableBounds` 把无穷位 ℓ² 参考基与已有参考基比较。结合距离三角不等式即可得到论文的版本。 |
| p.4 距离/对偶可测；命题 4.1.24 及 §4.1.3 | [Measurability/Countable.lean](ArakelovGeometry/AdelicVectorBundle/Measurability/Countable.lean) 的 `IsMeasurable.dual_of_countable_dense_subfield`、对应 `localDist` 定理及共同稠密子域版本，已处理真实完备纤维的上确界。 |

### B2. 运算与局部范数

| 论文使用位置；书中出处 | 当前代码依据及结论 |
| --- | --- |
| 命题 2.3，p.5；命题 4.1.19、4.1.24、4.1.32、注记 4.1.34 | [Construction/Countable.lean](ArakelovGeometry/AdelicVectorBundle/Construction/Countable.lean) 的 `restrictOfMeasurableBase`、`quotientOfMeasurableBase`、`dualOfMeasurableBase`；[Construction/Tensor/Countable.lean](ArakelovGeometry/AdelicVectorBundle/Construction/Tensor/Countable.lean) 的 `orthogonalTensorOfMeasurableBase`。已有控制性、可测性和 Hermitian 性的保持。 |
| p.5 行列式范数；§1.1.13 | [Determinant/Basic.lean](ArakelovGeometry/AdelicVectorBundle/Determinant/Basic.lean) 的 `determinant`、`determinant_norm_eq_sInf_ιMulti`；[HermitianBasis.lean](ArakelovGeometry/AdelicVectorBundle/Determinant/HermitianBasis.lean) 的 `IsHermitian.determinant_norm_orthonormalBasis`。任意 Gram 行列式公式可从正交基及换基公式组合得到。 |
| p.5 子空间/商对偶等距；命题 1.1.20、§1.2.3 | [Dual/Restriction.lean](ArakelovGeometry/AdelicVectorBundle/Dual/Restriction.lean) 的 `quotient_dual_annihilator_norm_eq`、`dual_quotient_annihilator_norm_eq` 及对应 completed isometry。它们不等于 A1 的张量对偶等距。 |
| 引理 6.1，p.25，近正交基及行列式下界；§1.2.3、命题 1.2.7、1.2.23 | [Analysis/Determinant/Basic.lean](ArakelovGeometry/Analysis/Determinant/Basic.lean) 的 `exists_basis_mul_dual_norm_le`、`exists_finBasis_mul_dual_norm_le` 在一般完备 `NormedField` 上成立，包含平凡赋值。对偶坐标估计给 α-正交下界，超度量三角不等式给上界；结合 [Pairing.lean](ArakelovGeometry/Analysis/Determinant/Pairing.lean) 的 `norm_det_le_prod_of_entry_le` 和行列式 infimum 公式，得到 `‖b₁∧⋯∧b_a‖ ≥ α^a ∏‖b_i‖`。 |

### B3. 度数、斜率及 HN

| 论文使用位置；书中出处 | 当前代码依据及结论 |
| --- | --- |
| pp.5–6，直线及一般 degree；§4.3 | [Degree/Line.lean](ArakelovGeometry/AdelicVectorBundle/Degree/Line.lean) 的 `lineDegree_eq_neg_integral`；[Degree/Basic.lean](ArakelovGeometry/AdelicVectorBundle/Degree/Basic.lean) 的 `degree_eq_neg_integral`。生成元无关性使用实际 product formula。 |
| p.6 式 (7)；命题 4.3.10，(4.25) | [Degree/Dual.lean](ArakelovGeometry/AdelicVectorBundle/Degree/Dual.lean) 的 `degree_dualOfMeasurableBase`，给 Hermitian 对偶度数精确变号。 |
| p.6 式 (8)–(9)，p.26 式 (39)；命题 4.3.19，(4.35) | [Degree/TensorHermitian.lean](ArakelovGeometry/AdelicVectorBundle/Degree/TensorHermitian.lean) 的 `degree_orthogonalTensorPair`；[Slope/Tensor.lean](ArakelovGeometry/AdelicVectorBundle/Slope/Tensor.lean) 的 `slope_orthogonalTensorPair`。是实际正交张量的等式，不能换用一般 mixed 张量的不等式。 |
| p.6 式 (10)，§7 的子商度数求和；命题 4.3.13，(4.29) | [Degree/ExactSequence/Dual.lean](ArakelovGeometry/AdelicVectorBundle/Degree/ExactSequence/Dual.lean) 的 `degree_restrict_add_degree_quotient_eq_of_isHermitian`；[Degree/Flag/Hermitian.lean](ArakelovGeometry/AdelicVectorBundle/Degree/Flag/Hermitian.lean) 的 `sum_flagQuotient_degree_eq_of_isHermitian`。 |
| p.6 式 (11)，p.27 压缩后的像斜率比较；命题 4.3.18，(4.32) | [Degree/Supermodular.lean](ArakelovGeometry/AdelicVectorBundle/Degree/Supermodular.lean) 的 `degree_le_of_completed_contraction`、`mapHeight_le_zero_of_completed_contraction`；限制到像后应用，保留实际诱导范数。 |
| p.6 极端斜率有限且取到；命题 4.3.28、推论 4.3.27 | [Slope/Finite.lean](ArakelovGeometry/AdelicVectorBundle/Slope/Finite.lean) 的 `exists_maximalSlope_eq_coe`、`exists_minimalSlope_eq_coe`；[Destabilizing.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Destabilizing.lean) 的 `exists_unique_largest_maximalSlope_subspace`；最小斜率由最后一个 HN 商取到。 |
| p.6 半稳定的商判据、对偶形式 (12) | [Hermitian/Semistability.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Hermitian/Semistability.lean) 的 `isMeanSlopeSemistable_iff_slope_le_quotient_of_isHermitian` 及对偶半稳定性；[Slope/DualUpper.lean](ArakelovGeometry/AdelicVectorBundle/Slope/DualUpper.lean) 的 `minimalSlope_dual_add_maximalSlope_eq_zero_of_isHermitian`。 |
| pp.6–7 映射高度及命题 2.4；命题 4.3.16、4.3.31(1)–(3) | [Operator/Measurable.lean](ArakelovGeometry/AdelicVectorBundle/Operator/Measurable.lean)、[StrongHeight.lean](ArakelovGeometry/AdelicVectorBundle/Operator/StrongHeight.lean) 给实际算子范数可测和非零映射高度可积；[Slope/LinearMap.lean](ArakelovGeometry/AdelicVectorBundle/Slope/LinearMap.lean)、[LinearMapFinite.lean](ArakelovGeometry/AdelicVectorBundle/Slope/LinearMapFinite.lean) 给非零、单射、满射的斜率比较。 |
| p.7 HN 存在、唯一、首末斜率和度数分解；§4.3.10、命题 4.3.37、4.3.38、4.3.41 | [Hermitian/Basic.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Hermitian/Basic.lean) 的 `hermitianHNFlag`、半稳定因子和严格下降斜率；[Uniqueness.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Hermitian/Uniqueness.lean) 的 `semistableFlag_eq_hermitianHNTerm`、`hermitianHNFiltration_unique`；[Dual.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Hermitian/Dual.lean) 的 `slope_hermitianHNFactor_last_eq_minimalSlope`；[Degree.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Hermitian/Degree.lean) 的加权度数和。 |
| p.7 HN 函子性，p.8 群等距作用保持 HN；命题 4.3.49 | [Hermitian/Functoriality.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Hermitian/Functoriality.lean) 的 `map_hermitianHNFiltration_le` 采用真实映射高度；双向应用得到等距不变性。 |
| pp.29–30 同斜率正交直和的半稳定性；命题 4.3.32 | [Slope/Extension.lean](ArakelovGeometry/AdelicVectorBundle/Slope/Extension.lean) 的 `minimalSlope_extension_lowerBound` 给命题对应的含实际 height/cokernel 的下界；结合 [DirectSum/Basic.lean](ArakelovGeometry/AdelicVectorBundle/DirectSum/Basic.lean) 的实际等距嵌入、商投影和度数加性，有限迭代即可得到论文使用形式。 |

### B4. 假设和现有滤过理论的核对

- 论文的可数 `K` 满足现有接口的
  `DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield`：可取共同子域为 `⊤`。
  [Density/Basic.lean](ArakelovGeometry/AdelicVectorBundle/Measurability/Density/Basic.lean)
  定义该条件；[CompletedUnitBall.lean](ArakelovGeometry/NumberTheory/NumberField/Local/Lattice/CompletedUnitBall.lean)
  中的 `isDenseSubfieldAt_top` 只有一般域假设，虽位于数域目录也不要求数域。
- 论文的无穷位通常实/复绝对值对应代码的 `hN`；Hermitian 条件提供有限位超度量性。
  `[S.IsProper]` 提供乘积公式。以上不会额外限制到离散 place 空间或局部紧域。
- 有限斜率和非零映射高度已有有限性证明；使用 `EReal` 表示再取 `.toReal` 本身不是强度缺失。
- §5.1 的有限实滤过基础、平凡位范数对应和单个适配基已经有相当覆盖，见 A3。
  [Filtration/HN.lean](ArakelovGeometry/AdelicVectorBundle/Examples/Trivial/Filtration/HN.lean)
  的 `generalHNFiltration_eq_trivialFiltration`、`generalHNFiltration_ofTrivialFiltration`
  还给出实际 HN 滤过与原滤过的一致性。缺口在共同基、配对和运算兼容性，不是整个 §5.1。

## C. 仅作比较、策略说明或其他提及的 CM 内容

### C1. 尚未覆盖的比较性结论：不列为主证明必需任务

- [ ] **命题 5.3.1，(5.7)，pp.310–311。** 几何半稳定商的 mixed 张量商斜率下界
  `μ(Q) ≥ Σ μ(E_j) − m∞ Σ log(dim E_j)`。
  论文在 pp.3、24 与它比较；当前分支没有带这一 GIT 前提的该结论。
  论文 §6 自行建立新的辅助束估计，并没有用 (5.7) 推出零误差结论。
- [ ] **注记 5.3.2，(5.9)，p.311。** Hermitian 正交张量的相应下界将上述误差系数改为 `1/2`。
  论文在 pp.3、24、28 提及；当前未覆盖。
  p.28 的 (43) 是论文从定理 6.2 对偶推出的零误差版本，不能把原书 (5.9) 当作那一步的前提。
- [ ] **定理 5.6.1，(5.15)–(5.16)，p.320。** 一般商的实际算术斜率不小于张量 HN
  滤过的商期望减去对数秩误差；mixed 系数为 `1`，Hermitian 系数为 `1/2`。
  论文 pp.3、28 引用其秩归纳策略，随后写出自己的归纳与变分论证；当前分支尚无原书完整结论。
  此处缺失不能与 A9 混同：定理 5.4.3 确实作为黑箱输入使用，而定理 5.6.1 的含误差结论没有。

这些条目供以后补全书籍覆盖时使用。复现 `bost.pdf` 的这条主证明路径，不必先证明它们。

### C2. 其他背景与特例：已有基础及表述差异

| 论文位置；CM 内容 | 覆盖状态与处理 |
| --- | --- |
| p.4，§3.1 的正特征无无穷位旁述 | 主定理假设特征零，因此不属于主证明输入。已有 [AdelicCurve/Basic.lean](ArakelovGeometry/AdelicCurve/Basic.lean) 的全有限位及零无穷位质量接口；不为这句旁述增加主证明待办。 |
| pp.8–9，命题 1.2.21 的 `Q_p/Z_p` 格范数、基坐标最大值及单位球 | [CompletedGauge.lean](ArakelovGeometry/NumberTheory/NumberField/Local/Lattice/CompletedGauge.lean) 的 `scalarLatticeGauge_basisCoordinateLattice`、`scalarLatticeGauge_basisCoordinateLattice_le_one_iff` 已覆盖实际 gauge 公式；其表述适用于一般相应赋值环。mathlib 的 `ℤ_[p]` DVR/PID 设施可直接复用。没有把缺少论文专用包装误记成此命题未证明。 |
| pp.2、8，数域归一化及通常格的度数解释 | [Model/GenericFibre/Projective.lean](ArakelovGeometry/NumberTheory/NumberField/Model/GenericFibre/Projective.lean) 已处理实际有限投射模、完备格范数及 `originalDiagonal_covolume_eq_exp_neg_degree`。但名为 `normalizedNumberFieldAdelicStructure` 的曲线按 `localDegree` 赋质量，`m∞=[K:Q]`；论文按 `localDegree/[K:Q]` 赋质量，`m∞=1`。应使用已有 `rationalAdelicStructure.algebraicExtension K`，或作测度归一化转换，不能直接把两个名称认作同一对象。 |

数域的正确归一化测度已经存在于
[ExtensionMeasure.lean](ArakelovGeometry/NumberTheory/NumberField/AdelicCurve/ExtensionMeasure.lean)；
[Height/Extension.lean](ArakelovGeometry/AdelicCurve/Height/Extension.lean) 的
`v_Ωinf_algebraicExtension` 给对应无穷位质量。
若以后专门导出论文的数域表述，可以补格 bundle 和度数的测度转换包装；这是特例接口工作，
不增加抽象主定理的 CM 依赖。`K=ℚ` 时归一化因子为 1。

## D. 不计入本清单的内容

以下用于划清来源，**不是新的待办项**：

- 参考文献 [3] 的 Specht 模、Schur–Weyl 对偶及相关附录内容；[5]、[6] 的 Gram 行列式、
  标准/半正规基结果；[4] 的 null cone、Kempf–Ness、capacity 理论；[1] 的替代归约。
  它们不属于本次指定的 CM 书 [2]。即使论文同时引用 [2] 和 [4]，也不把所有 GIT 旁述都归给 [2]。
- p.26 的“任意扩域下几何半稳定性不变”也是背景提及，所核对的 CM §5.2 没有单独陈述这样一个
  全基变换定理。p.27 直接在代数闭包上使用 `p,q`，并未将不变量下降到 `K`；
  `LinearMap.baseChange_zero` 已足以从扩域后的非零性反推 `Ψ_d ≠ 0`。
  因此 A2 不额外要求有理不变量下降或不变量环与任意基变换交换。
- 论文引理 2.6 的“有限群等距且不可约 ⇒ 算术半稳定”由论文借助 HN 唯一性证明。
  其中的 CM 输入已在 B3 核对；缺少同名有限群包装不构成一个新的 CM 定理缺口。
- 论文第 3–5 节的组合/概率论证、命题 5.3 的亚线性 Specht 余体积估计、
  引理 6.1 的具体 Specht bundle、定理 6.2 的零误差几何不等式，是论文自己的构造或结论。
  A1–A2 和 B 部分只登记它们实际用到的 CM 基础。
- 论文式 (45) 的 HN 商期望比较、引理 7.1、引理 7.2、最后的归纳，以及定理 1.1、
  推论 7.3 的零误差张量 HN 兼容性，不自动成为 CM 书中的结论。
  式 (45) 可利用已有 HN 函子性、半稳定旗子空间度数估计及精确度数加性，连接 A4–A5 后得到；
  引理 7.2 的非零 minors 最大值与单侧导数论证应按论文自己的引理处理。
- 当前 [Slope/Tensor.lean](ArakelovGeometry/AdelicVectorBundle/Slope/Tensor.lean)
  中 `maximalSlope_add_maximalSlope_le_maximalSlope_orthogonalTensorPair` 只是最大斜率等式的一侧。
  不能因此宣称论文主定理已覆盖，也不能把尚未覆盖的另一侧伪称为本书原有的零误差结论。

完成 A 部分只表示补齐本次识别的书籍依赖，仍须另行形式化论文自身的其余证明。
