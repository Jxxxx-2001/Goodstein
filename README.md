# 基于 Morse-Kelley 集合论的序数构建与 Goodstein 定理形式化证明

本仓库是论文《基于 Morse-Kelley 集合论的序数构建与 Goodstein 定理形式化证明》（投《软件学报》）的配套形式化代码。工程在定理证明器 Rocq（原 Coq）中，基于 Morse-Kelley（MK）公理化集合论形式化库，构建覆盖全体序数类的序数系统，并在其上完成 Goodstein 定理的机械化证明。

- 作者：吉祥，郁文生（北京邮电大学 电子工程学院；天地互联与融合北京市重点实验室）
- 通讯作者：郁文生，wsyu@bupt.edu.cn
- 平台：Rocq (Coq) 8.20
- 规模：9 个源文件、6291 行（统计口径含空行与注释行）
- 状态：全量编译通过，不含 `Axiom`、`Parameter`、`Hypothesis`、`Admitted`、`Abort`

## 主要结果

| 结果 | 形式化名称 | 位置 |
|---|---|---|
| 超限归纳原理 | `R_Transfinite_Induction` | [Induction.v](Induction.v) |
| 超限递归定理（序数类 / ω 上） | `Recursion_R.Recursion_R`、`Recursion_ω.Recursion_ω` | [Recursion.v](Recursion.v) |
| 序数加法、乘法、幂运算及其代数律 | `Add_R_Association`、`Mult_R_Distri`、`Exp_R_Distri` 等 | [R_Operation_Add.v](R_Operation_Add.v)、[R_Operation_Mult.v](R_Operation_Mult.v)、[R_Operation_Exp.v](R_Operation_Exp.v) |
| Cantor 范式存在性 | `CNF` | [Cantor_Normal_Form.v](Cantor_Normal_Form.v) |
| Cantor 范式唯一性 | `CNF_unique` | [Cantor_Normal_Form.v](Cantor_Normal_Form.v) |
| 基变换与序数解释的相容性 | `fn_Sn` | [Goodstein.v](Goodstein.v) |
| Goodstein 步的序数严格下降 | `goodstein_descent` | [Goodstein.v](Goodstein.v) |
| **Goodstein 定理** | `Goodstein` | [Goodstein.v](Goodstein.v) |

主定理的形式陈述：

```coq
Theorem Goodstein : ∀ m, m ∈ ω -> ∃ j, j ∈ ω /\ gval m j = Φ.
```

即：对任意自然数初值 `m`，其 Goodstein 序列存在某步 `j` 取值为零。序列由 `gd`（配对序列）、`gval`（数值分量）、`gbase`（基分量）定义，基变换算子为 `Sn`，序数解释函数为 `fn`。

## 环境准备

工程依赖 opam 包 `coq-morse-kelley-axiomatic-set-theory`（逻辑路径 `MorseKelley`，v1.0.0），该库是本团队前期工作，源码见 [1DGW/formalization-of-Morse-Kelley-axiomatic-set-theory](https://github.com/1DGW/formalization-of-Morse-Kelley-axiomatic-set-theory)。

```bash
# 1. 添加 Coq 官方 opam 仓库（若尚未添加）
opam repo add coq-released https://coq.inria.fr/opam/released

# 2. 安装 Rocq/Coq 8.20 与 MK 库
opam install coq.8.20.0 coq-morse-kelley-axiomatic-set-theory.1.0.0

# 3. 激活环境
eval $(opam env)
```

## 编译

`Makefile` 与 `Makefile.conf` 均由 `coq_makefile` 生成，未纳入版本控制，克隆后需先生成一次：

```bash
coq_makefile -f _CoqProject -o Makefile
make -j4
```

全量编译约需 20 秒（4 核并行）。单文件编译可用 `make Goodstein.vo`；依赖链是线性的，前驱文件会自动先编译。

验证证明不依赖额外公理：

```coq
Require Import OrdinalNum.Goodstein.
Print Assumptions Goodstein.
```

输出应仅含 MK 库自身的基础项 `Class`、`In`、`Classifier`、`MK_Axiom`（MK 的 8 条公理与分类公理图示）与经典逻辑 `classic`，工程本身不引入任何新公理。

交互式证明推荐在 VS Code 中配合 VsRocq 扩展进行。

## 文件结构

各文件以 `Require Export` 相连，下游可直接使用上游全部结论。依赖关系几乎是一条线性链，仅 `Induction.v` 与 `Recursion.v` 互不依赖、各自只依赖 `Ordinal_Number.v`，到 `R_Operation_Add.v` 汇合——这反映了超限归纳与超限递归在数学上的相互独立。

```
Ordinal_Number.v          236 行   序数定义、三分律、后继/极限二分、ω 的位置、上确界
  ├── Induction.v          75 行   超限归纳原理（三种形态）与 ω 上归纳
  └── Recursion.v         419 行   超限递归定理，Recursion_R / Recursion_ω 两个模块
        └── R_Operation_Add.v     814 行   序数加法：递归方程、单调性、结合律、减法
              └── R_Operation_Mult.v    885 行   序数乘法：分配律、结合律、单调性
                    └── R_Operation_Exp.v     703 行   序数幂运算：指数律、单调性
                          └── Sum_Function.v        342 行   有限求和算子 Sum
                                └── Cantor_Normal_Form.v   1146 行   CNF 存在性与唯一性
                                      └── Goodstein.v            1671 行   Goodstein 定理
```

与论文章节的对应：

| 论文章节 | 源文件 |
|---|---|
| 第 3 章 序数理论与序数运算 | `Ordinal_Number.v` — `Sum_Function.v`（7 个文件） |
| 第 4 章 Cantor 范式 | `Cantor_Normal_Form.v` |
| 第 5 章 Goodstein 定理 | `Goodstein.v` |

其余文件：

- [_CoqProject](_CoqProject)：逻辑路径声明（本工程为 `OrdinalNum`）与源文件清单
- [LICENSE](LICENSE)：LGPL-2.1 许可全文
- [Cantor_Normal_Form_说明.md](Cantor_Normal_Form_说明.md)、[Goodstein_说明.md](Goodstein_说明.md)：逐条陈述定义、引理与证明思路的说明文档
- [doc/Goodstein实现计划.md](doc/Goodstein实现计划.md)：分阶段实现计划
- [doc/集合论-古德斯坦.pdf](doc/集合论-古德斯坦.pdf)：证明的纸面推演稿

## 记号约定

沿用 MK 库的记号，一切数学对象均为 `Class`（类），`Ensemble x` 表示 `x` 是集合：

| 记号 | 含义 |
|---|---|
| `Φ` / `μ` | 空集 / 全类 |
| `R` | 全体序数之类（真类） |
| `ω` | 自然数之类，即全体有限序数 |
| `Ordinal_Number x` | `x ∈ R`，即 `x` 是序数 |
| `a ≺ b` / `a ≼ b` | 序数的严格小于 / 小于等于 |
| `PlusOne a` | 后继序数 `a ∪ {a}` |
| `Suc_Ord a` / `Lim_Ord a` | 后继序数 / 极限序数 |
| `a + b`、`a ⋅ b`、`a ^ b` | 序数加法、乘法、幂运算 |
| `dom(F)` / `ran(F)` / `F[x]` | 定义域 / 值域 / 取值 |
| `F \| (u)` | `F` 在 `u` 上的限制 |
| `\{ λ x, P x \}` / `\{\ λ u v, P u v \}\` | 类的概括 / 有序对形式的概括 |
| `OnTo F A B` | `F` 是从 `A` 到 `B` 的类函数 |

三个序数运算统一用超限递归的"三函数模式"定义：`G1`（零情形初值）、`G2`（后继情形构造）、`G3`（极限情形取上确界），代入 `Recursion_R` 得到唯一的类函数。

## 范围与可信基础

明确本工程做了什么、没做什么：

- 本工程形式化的是 **Goodstein 序列的终止性**，**未**形式化该定理相对皮亚诺算术（PA）的不可证明性（Kirby–Paris 独立性结果）。
- 本工程**未**重新形式化 MK 公理系统，直接导入 `MorseKelley.mk_theorems`。可信基础由 Rocq 内核与该 MK 库两部分构成。
- 证明不构造 \(\varepsilon_0\)。下降论证只依赖序数类的良基性，不依赖该上界。
- Goodstein 定理在 Isabelle/HOL（AFP 条目 `Nested_Multisets_Ordinals` 中的 `Goodstein_Sequence.thy`）与 Lean 中已有完整的机械化证明。本工程的差异在于：序数对象是公理化集合论中按 von Neumann 定义真正构造的对象而非语法记号或商类型编码；Cantor 范式作为定理被证明而非取作类型定义；序数运算经超限递归定义在全体序数类上，含一般幂运算 \(x^y\)。据此，本工程给出的是该定理**首个在集合论序数上的机械化证明**。

## 许可

本工程以 GNU LGPL-2.1 许可发布，与其所依赖的 MK 集合论形式化库保持一致，详见 [LICENSE](LICENSE)。

## 引用

```bibtex
@article{ji2026goodstein,
  author  = {吉祥 and 郁文生},
  title   = {基于 Morse-Kelley 集合论的序数构建与 Goodstein 定理形式化证明},
  journal = {软件学报},
  year    = {2026},
  note    = {审稿中}
}
```
