# `apply` 战术机制笔记

> 证据来源：`.lean_agent/evidence.md`（Lean 4.33.0 + Mathlib 的源码级验证报告，含 §9、§11 补充验证）。
> 全部结论有源码行号与 `lake env lean` 实跑输出支撑。可复现脚本：
> `MVE_apply_behavior_check.lean`、`MVE_apply_le_trans_goals.lean`、`MVE_apply_inside_out.lean`、
> `MVE_apply_open_questions.lean`、`MVE_lt_of_le_of_lt_tags.lean`
> （五份均 EXIT=0，其中 `#guard_msgs` 钉死了所有错误信息与目标标签）。

## TL;DR：八条核心结论

1. `apply e` 的全部行为 = 内核函数 `Lean.MVarId.apply`：拿 `e` 的**结论类型**和**目标类型**做合一；
   成功就把目标填成 `e ?1 ?2 …`，剩下**没被赋值的空位**变成新目标。
2. 空位来自 `e` 的 Pi 绑定——既有前提（显式参数），也有隐式参数（类型、实例、中间项）。
   所以 `apply le_trans` 在目标 `x ≤ z` 上是 **3 个目标，不是 2 个**。
3. 新目标的顺序由 `ApplyConfig.newGoals` 决定，默认 `nonDependentFirst`：
   被其他目标"用到"的空位（如中间项 `?b`）永远排在最后。
4. `apply` 的合一**只比较类型**，从不搜索你的局部假设。
5. 任何一步给某个空位赋了值，它对应的目标就**自动消失**
   （这解释了 MIL 书里 `apply le_trans; · apply h₀; · apply h₁` 为什么只写 2 个 bullet）。
6. `refine` 与 `apply` 对定不住的隐式参数处理相反：`refine` **当场合成、失败即报错**；
   `apply` 把它**留成一个目标**慢慢还。（已实测，见 §4）
7. `exact e` 缺信息会卡死类型类合成；`apply e` 推迟实例合成，因此更宽容。（已实测，见 §1.6）
8. `apply t at h`（前向推理）是 **Mathlib** 的独立战术，和核心 `apply` 是两回事。

## 1. 机制解释

### 1.1 apply 不是魔法：三层结构

```
apply e        -- 用户语法    Init/Tactics.lean:232（只有 "apply " term，无 location）
  └─ evalApply -- 战术壳      Elab/Tactic/ElabTerm.lean:300-303
       └─ Lean.MVarId.apply  -- 全部逻辑   Meta/Tactic/Apply.lean:169
```

一个容易忽略的细节：`apply` 用 `elabTermForApply`（ElabTerm.lean:263）解析 `e`——
对标识符只解析成**裸常量**（`∀` 保留着），不提前补隐式参数。这保证了实例参数能
在后面被正常合成（也是它比 `exact` 宽容的技术根源之一）。

### 1.2 四步心智模型（行号均指 Apply.lean）

以 `@le_trans : ∀ {α} [Preorder α] {a b c : α}, a ≤ b → b ≤ c → a ≤ c`、目标 `x ≤ z` 为例：

| 步骤 | 源码 | 做什么 | le_trans 例子中发生什么 |
|---|---|---|---|
| 1. 开空位 | `:205` `forallMetaTelescopeReducing` | 给 e 的 Pi 绑定各造一个元变量；前提也是 Pi 绑定，所以也有空位 | 造出 `?α ?inst ?a ?b ?c ?h₁ ?h₂` |
| 2. 合一 | `:206` `isDefEqApply` | 比较"剥掉绑定后的结论类型"与目标类型 | `?a ≤ ?c =?= x ≤ z` → `?a := x, ?c := z`；`?b` 定不住 |
| 3. 填目标 | `:223` `mvarId.assign (mkAppN e newMVars)` | 目标被直接赋值成 `e ?1 ?2 …`，主目标关闭 | 目标变成 `le_trans ?h₁ ?h₂` |
| 4. 收尾 | `:224` + `:227` | 未赋值的空位 → 新目标，再按 `cfg.newGoals` 排序 | 未赋值：`?b ?h₁ ?h₂` → 3 个目标 |

对 `lt_of_le_of_lt` 直接打印第 1、2 步（`MVE_apply_inside_out.lean` 实跑）：

```
第 1 步：给 `lt_of_le_of_lt` 的参数开了 7 个空位：[?α, ?inst✝, ?a, ?b, ?c, ?hab, ?hbc]
  此时引理的结论类型是：?a < ?c
第 2 步：把它和当前目标 a < e 合一 = true
  空位 ?a := a，?c := e；?b 没有任何信息能定出它
```

> **进阶：源码里的真实结构（比四步模型多四件事）**
> 四步是典型情形的简化模型。`MVarId.apply`（`Apply.lean:169-231`）实际还有：
> - `:175` `getExpectedNumArgsAux` + `:202-220` 的 `go` 循环：**试探不同的下划线数量**，
>   取第一个能让"结论 vs 目标"合一的方案。所以"给所有 Pi 绑定开空位"是
>   循环选出的**典型结果**，不是字面保证（`le_trans` 例中最终是全部 7 个）。
> - `:221` `postprocessAppMVars`：填目标**之前**先合成已赋值的实例参数。
> - `:225` `appendParentTag`（定义在 `:108`）：用 binder 用户名生成 `case` 标签（见 1.3）。
> - `:226-230`：结果还会拼上"原始项 `e` 自身携带的 mvar"（服务于 `apply foo ?_`
>   这类带用户空位的写法；对裸常量 `e`，这一项通常为空）。

### 1.3 为什么 `apply le_trans` 是 3 个目标

`trace_state` 实跑输出：

```
case a
⊢ x ≤ ?b        ← le_trans 第 1 条前提
case a
⊢ ?b ≤ z        ← 第 2 条前提
case b
⊢ ℝ             ← 隐式参数 {b : α} 自己！
```

目标 `x ≤ z` 只能定住 `?a := x`、`?c := z`；中间项 `?b` 在目标里没有任何信息能定出它，
于是它作为"还没赋值的 mvar"也变成一个目标。所以下面这种写法会报错：

```lean
apply le_trans
· sorry
· sorry          -- error: unsolved goals  case b  ⊢ ℝ
```

这个"躲在目标列表末尾的第 3 个目标"就是 `apply le_trans` 最常见的坑。

**标签规律（已验证）**：`case` 标签由 `appendParentTag`（Apply.lean:108）依据 binder
的**用户名**生成。`{b}` 有名字 → `case b`；两条无名前提箭头被默认取名，实测**都是
`case a`**。所以别用标签区分两个前提目标——它们同名！用 bullet 顺序（或 `next`）。
对照 `lt_of_le_of_lt`：前提 binder **有名字**（`hab`、`hbc`），实测三个标签依次为
`case hab`、`case hbc`、`case b`（见 §3，`MVE_lt_of_le_of_lt_tags.lean` 已钉死）——
标签规则在这两个引理上互相印证。

### 1.4 目标排序：nonDependentFirst

- 配置定义：`Init/Meta/Defs.lean:1702-1708`，默认 `newGoals := .nonDependentFirst`
- 排序实现：`Apply.lean:150-157`；"被依赖"的判定（`:132` `dependsOnOthers`）：
  某 mvar 出现在**其他** mvar 的类型里。

三种配置在同一目标上的实测结果（直接调 `MVarId.apply`，`MVE_apply_behavior_check.lean`）：

```
nonDependentFirst(默认) : (1) x ≤ ?b   (2) ?b ≤ z   (3) ℝ
nonDependentOnly        : (1) x ≤ ?b   (2) ?b ≤ z              （?b 被丢出目标列表）
all                     : (1) ℝ  (2) x ≤ ?b  (3) ?b ≤ z       （保持 mvar 创建顺序）
```

`?b` 出现在 `x ≤ ?b` 和 `?b ≤ z` 里，属于"被依赖"，所以默认被排到最后。

> **meta API 警告（已有 meta 级实证）**：`nonDependentOnly` 会把 `?b` 丢出目标列表
> 但**不赋值**。实测：关闭返回的 2 个目标后，证明项里仍有 1 个未赋值空位；
> 若让它成为真实声明，内核报：
> ```
> error: (kernel) declaration has metavariables '_example'
> ```
> 核心战术不暴露此配置。（另一个验证技巧：这种**内核级**错误 `#guard_msgs` 抓不到——
> 它在消息收集之后才产生，得用 meta 层计数之类的手段钉证据。）

### 1.5 赋值即消灭：为什么书上的写法只要 2 个 bullet

`exact h₀` 关闭 `x ≤ ?b` 时，合一顺带判定 `?b := y`。`?b` 一旦有值，
它自己的目标 `⊢ ℝ` 立即消失：

```lean
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀    -- 关闭 x ≤ ?b，同时 ?b := y → ⊢ ℝ 目标自动消失
  · apply h₁
```

想一开始就不产生第 3 个目标，用命名参数把中间项钉死：

```lean
  apply le_trans (b := y)   -- 从此只剩 2 个目标
```

### 1.6 三条边界规则（同样源自第 2 步的合一）

- **只比类型，不看假设**：`isDefEq` 只比较"引理结论"和"目标类型"，不做
  `assumption` 式搜索。类型对不上当场报错，即使上下文里有其他假设（完整走查见 §3）：

  ```
  Tactic `apply` failed: could not unify the type of `h₁`
    b < c
  with the goal
    b < e
  ```

- **允许定义等价（whnf）**：目标 `MyLe a b`（`def MyLe a b := a ≤ b`）
  可以 `apply h`（`h : a ≤ b`）——合一前目标先归约。

- **实例合成被推迟**：`apply le_trans` 在 ℝ 上不需要手写 `Preorder ℝ`。
  对照裸 `exact le_trans` 的**完整真实报错**（4.33.0 原文，已钉死）：

  ```
  error: typeclass instance problem is stuck
    Preorder ?m.8

  Note: Lean will not try to resolve this typeclass instance problem because the type
  argument to `Preorder` is a metavariable. This argument must be fully determined
  before Lean will try to resolve the typeclass.
  ```

  `apply` 把"缺的信息"变成新目标，实例合成被推迟到信息齐全之后，所以不卡。

## 2. 最小示例

成功情形：

```lean
example (x : ℝ) : x ≤ x := by apply le_refl          -- 无前提 → 直接关闭
example (x y : ℝ) (h : x ≤ y) : x ≤ y := by apply h  -- 局部假设也能被 apply
example (f g : ℝ → ℝ) (h : ∀ x, f x ≤ g x) : ∀ x, f x ≤ g x := by
  apply h                                            -- ∀ 目标直接关闭
```

边界情形：

```lean
-- ① "看不见的第 3 个目标"坑
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · sorry
  · sorry          -- error: unsolved goals  case b  ⊢ ℝ

-- ② 类型不合一直接报错，不搜索其他假设（完整走查见 §3）
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt
  · exact h₀
  · apply h₁   -- error: could not unify the type of `h₁`（b < c）with the goal（b < e）

-- ③ refine 不会把定不住的隐式参数留成目标，而是当场报错（详见 §4）
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  refine le_trans ?_ ?_
-- error: don't know how to synthesize implicit argument `b`
--   @le_trans ℝ Real.instPreorder x ?m.11 z ?m.13 ?m.14

-- ④ 裸 exact 会卡在实例合成，apply 不会（完整报错见 1.6）
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  exact le_trans
-- error: typeclass instance problem is stuck  Preorder ?m.8
```

## 3. 回到教材：`a < e` 链式练习走查

MIL C02_Basics/S03 的 "Try this" 练习——也是本笔记多数报错证据的出处：

```lean
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt
  · apply h₀
```

**逐步走查**（目标列表与标签均已被 `MVE_apply_inside_out.lean`、
`MVE_lt_of_le_of_lt_tags.lean` 的 `#guard_msgs` 钉死）：

1. `apply lt_of_le_of_lt` 之后有 **3** 个目标：

   ```
   case hab   ⊢ a ≤ ?b     ← 第 1 条前提
   case hbc   ⊢ ?b < e     ← 第 2 条前提
   case b     ⊢ ℝ          ← 隐式中间项 {b} 自己，藏在最后
   ```

   与 `le_trans` 完全同理：目标 `a < e` 定得住 `?a := a`、`?c := e`，定不住 `?b`。

2. `apply h₀` 关闭 (1)：合一给出 `?b := b`，于是 (3) **自动消失**（§1.5 的机制），
   只剩 `b < e`。

3. 卡住的人十有八九在这里写 `apply h₁`——然后撞上 §1.6 第一条边界规则
   （这段报错被 `MVE_apply_behavior_check.lean` 钉死）：

   ```
   Tactic `apply` failed: could not unify the type of `h₁`
     b < c
   with the goal
     b < e

   case hbc
   a b c d e : ℝ
   h₀ : a ≤ b
   h₁ : b < c
   h₂ : c ≤ d
   h₃ : d < e
   ⊢ b < e
   ```

   注意两个细节：报错头是 `case hbc`（前提 binder 有名字，与 §1.3 标签规律一致）；
   报错里的目标是 `b < e` 而**不是** `?b < e`——这正是第 2 步里 `?b := b` 已经发生的
   直接证据。`apply` 只做类型合一、不搜索假设，`b < c` 对不上 `b < e`，它不会替你
   "想到"该把 h₁、h₂、h₃ 攒起来。

4. 正确的收尾：自己构造中间段——

```lean
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt
  · apply h₀                                    -- ?b := b，隐藏的第 3 个目标随之消失
  · exact lt_trans h₁ (lt_of_le_of_lt h₂ h₃)    -- 攒出 b < e
```

   （该解法已实测编译通过：`MVE_lt_of_le_of_lt_tags.lean`，EXIT=0。`apply h₀` 与
   `MVE_apply_inside_out.lean` 用的 `exact h₀` 走同一次合一，区别只在战术壳。）

## 4. 使用建议与对比

| 场景 | 建议 |
|---|---|
| 目标能被某引理的结论"罩住" | `apply 引理`，让前提变成待办清单 |
| 中间项定不住（如 le_trans） | `apply 引理 (b := y)` 钉死，或先 apply 一个能定住它的前提 |
| 中段类型对不上（如 `b < e` 要靠 h₁h₂h₃ 攒） | 先用引理把中段构造出来，再 `exact`/`apply`（见 §3） |
| 怀疑有看不见的目标 | `trace_state` 一次列出**全部**目标（包括末尾的隐式参数目标） |
| 想一次清空所有目标 | `all_goals sorry`（与逐个 bullet 等价，还能暴露隐藏目标） |
| 需要区分两个前提目标 | 别用 `case a` 标签（可能同名），用 bullet 顺序 |

**apply vs exact**：`exact e` 要求 `e` 完整给出证明，缺隐式信息时卡在类型类合成
（完整报错见 1.6）；`apply e` 把"缺的信息"变成新目标并推迟实例合成，因此更宽容。

**apply vs refine（已实测）**：两者都允许留洞，但对**定不住的隐式参数**态度相反——

```lean
-- refine：当场合成隐式参数 b，合成不出直接报错，不产生任何目标
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  refine le_trans ?_ ?_
-- error: don't know how to synthesize implicit argument `b` ...

-- 要用 refine 就得显式把 b 给出来
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  refine @le_trans ℝ _ x y z ?_ ?_
  · exact h₀
  · exact h₁

-- apply：把定不住的 ?b 留成第 3 个目标，"先欠着，后面还"
```

选型直觉：**结构已知、隐式可当场定** → `refine`（早失败，错误信息更准）；
**想让 Lean 先欠账、由后续前提慢慢还** → `apply`。

**apply vs apply at**：核心 `apply` 只有 `apply term` 一种语法；`apply t at i` 是
Mathlib 的前向推理战术（`Mathlib/Tactic/ApplyAt.lean:31`）。语义：`t : α₁ → … → αₙ`、
`i : αᵢ` 时，为 `α₁…α_{i-1}` 开目标，并把 `i` 的类型替换成 `α_{i+1} → … → αₙ`：

```lean
example (a b c : ℝ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  apply le_trans h at h'   -- h' : b ≤ c 变成 h' : a ≤ c，主目标不变
  exact h'
```

## 5. 常见报错速查表

| 报错关键词 | 根因 | 处方 |
|---|---|---|
| `unsolved goals case b ⊢ ℝ` | apply 留下的隐式参数目标没解决 | 补一条 bullet 给出该类型的项（如 `y`）；或命名参数 `(b := y)` 钉死；或先解决能定住它的前提（§1.3、§1.5） |
| `Tactic 'apply' failed: could not unify ...` | 假设类型与目标对不上；apply 不搜索假设 | 换类型匹配的假设，或先用其他引理把目标改写到位（§1.6、§3） |
| `don't know how to synthesize implicit argument 'b'`（refine 场景） | refine 当场合成隐式参数失败 | 改用 `apply`（把 `?b` 留成目标），或显式给参 `@le_trans ℝ _ x y z ?_ ?_`（§4） |
| `typeclass instance problem is stuck Preorder ?m`（exact 场景） | exact 必须当场定出实例 | 改用 `apply` 推迟合成，或手动给出实例（§1.6） |
| `(kernel) declaration has metavariables` | 证明项残留未赋值 mvar | 仅 meta API 的 `nonDependentOnly` 可触发，核心战术无此路（§1.4） |

## 6. 仍不确定的点

1. 源码行号绑定本工作区 vendored 的 Lean 4.33.0（commit d8b1897）；升级后行号可能漂移，
   但 `MVarId.apply` / `ApplyConfig` 的结构稳定。
2. `nonDependentOnly` 的"残留未赋值 mvar → declaration has metavariables"只在直接调用
   meta API 时可达，核心 `apply` 不暴露该配置。
3. `apply t at i` 依赖 Mathlib 的 `forallMetaTelescopeReducingUntilDefEq`，Mathlib
   版本更新可能微调其行为。
4. "两条无名前提都叫 `case a`"背后的 `forallMetaTelescope` 匿名 binder 命名规则
   未逐行追到底——标签**值**已实测，命名**规则**未溯源。
5. `exact le_trans` 的 Note 文案是版本相关字符串，以 4.33.0 原文为准。
6. **（已实测，本项已关闭）** `lt_of_le_of_lt` 三目标的标签为 `case hab` / `case hbc` / `case b`；
   教材式解法（第一条用 `apply h₀`）编译通过、EXIT=0。
   见 §3 与 `MVE_lt_of_le_of_lt_tags.lean`（evidence.md §11）。

## 附：复现命令

```bash
cd /workspaces/mathematics_in_lean
lake env lean MVE_apply_behavior_check.lean    # 三种 newGoals 配置 + 合一行为，EXIT=0
lake env lean MVE_apply_le_trans_goals.lean    # 3 目标 / 默认排序 / 命名参数，EXIT=0
lake env lean MVE_apply_inside_out.lean        # 拆解 MVarId.apply 第 1、2 步，EXIT=0
lake env lean MVE_apply_open_questions.lean    # refine 对比 / 残留空位 / exact 报错，EXIT=0
lake env lean MVE_lt_of_le_of_lt_tags.lean     # lt_of_le_of_lt 标签 + 教材式解法，EXIT=0
```
