# `apply` 战术行为验证报告

环境：Lean 4.33.0（commit d8b1897），Mathlib（`.lake/packages/mathlib`），工作区 `/workspaces/mathematics_in_lean`。

所有结论均由源码 + `lake env lean` 真实输出支撑。可复现文件：
`MVE_apply_behavior_check.lean`、`MVE_apply_le_trans_goals.lean`、`MVE_apply_inside_out.lean`、`MVE_apply_open_questions.lean`（最后一次为补充验证，EXIT=0）。

---

## 0. 结论速览

| # | 命题 | 判定 |
|---|------|------|
| 1 | 核心 `apply` 只是 `Lean.MVarId.apply` 的壳 | **成立** |
| 2 | `apply le_trans` 在目标 `x ≤ z` 上生成 **3** 个目标（不是 2） | **成立** |
| 3 | 目标顺序由 `ApplyConfig.newGoals` 决定，默认 `nonDependentFirst`（依赖 mvar 排最后） | **成立** |
| 4 | `apply` 用前提给 mvar 赋值后，隐式参数目标会自动消失 | **成立** |
| 5 | `apply e` 第 2 步只做类型合一，**不查看局部假设** | **成立** |
| 6 | `apply` 可对目标做定义等价（whnf）归约 | **成立** |
| 7 | `apply` 会合成类型类实例；裸 `exact le_trans` 会卡在 `Preorder ?m` | **成立** |
| 8 | `apply t at i` 是 **Mathlib** 独立战术，不是核心 `apply` | **成立** |
| 9 | `refine e ?_ …` 与 `apply e` 处理隐式空位的方式不同 | **成立** |
| 10 | `nonDependentOnly` 会丢弃未赋值空位；这正是内核 `declaration has metavariables` 的根因 | **成立** |
| 11 | 目标标签 `case a` / `case b` 来自 `appendParentTag` | **成立** |
| 12 | 源码"四步"是简化模型；`MVarId.apply` 还有下划线数量试探循环与后处理 | **成立（补充）** |

---

## 1. 核心 `apply` = `MVarId.apply` 的薄壳（成立）

关键源码：

- `src/lean/Init/Tactics.lean:232`：`syntax (name := apply) "apply " term : tactic`（核心只有 `apply $t`，无 location）
- `src/lean/Lean/Elab/Tactic/ElabTerm.lean:263`：`elabTermForApply`（标识符直接解析成裸常量，不提前插隐式参数）
- `src/lean/Lean/Elab/Tactic/ElabTerm.lean:280-303`：`evalApplyLikeTactic` / `evalApply`
  ```lean
  | `(tactic| apply $t) => evalApplyLikeTactic (fun g e => g.apply e (term? := some m!"`{e}`")) t
  ```
- `src/lean/Lean/Meta/Tactic/Apply.lean:169`：`Lean.MVarId.apply`

`MVarId.apply` 的四步（行号 `Apply.lean`）：

1. `:205` `forallMetaTelescopeReducing eType i` —— 给引理的 **所有** Pi 绑定开空位，含显式前提；
2. `:206` `isDefEqApply cfg.approx eType targetType` —— 引理结论与目标类型合一；
3. `:223` `mvarId.assign (mkAppN e newMVars)` —— 目标被填成 `e ?1 ?2 …`，主目标关闭；
4. `:224` `newMVars.filterM (not ∘ isAssigned)` + `:227` `reorderGoals newMVars cfg.newGoals` —— 未赋值的空位成为新目标并排序。

**源码复查修正（2026-09-25）**：上面四步是**典型情形的简化模型**。实际 `MVarId.apply`（`Apply.lean:169-231`）还包含：

- `:175` `getExpectedNumArgsAux eType` + `:202-220` 的 `go` 循环：**试探不同的下划线数量**，取第一个能让「结论类型 vs 目标类型」合一的方案；所以"给引理的所有 Pi 绑定开空位"并非字面永远成立，而是这个循环选出的结果（`le_trans` 例中最终是全部 7 个）。
- `:221` `postprocessAppMVars`：在填目标**之前**合成已赋值的实例参数。
- `:225` `appendParentTag mvarId newMVars binderInfos`：用 binder 用户名生成 `case` 标签（见 §11）。
- `:226-230` 结果 = 排序后的未赋值空位 `++` 出现在**原始项 `e` 自身**里、且未被包含的其它 mvar（用于 `apply foo ?_` 之类带用户空位的写法）。对裸常量 `e`，后者通常为空。

`elabTermForApply` 的效果（直接打印，`MVE_apply_inside_out.lean`）：

```
第 1 步：给 `lt_of_le_of_lt` 的参数开了 7 个空位：[?α, ?inst✝, ?a, ?b, ?c, ?hab, ?hbc]
  此时引理的结论类型是：?a < ?c
第 2 步：把它和当前目标 a < e 合一 = true
```

---

## 2. `apply le_trans` 生成 3 个目标（成立）

签名（真实输出）：

```
@le_trans : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b ≤ c → a ≤ c
```

实跑 `lake env lean MVE_apply_le_trans_goals.lean`（EXIT=0）中 `apply le_trans` 后 `trace_state`：

```
case a
x y z : ℝ
h₀ : x ≤ y
h₁ : y ≤ z
⊢ x ≤ ?b

case a
...
⊢ ?b ≤ z

case b
...
⊢ ℝ
```

原因：`?b` 是隐式参数，目标 `x ≤ z` 只能定住 `a := x, c := z`，定不住 `b`；`b` 未被赋值 → 变成第 3 个目标。因此 `apply le_trans; · sorry; · sorry` 会留下 `case b ⊢ ℝ` 未解决（该文件用 `#guard_msgs` 钉死了这条 `unsolved goals`）。

---

## 3. 目标顺序由 `ApplyConfig.newGoals` 决定（成立）

- `src/lean/Init/Meta/Defs.lean:1702`：`inductive ApplyNewGoals | nonDependentFirst | nonDependentOnly | all`
- `:1707-1708`：`structure ApplyConfig where newGoals := ApplyNewGoals.nonDependentFirst`
- `Apply.lean:150-157`：
  ```lean
  | .nonDependentFirst => (nonDeps ++ deps)
  | .nonDependentOnly  => nonDeps
  | .all               => mvars.map mvarId!   -- 原始创建顺序
  ```
  依赖判定：`dependsOnOthers` (`Apply.lean:132`)：`mvar` 出现在**别的** mvar 的类型里即为「被依赖」。

直接用 `MVarId.apply` 传不同 config，在同一定理上打印（`MVE_apply_behavior_check.lean`，EXIT=0，`#guard_msgs` 全部通过）：

```
config 0 (nonDependentFirst, 默认): 3 个新目标
  (1) x ≤ ?b
  (2) ?b ≤ z
  (3) ℝ
config 1 (nonDependentOnly): 2 个新目标
  (1) x ≤ ?b
  (2) ?b ≤ z
config 2 (all): 3 个新目标
  (1) ℝ
  (2) x ≤ ?b
  (3) ?b ≤ z
```

即：`?b` 出现在 `x ≤ ?b`、`?b ≤ z` 中，是「被依赖」的 mvar，所以默认排最后；`all` 则保持创建顺序，`?b` 反而第一。

**meta API 注意**：`nonDependentOnly` 会把 `?b` 从目标列表移除但不赋值；若两个前提目标被关闭时仍未给 `?b` 赋值，内核会报 `declaration has metavariables`（实验中用 `all_goals sorry` 观察到此现象）。核心 `apply` 战术用默认 config，不暴露此模式。

---

## 4. 赋值 mvar 会顺带消灭其目标（成立）

`apply le_trans` 后（config 0）三个目标为 `x ≤ ?b`、`?b ≤ z`、`ℝ`。执行 `exact h₀` 关闭第一个目标时会顺带判定 `?b := y`，于是 `?b` 自己的目标 `ℝ` 立即消失，只剩 1 个目标：

```lean
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply_print 0 le_trans
  · exact h₀   -- 关闭 `x ≤ ?b`，同时 `?b := y` → 第 3 个目标 `ℝ` 随之消失
  · exact h₁
```

对照：MIL 原书写法 `apply le_trans; · apply h₀; · apply h₁` 能通过，正是同一机制。命名参数 `apply le_trans (b := y)` 则在第一步就只剩 2 个目标。

---

## 5. `apply` 不查看局部假设，只做类型合一（成立）

在 `h₁ : b < c` 存在、目标为 `b < e` 时执行 `apply h₁`，真实错误（`MVE_apply_behavior_check.lean` 已用 `#guard_msgs` 钉死）：

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

`isDefEq` 只比较「引理结论」和「目标类型」，不做 `assumption` 式搜索——这就是 `apply h₁` 不看 `h₂/h₃` 的原因。

---

## 6. 其他已验证行为（均 EXIT=0）

- 目标与引理结论**定义等价**时可 apply：`def MyLe a b := a ≤ b`，`h : a ≤ b ⊢ MyLe a b`，`apply h` 成功（目标 whnf 归约后合一）。
- `apply` 可在 `∀` 目标下直接关闭：`h : ∀ x, f x ≤ g x ⊢ ∀ x, f x ≤ g x`，`apply h` 成功。
- `apply` 合成类型类实例：`apply le_trans` 在 `ℝ` 上无需手写 `Preorder ℝ`。
  对照裸应用 `exact le_trans` 的真实报错：
  ```
  error: typeclass instance problem is stuck
    Preorder ?m.8
  Note: Lean will not try to resolve this typeclass instance problem because the type
  argument to `Preorder` is a metavariable. ...
  ```
- 局部假设可作为被 apply 的项：`example (h : x ≤ y) : x ≤ y := by apply h` 成功。

---

## 7. `apply t at i` 属于 Mathlib（成立）

核心 Lean 4.33 只有 `apply $t`（`src/lean/Init/Tactics.lean:232`）。
`apply t at i`（前向推理）定义在 **Mathlib**：`Mathlib/Tactic/ApplyAt.lean:31`：

```lean
elab "apply " t:term " at " i:ident : tactic => withSynthesize <| withMainContext do
  ...
  let (mvs, bis, _) ← forallMetaTelescopeReducingUntilDefEq (← inferType f) ldecl.type
  ...
```

语义（docstring）：`t : α₁ → … → αᵢ → … → αₙ`、`i : αᵢ` 时，为 `α₁…α_{i-1}` 生成目标，并把 `i` 的类型替换为 `α_{i+1} → … → αₙ`。已验证：

```lean
example (a b c : ℝ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  apply le_trans h at h'   -- h' 从 b ≤ c 变成 a ≤ c
  exact h'
```

---

## 8. 最小复现命令

```bash
cd /workspaces/mathematics_in_lean
lake env lean MVE_apply_behavior_check.lean    # 新建的独立验证文件，EXIT=0
lake env lean MVE_apply_le_trans_goals.lean    # 3 目标 / 默认排序，EXIT=0
lake env lean MVE_apply_inside_out.lean        # 拆解 MVarId.apply 各步，EXIT=0
lake env lean MVE_apply_open_questions.lean    # 补充验证 §9 四点，全部 #guard_msgs 通过，EXIT=0
```

---

## 9. 补充验证（2026-09-25，`MVE_apply_open_questions.lean`，EXIT=0）

### 9.1 `refine` vs `apply`：隐式中间项的处理（成立）

MIL `notes/apply_mechanism.md` 第 4 节第 4 条此前只把 `refine` 断言写在**注释里**，未运行。现补测：

```lean
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  refine le_trans ?_ ?_
```

真实报错（`#guard_msgs (check error)` 已钉死）：

```
error: don't know how to synthesize implicit argument `b`
  @le_trans ℝ Real.instPreorder x ?m.11 z ?m.13 ?m.14
context:
x y z : ℝ
h₀ : x ≤ y
h₁ : y ≤ z
⊢ ℝ
```

即 `refine` **当场要求合成** `b`，合成不出来就直接报错，**不会**像 `apply` 那样把定不住的 `?b` 留成目标。
对照 `refine @le_trans ℝ _ x y z ?_ ?_`（显式给出 `b := y`）后正常生成两个目标。

### 9.2 `nonDependentOnly` 丢弃未赋值空位（成立）

在孤立临时目标上调用 `MVarId.apply … { newGoals := .nonDependentOnly }`，用 `sorry` 关闭返回的 2 个目标后，
统计"证明项里仍未赋值的空位个数 = 1"（即中间项 `?b`）。这解释了此前只作为现象描述的
内核级失败——直接让该证明成为真实声明时，真实输出为：

```
error: (kernel) declaration has metavariables '_example'
```

注意：这是**内核**错误，`#guard_msgs` 捕获不到（它在消息收集之后才产生），因此报告改用 meta 层计数作可运行证据。

### 9.3 目标标签来源（成立）

`apply le_trans` 后三个目标的标签实测为：

```
case a   ⊢ x ≤ ?b      ← 第 1 条前提
case a   ⊢ ?b ≤ z      ← 第 2 条前提
case b   ⊢ ℝ           ← 隐式参数 {b : α} 自己
```

标签由 `Apply.lean:108 appendParentTag` 依据 `forallMetaTelescope` 给出的 binder 用户名设置（`{b}` 有名字 → `case b`；两条无名前提箭头默认取名 `a`）。

### 9.4 `exact le_trans` 的类型类卡死（成立，原文补全）

`MVE_apply_behavior_check.lean`/§6 此前只摘录了前两行。完整真实输出（`#guard_msgs` 已钉死）：

```
error: typeclass instance problem is stuck
  Preorder ?m.8

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Preorder` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. ...
```

`apply le_trans` 同类目标则成功（实例被合成，见 §6），这是 `apply` 推迟实例合成的直接效果。

---

## 10. 不确定点 / 边界

- 行号对应本工作区 vendored 的 Lean 4.33.0 源码（commit d8b1897，路径前缀 `leanprover--lean4---v4.33.0/src/lean/`）；升级 Lean/Mathlib 后行号可能变化，但 `MVarId.apply` / `ApplyConfig` 结构稳定。
- `nonDependentOnly` 的「残留未赋值 mvar → declaration has metavariables」只在直接调用 meta API 时可达，核心 `apply` 战术不暴露该配置。
- `apply t at i` 的具体实现依赖 Mathlib 的 `forallMetaTelescopeReducingUntilDefEq`（`Mathlib/Lean/Meta/Basic.lean:41`），不同 Mathlib 版本可能微调。
- `exact le_trans` 的 Note/Hint 文案属于 Lean 版本相关字符串，升级后可能变；本报告以 4.33.0 原文为准。
- 目标标签中"两条无名前提都叫 `case a`"的**取名规则**（`forallMetaTelescope` 的匿名 binder 命名）未逐行追到底，仅实测标签值。

---

## 11. 追加验证：`lt_of_le_of_lt` 的标签与教材式解法（2026-09-25，`MVE_lt_of_le_of_lt_tags.lean`，EXIT=0）

待验证点来自 `notes/apply_mechanism.md` §6 第 6 条（两处"规则推断、待实测"）。命令：

```bash
cd /workspaces/mathematics_in_lean && lake env lean MVE_lt_of_le_of_lt_tags.lean
```

### Q1：`apply lt_of_le_of_lt` 后三个目标的 case 标签

`#guard_msgs (check trace)` 钉死的真实输出：

```
trace: case hab
a b c d e : ℝ
h₀ : a ≤ b
h₁ : b < c
h₂ : c ≤ d
h₃ : d < e
⊢ a ≤ ?b
---
trace: case hbc
a b c d e : ℝ
h₀ : a ≤ b
h₁ : b < c
h₂ : c ≤ d
h₃ : d < e
⊢ ?b < e
---
trace: case b
a b c d e : ℝ
h₀ : a ≤ b
h₁ : b < c
h₂ : c ≤ d
h₃ : d < e
⊢ ℝ
```

**结论**：标签依次为 **`case hab`、`case hbc`、`case b`**，与推断一致（`hab`/`hbc` 是 `lt_of_le_of_lt` 前提的有名 binder，`b` 是隐式中间项）。

### Q2：教材式解法（第一条用 `apply h₀` 而非 `exact h₀`）

```lean
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt
  · apply h₀
  · exact lt_trans h₁ (lt_of_le_of_lt h₂ h₃)
```

**真实结果：编译通过，EXIT=0**（无 error；仅 Q1 example 的 `sorry` warning）。

**结论**：`apply h₀` 关闭 `a ≤ ?b` 并令 `?b := b`，第 3 个目标随之消失，故只用 2 个 bullet 即可。

### 对笔记的影响

`notes/apply_mechanism.md` §6 第 6 条的两处"规则推断、待实测"**均实测成立**，应改为"已实测"并去掉"推断"标注。
