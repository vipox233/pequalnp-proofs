import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_25607_aux

abbrev Bit := ZMod 2
abbrev Address (b : ℕ) := Fin b → Bit
abbrev Data (b : ℕ) := Address b → Bit × Bit
abbrev Input (b : ℕ) := Address b × Data b

def triangleEdge (p : Bit × Bit) : Fin 3 × Fin 3 :=
  if p.1 = 0 then (if p.2 = 0 then (0, 1) else (1, 2)) else (2, 0)

def cutColor (first : Bit) (vertex : Fin 3) : Bool :=
  decide (vertex = if first = 0 then 1 else 2)

theorem cutColor_separates : ∀ p : Bit × Bit,
    cutColor p.1 (triangleEdge p).1 ≠ cutColor p.1 (triangleEdge p).2 := by
  decide +kernel

def addressBit {b : ℕ} (i : Fin b) : Input b →ₗ[Bit] Bit :=
  (LinearMap.proj i).comp (LinearMap.fst Bit (Address b) (Data b))

def selectedBit {b : ℕ} (addr : Address b) : Input b →ₗ[Bit] Bit :=
  (LinearMap.fst Bit Bit Bit).comp
    ((LinearMap.proj addr).comp (LinearMap.snd Bit (Address b) (Data b)))

def adaptiveRun {b h : ℕ} (z : Input b) (j : Fin h) : Bit :=
  if small : j.val < b then z.1 ⟨j.val, small⟩ else (z.2 z.1).1

def adaptiveAsk {b h : ℕ} (j : Fin h) (history : Fin j.val → Bit) : Input b →ₗ[Bit] Bit :=
  if small : j.val < b then addressBit ⟨j.val, small⟩
  else selectedBit (fun i => history ⟨i.val, i.isLt.trans_le (Nat.le_of_not_gt small)⟩)

theorem adaptive_run_follows {b h : ℕ} (z : Input b) (j : Fin h) :
    adaptiveRun z j = adaptiveAsk j (fun i => adaptiveRun z ⟨i.val, i.isLt.trans j.isLt⟩) z := by
  by_cases small : j.val < b
  · simp only [adaptiveRun, adaptiveAsk, dite_eq_left small]
    rfl
  · simp only [adaptiveRun, adaptiveAsk, dite_eq_right small]
    let addr : Address b := fun i =>
      adaptiveRun z (⟨i.val, (i.isLt.trans_le (Nat.le_of_not_gt small)).trans j.isLt⟩ : Fin h)
    have recovered : addr = z.1 := by
      funext i
      simp [addr, adaptiveRun]
    change (z.2 z.1).1 = (z.2 addr).1
    rw [recovered]

def adaptiveDecoder {b h : ℕ} (long : b + 1 ≤ h) (history : Fin h → Bit)
    (vertex : Address b × Fin 3) : Bool :=
  cutColor (history ⟨b, long⟩) vertex.2

theorem adaptive_decoder_cuts {b h : ℕ} (long : b + 1 ≤ h) (z : Input b) :
    adaptiveDecoder long (adaptiveRun z) (z.1, (triangleEdge (z.2 z.1)).1) ≠
      adaptiveDecoder long (adaptiveRun z) (z.1, (triangleEdge (z.2 z.1)).2) := by
  simp only [adaptiveDecoder, adaptiveRun, Nat.lt_irrefl, dite_false]
  exact cutColor_separates (z.2 z.1)

def blockValue {b : ℕ} (addr : Address b) : Data b →ₗ[Bit] Bit × Bit := LinearMap.proj addr

noncomputable def constrainedBlocks {b q : ℕ} (M : Data b →ₗ[Bit] (Fin q → Bit)) :
    Finset (Address b) := by
  classical
  exact Finset.univ.filter fun j =>
    ¬ Function.Surjective ((blockValue j).comp (LinearMap.ker M).subtype)

theorem constrained_blocks_card_le {b q : ℕ} (M : Data b →ₗ[Bit] (Fin q → Bit)) :
    (constrainedBlocks M).card ≤ q := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T := constrainedBlocks M
  let K := LinearMap.ker M
  let image (j : T) := LinearMap.range ((blockValue j.val).comp K.subtype)
  have proper (j : T) : image j < ⊤ := by
    have member := j.property
    change j.val ∈ constrainedBlocks M at member
    have lacks : ¬ Function.Surjective ((blockValue j.val).comp K.subtype) := by
      simpa only [constrainedBlocks, Finset.mem_filter, Finset.mem_univ, true_and] using member
    exact lt_top_iff_ne_top.mpr (fun eq => lacks (LinearMap.range_eq_top.mp eq))
  have form_exists (j : T) : ∃ f : (Bit × Bit) →ₗ[Bit] Bit, f ≠ 0 ∧ (image j).map f = ⊥ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (proper j) inferInstance
  choose form nonzero vanishes using form_exists
  have one_exists (j : T) : ∃ p : Bit × Bit, form j p = 1 := by
    have witness : ∃ p : Bit × Bit, form j p ≠ 0 := by
      by_contra! h
      apply nonzero j
      exact LinearMap.ext (fun p => h p)
    obtain ⟨p, hp⟩ := witness
    exact ⟨p, Fin.eq_one_of_ne_zero _ hp⟩
  choose lift lift_one using one_exists
  let observe : Data b →ₗ[Bit] (T → Bit) :=
    LinearMap.pi fun j => (form j).comp (blockValue j.val)
  have observe_surj : Function.Surjective observe := by
    intro y
    let d : Data b := fun j => if hj : j ∈ T then y ⟨j, hj⟩ • lift ⟨j, hj⟩ else 0
    refine ⟨d, ?_⟩
    funext j
    change form j (d j.val) = y j
    simp [d, j.property, lift_one]
  have vanishing : K ≤ LinearMap.ker observe := by
    intro d hd
    apply LinearMap.mem_ker.mpr
    funext j
    change form j (d j.val) = 0
    have in_image : d j.val ∈ image j := ⟨⟨d, hd⟩, rfl⟩
    have in_map := Submodule.mem_map_of_mem (f := form j) in_image
    rw [vanishes j] at in_map
    exact (Submodule.mem_bot Bit).mp in_map
  let factor := K.liftQ observe vanishing
  have factor_surj : Function.Surjective factor := by
    intro y
    obtain ⟨d, hd⟩ := observe_surj y
    exact ⟨K.mkQ d, hd⟩
  have dimension := calc
    Module.finrank Bit (T → Bit) ≤ Module.finrank Bit (Data b ⧸ K) :=
      LinearMap.finrank_le_finrank_of_surjective factor_surj
    _ = Module.finrank Bit (LinearMap.range M) := M.quotKerEquivRange.finrank_eq
    _ ≤ Module.finrank Bit (Fin q → Bit) :=
      LinearMap.finrank_le_finrank_of_injective (f := (LinearMap.range M).subtype) Subtype.val_injective
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_fin] using dimension

abbrev Colors (b q : ℕ) := (Fin q → Bit) → (Address b × Fin 3) → Bool

def losingData {b q : ℕ} (transcript : Input b → Fin q → Bit) (label : Colors b q)
    (addr : Address b) : Finset (Data b) :=
  Finset.univ.filter fun d =>
    label (transcript (addr, d)) (addr, (triangleEdge (d addr)).1) =
      label (transcript (addr, d)) (addr, (triangleEdge (d addr)).2)

def dataMap {b q : ℕ} (M : Input b →ₗ[Bit] (Fin q → Bit)) : Data b →ₗ[Bit] (Fin q → Bit) :=
  M.comp (LinearMap.inr Bit (Address b) (Data b))

private theorem always_bad_signature : ∀ label : Fin 3 → Bool,
    ∃ p : Bit × Bit, label (triangleEdge p).1 = label (triangleEdge p).2 := by
  decide +kernel

theorem default_bad_iff : ∀ p : Bit × Bit,
    cutColor 1 (triangleEdge p).1 = cutColor 1 (triangleEdge p).2 ↔ p = (0, 0) := by
  decide +kernel

abbrev ZeroBlock {b : ℕ} (addr : Address b) := {d : Data b // d addr = 0}

theorem zero_block_card {b : ℕ} (addr : Address b) :
    Fintype.card (ZeroBlock addr) = 4 ^ (2 ^ b - 1) := by
  classical
  let Rest := {j : Address b // j ≠ addr}
  let fill : (Rest → Bit × Bit) ≃ ZeroBlock addr :=
    { toFun := fun d => ⟨fun j => if he : j = addr then 0 else d ⟨j, he⟩, by simp⟩
      invFun := fun d j => d.val j.val
      left_inv := by
        intro d
        funext j
        change (if he : j.val = addr then 0 else d ⟨j.val, he⟩) = d j
        rw [dite_eq_right j.property]
      right_inv := by
        intro d
        apply Subtype.ext
        funext j
        by_cases he : j = addr
        · subst j
          exact (dite_eq_left rfl).trans d.property.symm
        · exact dite_eq_right he }
  have bit_card : Fintype.card Bit = 2 := by decide +kernel
  have pair_card : Fintype.card (Bit × Bit) = 4 := by decide +kernel
  have rest_card : Fintype.card Rest = 2 ^ b - 1 := by
    simp only [Rest, Fintype.card_subtype_compl (fun j : Address b => j = addr), Fintype.card_subtype_eq,
      Address, Fintype.card_pi_const, bit_card]
  rw [← Fintype.card_congr fill, Fintype.card_fun, pair_card, rest_card]

theorem unconstrained_loss_lower {b q : ℕ} (M : Input b →ₗ[Bit] (Fin q → Bit))
    (label : Colors b q) (addr : Address b) (free : addr ∉ constrainedBlocks (dataMap M)) :
    4 ^ (2 ^ b - 1) ≤ (losingData M label addr).card := by
  classical
  let K := LinearMap.ker (dataMap M)
  have full : Function.Surjective ((blockValue addr).comp K.subtype) := by
    simpa only [constrainedBlocks, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using free
  choose lift lift_value using full
  have bad_exists (d : ZeroBlock addr) :=
    always_bad_signature (fun v => label (M (addr, d.val)) (addr, v))
  choose bad bad_color using bad_exists
  let put (d : ZeroBlock addr) : Data b := d.val + (lift (bad d)).val
  have at_addr (d : ZeroBlock addr) : put d addr = bad d := by
    have recovered : (lift (bad d)).val addr = bad d := lift_value (bad d)
    change d.val addr + (lift (bad d)).val addr = bad d
    rw [d.property, recovered, zero_add]
  have same (d : ZeroBlock addr) : M (addr, put d) = M (addr, d.val) := by
    have lift_zero : M (0, (lift (bad d)).val) = 0 := LinearMap.mem_ker.mp (lift (bad d)).property
    have sum : (addr, put d) = (addr, d.val) + (0, (lift (bad d)).val) := by
      exact Prod.ext (add_zero addr).symm rfl
    rw [sum, map_add, lift_zero, add_zero]
  have lies_inside (d : ZeroBlock addr) : put d ∈ losingData M label addr := by
    simp only [losingData, Finset.mem_filter, Finset.mem_univ, true_and, same d, at_addr d]
    exact bad_color d
  let inject : ZeroBlock addr → ↥(losingData M label addr) := fun d => ⟨put d, lies_inside d⟩
  have injected : Function.Injective inject := by
    intro d e eq
    have equal : put d = put e := congrArg Subtype.val eq
    have same_bad : bad d = bad e := by
      rw [← at_addr d, ← at_addr e, equal]
    change d.val + (lift (bad d)).val = e.val + (lift (bad e)).val at equal
    rw [same_bad] at equal
    exact Subtype.ext (add_right_cancel equal)
  simpa only [zero_block_card, Fintype.card_coe] using Fintype.card_le_of_injective inject injected

def weightedLoss {b q : ℕ} (transcript : Input b → Fin q → Bit) (label : Colors b q)
    (weight : Address b → ℕ) : ℕ :=
  ∑ addr, weight addr * (losingData transcript label addr).card

def savedWeight {b : ℕ} (q : ℕ) (weight : Address b → ℕ) : ℕ :=
  ((Finset.univ : Finset (Address b)).powerset.filter (fun T => T.card ≤ q)).sup
    (fun T => ∑ j ∈ T, weight j)

def minimumLoss {b : ℕ} (q : ℕ) (weight : Address b → ℕ) : ℕ :=
  4 ^ (2 ^ b - 1) * ((∑ j, weight j) - savedWeight q weight)

private theorem weight_outside {b : ℕ} (T : Finset (Address b)) (w : Address b → ℕ) :
    (∑ addr ∈ Finset.univ \ T, w addr) = (∑ addr, w addr) - (∑ addr ∈ T, w addr) := by
  classical
  have partition : (∑ addr ∈ Finset.univ \ T, w addr) + (∑ addr ∈ T, w addr) = ∑ addr, w addr :=
    Finset.sum_sdiff (Finset.subset_univ T)
  omega

theorem fixed_budget_lower {b q : ℕ} (M : Input b →ₗ[Bit] (Fin q → Bit))
    (label : Colors b q) (w : Address b → ℕ) : minimumLoss q w ≤ weightedLoss M label w := by
  classical
  let T := constrainedBlocks (dataMap M)
  let multiplicity : ℕ := 4 ^ (2 ^ b - 1)
  have eligible : T ∈ (Finset.univ : Finset (Address b)).powerset.filter (fun U => U.card ≤ q) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), constrained_blocks_card_le _⟩
  have saved : (∑ j ∈ T, w j) ≤ savedWeight q w :=
    Finset.le_sup (f := fun U => ∑ j ∈ U, w j) eligible
  change multiplicity * ((∑ j, w j) - savedWeight q w) ≤ weightedLoss M label w
  calc
    _ ≤ multiplicity * ((∑ j, w j) - (∑ j ∈ T, w j)) :=
      Nat.mul_le_mul_left _ (Nat.sub_le_sub_left saved _)
    _ = ∑ j ∈ Finset.univ \ T, w j * multiplicity := by
      rw [← weight_outside T w, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact Nat.mul_comm _ _
    _ ≤ ∑ j ∈ Finset.univ \ T, w j * (losingData M label j).card := by
      apply Finset.sum_le_sum
      intro j hj
      exact Nat.mul_le_mul_left _ (unconstrained_loss_lower M label j (Finset.mem_sdiff.mp hj).2)
    _ ≤ weightedLoss M label w :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) (fun _ _ _ => Nat.zero_le _)

theorem perfect_fixed_requires_all_blocks {b q : ℕ} (M : Input b →ₗ[Bit] (Fin q → Bit))
    (label : Colors b q) (perfect : weightedLoss M label (fun _ => 1) = 0) : 2 ^ b ≤ q := by
  have lower := fixed_budget_lower M label (fun _ => 1)
  rw [perfect] at lower
  have bit_card : Fintype.card Bit = 2 := by decide +kernel
  have total : (∑ _ : Address b, 1) = 2 ^ b := by
    simp [Address, bit_card]
  have saved : savedWeight q (fun _ : Address b => 1) ≤ q := by
    apply Finset.sup_le
    intro T member
    simpa using (Finset.mem_filter.mp member).2
  change 4 ^ (2 ^ b - 1) * ((∑ _ : Address b, 1) - savedWeight q (fun _ => 1)) ≤ 0 at lower
  rw [total] at lower
  by_contra! short
  have remainder : 0 < 2 ^ b - savedWeight q (fun _ : Address b => 1) := by omega
  exact (Nat.not_le_of_lt (Nat.mul_pos (Nat.pow_pos (by decide)) remainder)) lower

theorem fixed_budget_attained {b q : ℕ} (w : Address b → ℕ) :
    ∃ (M : Input b →ₗ[Bit] (Fin q → Bit)) (label : Colors b q),
      weightedLoss M label w = minimumLoss q w := by
  classical
  let feasible := (Finset.univ : Finset (Address b)).powerset.filter (fun T => T.card ≤ q)
  have nonempty : feasible.Nonempty := ⟨∅, by simp [feasible]⟩
  obtain ⟨T, member, maximal⟩ := Finset.exists_mem_eq_sup feasible nonempty (fun S => ∑ j ∈ S, w j)
  have best : savedWeight q w = ∑ j ∈ T, w j := maximal
  have cap : Fintype.card T ≤ q := by
    rw [Fintype.card_coe]
    exact (Finset.mem_filter.mp member).2
  let slot (a : T) : Fin q := Fin.castLE cap (Fintype.equivFin T a)
  have distinct : Function.Injective slot := (Fin.castLE_injective cap).comp (Fintype.equivFin T).injective
  let query (i : Fin q) : Input b →ₗ[Bit] Bit :=
    if hit : ∃ a : T, slot a = i then selectedBit (Classical.choose hit).val else 0
  let M := LinearMap.pi query
  have read (a : T) (z : Input b) : M z (slot a) = (z.2 a.val).1 := by
    have hit : ∃ x : T, slot x = slot a := ⟨a, rfl⟩
    have chosen : Classical.choose hit = a := distinct (Classical.choose_spec hit)
    change query (slot a) z = (z.2 a.val).1
    simp only [query, dite_eq_left hit, chosen]
    rfl
  let label : Colors b q := fun transcript vertex =>
    if hv : vertex.1 ∈ T then cutColor (transcript (slot ⟨vertex.1, hv⟩)) vertex.2
    else cutColor 1 vertex.2
  have no_loss (a : Address b) (ha : a ∈ T) : (losingData M label a).card = 0 := by
    apply Finset.card_eq_zero.mpr
    ext d
    simp only [losingData, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      label, dite_eq_left ha, read]
    exact cutColor_separates (d a)
  have outside_loss (a : Address b) (ha : a ∉ T) :
      (losingData M label a).card = 4 ^ (2 ^ b - 1) := by
    have exactly : losingData M label a = Finset.univ.filter (fun d : Data b => d a = 0) := by
      ext d
      simp only [losingData, Finset.mem_filter, Finset.mem_univ, true_and, label, dite_eq_right ha]
      exact default_bad_iff (d a)
    rw [exactly, ← Fintype.card_subtype (fun d : Data b => d a = 0), zero_block_card]
  refine ⟨M, label, ?_⟩
  let multiplicity : ℕ := 4 ^ (2 ^ b - 1)
  calc
    weightedLoss M label w = ∑ a ∈ Finset.univ \ T, w a * multiplicity := by
      unfold weightedLoss
      rw [← Finset.sum_sdiff (Finset.subset_univ T)]
      have zero_sum : (∑ a ∈ T, w a * (losingData M label a).card) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        rw [no_loss a ha, Nat.mul_zero]
      rw [zero_sum, Nat.add_zero]
      apply Finset.sum_congr rfl
      intro a ha
      rw [outside_loss a (Finset.mem_sdiff.mp ha).2]
    _ = minimumLoss q w := by
      unfold minimumLoss
      rw [best, ← weight_outside T w, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact Nat.mul_comm _ _

abbrev QueryTree (b depth : ℕ) :=
  (j : Fin depth) → (Fin j.val → Bit) → (Input b →ₗ[Bit] Bit)

def consistentRun {b depth : ℕ} (ask : QueryTree b depth)
    (run : Input b → Fin depth → Bit) : Prop :=
  ∀ key j, run key j = ask j (fun i => run key ⟨i.val, i.isLt.trans j.isLt⟩) key

private abbrev QueryNode (depth : ℕ) := Σ j : Fin depth, (Fin j.val → Bit)

private theorem query_node_count (depth : ℕ) : Fintype.card (QueryNode depth) = 2 ^ depth - 1 := by
  have bit_card : Fintype.card Bit = 2 := by decide +kernel
  simp only [QueryNode, Fintype.card_sigma, Fintype.card_pi_const, bit_card]
  induction depth with
  | zero => simp
  | succ h ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Nat.pow_succ]
    have pos : 0 < 2 ^ h := Nat.pow_pos (by decide)
    omega

private theorem flatten_perfect_tree {b depth : ℕ} (ask : QueryTree b depth)
    (run : Input b → Fin depth → Bit) (decoder : Colors b depth)
    (follows : consistentRun ask run) (perfect : weightedLoss run decoder (fun _ => 1) = 0) :
    2 ^ b ≤ Fintype.card (QueryNode depth) := by
  classical
  let index := Fintype.equivFin (QueryNode depth)
  let fixed : Input b →ₗ[Bit] (Fin (Fintype.card (QueryNode depth)) → Bit) :=
    LinearMap.pi fun i => ask (index.symm i).1 (index.symm i).2
  have reads (node : QueryNode depth) (x : Input b) :
      fixed x (index node) = ask node.1 node.2 x := by
    change ask (index.symm (index node)).1 (index.symm (index node)).2 x = ask node.1 node.2 x
    rw [Equiv.symm_apply_apply]
  have agreement (x y : Input b) (same : fixed x = fixed y) : run x = run y := by
    have positions : ∀ n : ℕ, ∀ hn : n < depth, run x ⟨n, hn⟩ = run y ⟨n, hn⟩ := by
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro hn
        let j : Fin depth := ⟨n, hn⟩
        let past (z : Input b) (i : Fin j.val) : Bit := run z ⟨i.val, i.isLt.trans j.isLt⟩
        have earlier : past x = past y := by
          funext i
          exact ih i.val i.isLt (i.isLt.trans j.isLt)
        have same_answer : ask j (past x) x = ask j (past x) y := by
          have at_index := congrFun same (index ⟨j, past x⟩)
          simpa only [reads] using at_index
        change run x j = run y j
        calc
          _ = ask j (past x) x := follows x j
          _ = ask j (past x) y := same_answer
          _ = ask j (past y) y := by rw [earlier]
          _ = _ := (follows y j).symm
    exact funext fun j => positions j.val j.isLt
  let label : Colors b (Fintype.card (QueryNode depth)) := fun a =>
    if reached : ∃ x : Input b, fixed x = a then decoder (run (Classical.choose reached))
    else fun _ => false
  have same_label (x : Input b) : label (fixed x) = decoder (run x) := by
    have reached : ∃ y : Input b, fixed y = fixed x := ⟨x, rfl⟩
    have transcript := agreement _ x (Classical.choose_spec reached)
    simp only [label, dite_eq_left reached, transcript]
  have equal_loss : weightedLoss fixed label (fun _ => 1) = weightedLoss run decoder (fun _ => 1) := by
    unfold weightedLoss losingData
    simp_rw [same_label]
  exact perfect_fixed_requires_all_blocks fixed label (equal_loss.trans perfect)

theorem adaptive_exact {b depth : ℕ} :
    (∃ (ask : QueryTree b depth) (run : Input b → Fin depth → Bit) (decoder : Colors b depth),
      consistentRun ask run ∧ weightedLoss run decoder (fun _ => 1) = 0) ↔ b + 1 ≤ depth := by
  constructor
  · rintro ⟨ask, run, decoder, follows, perfect⟩
    have bound := flatten_perfect_tree ask run decoder follows perfect
    rw [query_node_count] at bound
    have depth_pos : 0 < 2 ^ depth := Nat.pow_pos (by decide)
    have strict : 2 ^ b < 2 ^ depth := by omega
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp strict
  · intro long
    refine ⟨adaptiveAsk, adaptiveRun, adaptiveDecoder long, adaptive_run_follows, ?_⟩
    unfold weightedLoss
    apply Finset.sum_eq_zero
    intro addr _
    have empty : losingData adaptiveRun (adaptiveDecoder long) addr = ∅ := by
      ext d
      simp only [losingData, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact adaptive_decoder_cuts long (addr, d)
    simp [empty]

end PEqualNP.Outside.L_meta_25607_aux

open PEqualNP.Outside.L_meta_25607_aux

theorem PEqualNP.Outside.L_meta_25607 : (∀ b : ℕ,
  let A := Fin b → ZMod 2
  let D := A → ZMod 2 × ZMod 2
  let V := A × D
  let s := 2 ^ b
  let edge := fun z : V =>
    (if (z.2 z.1).1 = 0 then (if (z.2 z.1).2 = 0 then (0, 1) else (1, 2))
     else (2, 0) : Fin 3 × Fin 3)
  let Colors := fun q : ℕ => (Fin q → ZMod 2) → (A × Fin 3) → Bool
  let losses := fun (q : ℕ) (transcript : V → Fin q → ZMod 2) (colors : Colors q) (wt : A → ℕ) =>
    ∑ addr : A, wt addr * (Finset.univ.filter (fun x : D =>
      colors (transcript (addr, x)) (addr, (edge (addr, x)).1) =
      colors (transcript (addr, x)) (addr, (edge (addr, x)).2))).card
  let Ask := fun limit : ℕ => (j : Fin limit) → (Fin j.val → ZMod 2) → (V →ₗ[ZMod 2] ZMod 2)
  let follows := fun (depth : ℕ) (ask : Ask depth) (run : V → Fin depth → ZMod 2) =>
    ∀ (key : V) (j : Fin depth),
      run key j = ask j (fun i => run key ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) key
  (∀ (q : ℕ) (w : A → ℕ),
    let saved := ((Finset.univ : Finset A).powerset.filter (fun T => T.card ≤ q)).sup
      (fun T => ∑ j ∈ T, w j)
    let cost := 4 ^ (s - 1) * ((∑ j : A, w j) - saved)
    (∃ (Q : V →ₗ[ZMod 2] (Fin q → ZMod 2)) (label : Colors q), losses q Q label w = cost) ∧
    ∀ (M : V →ₗ[ZMod 2] (Fin q → ZMod 2)) (family : Colors q), cost ≤ losses q M family w) ∧
  ∀ h : ℕ, (∃ (ask : Ask h) (run : V → Fin h → ZMod 2) (decoder : Colors h),
    follows h ask run ∧ losses h run decoder (fun _ => 1) = 0) ↔ b + 1 ≤ h) := by
  intro b A D V s edge Colors losses Ask follows
  constructor
  · intro q w
    exact ⟨fixed_budget_attained (q := q) w, fun M family => fixed_budget_lower M family w⟩
  · intro h
    exact adaptive_exact (b := b) (depth := h)
