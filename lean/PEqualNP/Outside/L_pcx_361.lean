import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_361_aux
namespace Base

namespace BooleanCoordinates

def bit : Bool → ZMod 2
  | false => 0
  | true => 1

@[local simp] theorem bit_false : bit false = 0 := rfl
@[local simp] theorem bit_true : bit true = 1 := rfl

def bitEquiv : Bool ≃ ZMod 2 where
  toFun := bit
  invFun a := decide (a = 1)
  left_inv b := by cases b <;> decide
  right_inv := by decide

def vector {n : ℕ} (x : Fin n → Bool) : Fin n → ZMod 2 := fun i => bit (x i)

def vectorEquiv (n : ℕ) : (Fin n → Bool) ≃ (Fin n → ZMod 2) where
  toFun := vector
  invFun x i := bitEquiv.symm (x i)
  left_inv x := funext fun i => bitEquiv.left_inv (x i)
  right_inv x := funext fun i => bitEquiv.right_inv (x i)

def support {n : ℕ} (f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) : Finset (Fin n) :=
  Finset.univ.filter fun i => f (Pi.single i 1) = 1

theorem mem_support {n : ℕ} (f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (i : Fin n) : i ∈ support f ↔ f (Pi.single i 1) = 1 := by
  simp [support]

open scoped BigOperators

theorem apply_eq_sum_support {n : ℕ} (f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (x : Fin n → ZMod 2) : f x = ∑ i ∈ support f, x i := by
  have expand : (∑ i : Fin n, x i • Pi.single i (1 : ZMod 2)) = x := by
    ext j
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  conv_lhs => rw [← expand, map_sum]
  rw [support, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul]
  have split : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases split (f (Pi.single i 1)) with h | h <;> simp [h]

theorem apply_vector_eq_card {n : ℕ} (f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (x : Fin n → Bool) :
    f (vector x) = ((support f).filter fun i => x i = true).card := by
  rw [apply_eq_sum_support, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases h : x i <;> simp [vector, h]

theorem apply_vector_eq_one_iff {n : ℕ} (f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (x : Fin n → Bool) :
    f (vector x) = 1 ↔ ((support f).filter fun i => x i = true).card % 2 = 1 := by
  rw [apply_vector_eq_card]
  constructor
  · intro h
    simpa [ZMod.val_natCast, ZMod.val_one_eq_one_mod] using congrArg ZMod.val h
  · intro h
    rw [← ZMod.natCast_mod, h, Nat.cast_one]

end BooleanCoordinates

inductive PTree (Q I : Type) where
  | leaf (i : I)
  | branch (q : Q) (l r : PTree Q I)

namespace PTree

variable {Q I : Type} {X : Type*}

private def prepend (b : Bool) : List Bool ↪ List Bool where
  toFun := List.cons b
  inj' := by intro a c h; exact (List.cons.inj h).2

private theorem prepend_apply (b : Bool) (p : List Bool) : prepend b p = b :: p := rfl

def nodes : PTree Q I → Finset (List Bool)
  | .leaf _ => {[]}
  | .branch _ l r => insert [] ((l.nodes.map (prepend false)) ∪ (r.nodes.map (prepend true)))

def inner : PTree Q I → Finset (List Bool)
  | .leaf _ => ∅
  | .branch _ l r => insert [] ((l.inner.map (prepend false)) ∪ (r.inner.map (prepend true)))

def subtree : PTree Q I → List Bool → Option (PTree Q I)
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .branch _ l _, false :: p => l.subtree p
  | .branch _ _ r, true :: p => r.subtree p

def ask (default : Q) (t : PTree Q I) (p : List Bool) : Q :=
  match t.subtree p with
  | some (.branch q _ _) => q
  | _ => default

def out (default : I) (t : PTree Q I) (p : List Bool) : I :=
  match t.subtree p with
  | some (.leaf i) => i
  | _ => default

theorem root_mem_nodes (t : PTree Q I) : [] ∈ t.nodes := by
  cases t <;> simp [nodes]

@[local simp] theorem mem_nodes_cons_branch (q : Q) (l r : PTree Q I) (b : Bool)
    (p : List Bool) :
    b :: p ∈ (branch q l r).nodes ↔ p ∈ (if b then r else l).nodes := by
  cases b <;> simp [nodes, prepend_apply]

@[local simp] theorem mem_inner_cons_branch (q : Q) (l r : PTree Q I) (b : Bool)
    (p : List Bool) :
    b :: p ∈ (branch q l r).inner ↔ p ∈ (if b then r else l).inner := by
  cases b <;> simp [inner, prepend_apply]

theorem mem_nodes_iff (t : PTree Q I) (p : List Bool) :
    p ∈ t.nodes ↔ ∃ u, t.subtree p = some u := by
  induction t generalizing p with
  | leaf i => cases p <;> simp [nodes, subtree]
  | branch q l r hl hr =>
    cases p with
    | nil => simp [nodes, subtree]
    | cons b p => cases b <;> simp [subtree, hl, hr]

theorem mem_inner_iff (t : PTree Q I) (p : List Bool) :
    p ∈ t.inner ↔ ∃ q l r, t.subtree p = some (.branch q l r) := by
  induction t generalizing p with
  | leaf i => cases p <;> simp [inner, subtree]
  | branch q l r hl hr =>
    cases p with
    | nil => simp [inner, subtree]
    | cons b p => cases b <;> simp [subtree, hl, hr]

theorem inner_subset_nodes (t : PTree Q I) : t.inner ⊆ t.nodes := by
  intro p hp
  obtain ⟨q, l, r, h⟩ := (t.mem_inner_iff p).mp hp
  exact (t.mem_nodes_iff p).mpr ⟨.branch q l r, h⟩

theorem mem_leaves_iff (t : PTree Q I) (p : List Bool) :
    p ∈ t.nodes \ t.inner ↔ ∃ i, t.subtree p = some (.leaf i) := by
  rw [Finset.mem_sdiff, mem_nodes_iff, mem_inner_iff]
  constructor
  · rintro ⟨⟨u, hu⟩, hn⟩
    cases u with
    | leaf i => exact ⟨i, hu⟩
    | branch q l r => exact (hn ⟨q, l, r, hu⟩).elim
  · rintro ⟨i, hi⟩
    refine ⟨⟨.leaf i, hi⟩, ?_⟩
    simp [hi]

theorem ask_eq_of_subtree {t : PTree Q I} {p : List Bool} {q : Q} {l r : PTree Q I}
    (default : Q) (h : t.subtree p = some (.branch q l r)) : t.ask default p = q := by
  simp [ask, h]

theorem subtree_eq_ask_of_mem_inner (t : PTree Q I) (default : Q) {p : List Bool}
    (h : p ∈ t.inner) : ∃ l r, t.subtree p = some (.branch (t.ask default p) l r) := by
  obtain ⟨q, l, r, hq⟩ := (t.mem_inner_iff p).mp h
  exact ⟨l, r, by rw [ask_eq_of_subtree default hq, hq]⟩

theorem out_eq_of_subtree {t : PTree Q I} {p : List Bool} {i : I}
    (default : I) (h : t.subtree p = some (.leaf i)) : t.out default p = i := by
  simp [out, h]

theorem subtree_eq_out_of_mem_leaves (t : PTree Q I) (default : I) {p : List Bool}
    (h : p ∈ t.nodes \ t.inner) : t.subtree p = some (.leaf (t.out default p)) := by
  obtain ⟨i, hi⟩ := (t.mem_leaves_iff p).mp h
  rw [out_eq_of_subtree default hi, hi]

theorem subtree_append (t : PTree Q I) (p s : List Bool) :
    t.subtree (p ++ s) = (t.subtree p).bind (fun u => u.subtree s) := by
  induction t generalizing p with
  | leaf i => cases p <;> rfl
  | branch q l r hl hr =>
    cases p with
    | nil => rfl
    | cons b p => cases b <;> exact (by first | exact hl p | exact hr p)

theorem child_mem_iff (t : PTree Q I) (p : List Bool) (b : Bool) :
    p ++ [b] ∈ t.nodes ↔ p ∈ t.inner := by
  rw [mem_nodes_iff, mem_inner_iff, subtree_append]
  cases h : t.subtree p with
  | none => simp
  | some u =>
    cases u with
    | leaf i => simp [subtree]
    | branch q l r => cases b <;> simp [subtree]

theorem parent_mem_inner (t : PTree Q I) (p : List Bool) (b : Bool)
    (h : p ++ [b] ∈ t.nodes) : p ∈ t.inner :=
  (t.child_mem_iff p b).mp h

theorem children_mem_nodes (t : PTree Q I) {p : List Bool} (h : p ∈ t.inner) :
    p ++ [false] ∈ t.nodes ∧ p ++ [true] ∈ t.nodes :=
  ⟨(t.child_mem_iff p false).mpr h, (t.child_mem_iff p true).mpr h⟩

def restrict (e : Q → X → Bool) : PTree Q I → List Bool → X → Prop
  | _, [], _ => True
  | .leaf _, _ :: _, _ => False
  | .branch q l r, b :: p, x => e q x = b ∧ restrict e (if b then r else l) p x

def followsAll (e : Q → X → Bool) (default : Q) (t : PTree Q I) (p : List Bool) (x : X) : Prop :=
  ∀ j : Fin p.length, e (t.ask default (p.take j.val)) x = p.get j

def follows (e : Q → X → Bool) (default : Q) (t : PTree Q I) (p : List Bool) (x : X) : Bool :=
  decide (((Finset.univ : Finset (Fin p.length)).filter (fun j =>
    e (t.ask default (p.take j.val)) x ≠ p.get j)).card = 0)

theorem follows_eq_true_iff (e : Q → X → Bool) (default : Q) (t : PTree Q I)
    (p : List Bool) (x : X) : t.follows e default p x = true ↔ t.followsAll e default p x := by
  simp [follows, followsAll, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

private theorem ask_cons_branch (default q : Q) (l r : PTree Q I) (b : Bool)
    (p : List Bool) :
    (branch q l r).ask default (b :: p) = (if b then r else l).ask default p := by
  cases b <;> rfl

theorem followsAll_cons_branch (e : Q → X → Bool) (default q : Q) (l r : PTree Q I)
    (b : Bool) (p : List Bool) (x : X) :
    (branch q l r).followsAll e default (b :: p) x ↔
      e q x = b ∧ (if b then r else l).followsAll e default p x := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [ask, subtree] using h 0
    · intro j
      simpa [ask_cons_branch] using h j.succ
  · rintro ⟨h₀, hs⟩ j
    exact Fin.cases (by simpa [ask, subtree] using h₀)
      (fun k => by simpa [ask_cons_branch] using hs k) j

theorem followsAll_iff_restrict (e : Q → X → Bool) (default : Q) (t : PTree Q I)
    (p : List Bool) (x : X) : p ∈ t.nodes ∧ t.followsAll e default p x ↔ t.restrict e p x := by
  induction t generalizing p with
  | leaf i => cases p <;> simp [nodes, followsAll, restrict]
  | branch q l r hl hr =>
    cases p with
    | nil => simp [nodes, followsAll, restrict]
    | cons b p =>
      rw [mem_nodes_cons_branch, followsAll_cons_branch, restrict]
      rw [and_left_comm]
      cases b <;> simp [hl, hr]

theorem follows_iff_restrict (e : Q → X → Bool) (default : Q) (t : PTree Q I)
    {p : List Bool} (h : p ∈ t.nodes) (x : X) :
    t.follows e default p x = true ↔ t.restrict e p x := by
  rw [follows_eq_true_iff, ← followsAll_iff_restrict e default, and_iff_right h]

end PTree

open scoped BigOperators

private theorem exists_min_codimension_by_mass {α : Type*} [DecidableEq α]
    {s : Finset α} {m : ℕ} (t : Fin m → Finset α) (c : Fin m → ℕ)
    (hs : s.Nonempty) (hcover : s ⊆ Finset.univ.biUnion t)
    (hmass : ∀ i, (t i).Nonempty → (t i).card * 2 ^ c i = s.card) :
    ∃ i, (t i).Nonempty ∧ c i ≤ Nat.log 2 m ∧
      ∀ j, (t j).Nonempty → c i ≤ c j := by
  classical
  have hcard : s.card ≤ ∑ i, (t i).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hex : ∃ i, (t i).Nonempty ∧ c i ≤ Nat.log 2 m := by
    by_contra h
    let d := Nat.log 2 m + 1
    have hbound (i : Fin m) : (t i).card * 2 ^ d ≤ s.card := by
      by_cases hi : (t i).Nonempty
      · have hc : d ≤ c i := Nat.succ_le_of_lt (lt_of_not_ge fun hci => h ⟨i, hi, hci⟩)
        rw [← hmass i hi]
        exact Nat.mul_le_mul_left _ (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hc)
      · simp [Finset.not_nonempty_iff_eq_empty.mp hi]
    have hscaled : s.card * 2 ^ d ≤ m * s.card := by
      calc
        s.card * 2 ^ d ≤ (∑ i, (t i).card) * 2 ^ d := Nat.mul_le_mul_right _ hcard
        _ = ∑ i, (t i).card * 2 ^ d := Finset.sum_mul _ _ _
        _ ≤ ∑ _i : Fin m, s.card := Finset.sum_le_sum fun i _ => hbound i
        _ = m * s.card := by simp
    have hd : 2 ^ d ≤ m :=
      Nat.le_of_mul_le_mul_right (by simpa only [Nat.mul_comm s.card] using hscaled)
        (Finset.card_pos.mpr hs)
    exact (not_lt_of_ge hd) (Nat.lt_pow_succ_log_self (by decide : 1 < 2) m)
  obtain ⟨j, hj, hjc⟩ := hex
  let good : Finset (Fin m) := Finset.univ.filter fun i => (t i).Nonempty
  have hgood (i : Fin m) : i ∈ good ↔ (t i).Nonempty := by simp [good]
  obtain ⟨i, hi, hmin⟩ := good.exists_min_image c ⟨j, (hgood j).mpr hj⟩
  exact ⟨i, (hgood i).mp hi, (hmin j ((hgood j).mpr hj)).trans hjc,
    fun k hk => hmin k ((hgood k).mpr hk)⟩

private def potential (m k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, min (j + 1) (Nat.log 2 m)

private theorem add_potential_le {m r' r s : ℕ} (hrr : r' < r) (hsr : s ≤ r)
    (hsl : s ≤ Nat.log 2 m) : s + potential m r' ≤ potential m r := by
  cases r with
  | zero => omega
  | succ r =>
    have hmono : potential m r' ≤ potential m r := by
      unfold potential
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.le_of_lt_succ hrr)) (fun _ _ _ => Nat.zero_le _)
    have hs : s ≤ min (r + 1) (Nat.log 2 m) := le_min hsr hsl
    unfold potential at ⊢
    rw [Finset.sum_range_succ]
    exact (Nat.add_comm s (potential m r')).le.trans (Nat.add_le_add hmono hs)

open Module

private theorem finrank_sub_inf_lt_of_disjoint_translates
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    {U W V : Submodule (ZMod 2) E} [FiniteDimensional (ZMod 2) U]
    (hWU : W ≤ U) (hVU : V ≤ U) {a b : E} (hab : a - b ∈ U)
    (hdis : Disjoint ((fun w : E => a + w) '' (W : Set E))
      ((fun v : E => b + v) '' (V : Set E))) :
    finrank (ZMod 2) V - finrank (ZMod 2) (V ⊓ W : Submodule (ZMod 2) E) <
      finrank (ZMod 2) U - finrank (ZMod 2) W := by
  have hnot : a - b ∉ W ⊔ V := by
    intro hmem
    obtain ⟨w, hw, v, hv, hwv⟩ := Submodule.mem_sup.mp hmem
    have heq : a + -w = b + v := calc
      a + -w = (a - b) + b + -w := by abel
      _ = b + v := by rw [← hwv]; abel
    exact Set.disjoint_left.mp hdis ⟨-w, W.neg_mem hw, heq⟩ ⟨v, hv, rfl⟩
  have hsup : W ⊔ V < U := lt_of_le_not_ge (sup_le hWU hVU) (fun h => hnot (h hab))
  letI : FiniteDimensional (ZMod 2) W :=
    FiniteDimensional.of_injective (Submodule.inclusion hWU) (Submodule.inclusion_injective hWU)
  letI : FiniteDimensional (ZMod 2) V :=
    FiniteDimensional.of_injective (Submodule.inclusion hVU) (Submodule.inclusion_injective hVU)
  have hdim := Submodule.finrank_lt_finrank_of_lt hsup
  have hWdim := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_lt le_sup_left hsup)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W V
  rw [inf_comm W V] at hsum
  omega

namespace PCX360

noncomputable section AffineQueries
open scoped BigOperators

abbrev F := ZMod 2
abbrev E (n : ℕ) := Fin n → F
abbrev Dir (n : ℕ) := Submodule F (E n)
abbrev Query (n : ℕ) := E n →ₗ[F] F

def coset {n : ℕ} (a : E n) (U : Dir n) : Set (E n) := {x | x - a ∈ U}

@[local simp] theorem mem_coset {n : ℕ} {a x : E n} {U : Dir n} :
    x ∈ coset a U ↔ x - a ∈ U := Iff.rfl

theorem self_mem_coset {n : ℕ} (a : E n) (U : Dir n) : a ∈ coset a U := by simp

theorem coset_inter {n : ℕ} {a b x : E n} {U V : Dir n}
    (ha : x ∈ coset a U) (hb : x ∈ coset b V) :
    coset a U ∩ coset b V = coset x (U ⊓ V) := by
  ext y
  change (y - a ∈ U ∧ y - b ∈ V) ↔ (y - x ∈ U ∧ y - x ∈ V)
  constructor
  · rintro ⟨hyU, hyV⟩
    exact ⟨by simpa using U.sub_mem hyU ha, by simpa using V.sub_mem hyV hb⟩
  · rintro ⟨hyU, hyV⟩
    exact ⟨by simpa using U.add_mem hyU ha, by simpa using V.add_mem hyV hb⟩

def enum {n : ℕ} (S : Set (E n)) : Finset (E n) := by
  classical exact Finset.univ.filter (· ∈ S)

@[local simp] theorem mem_enum {n : ℕ} {S : Set (E n)} {x : E n} : x ∈ enum S ↔ x ∈ S := by
  classical simp [enum]

def rk {n : ℕ} (U : Dir n) := Module.finrank F U

theorem card_coset {n : ℕ} (a : E n) (U : Dir n) : (enum (coset a U)).card = 2 ^ rk U := by
  classical
  rw [← Fintype.card_coe]
  let e : U ≃ ↥(enum (coset a U)) :=
    { toFun := fun u => ⟨u.val + a, by simpa using u.property⟩
      invFun := fun x => ⟨x.val - a, mem_coset.mp (mem_enum.mp x.property)⟩
      left_inv := by intro u; ext : 1; simp
      right_inv := by intro x; ext : 1; simp }
  rw [← Fintype.card_congr e, Module.card_eq_pow_finrank (K := F)]
  simp [F, rk]

theorem rk_top (n : ℕ) : rk (⊤ : Dir n) = n := by
  simp [rk, finrank_top, Module.finrank_pi, Module.finrank_self]

private theorem split {n : ℕ} (a : E n) {W U : Dir n} (hle : W < U) :
    ∃ (q : Query n) (V : Dir n) (a₀ a₁ : E n),
      W ≤ V ∧ V ≤ U ∧ rk V + 1 = rk U ∧
      (∀ x, x ∈ coset a₀ V ↔ x ∈ coset a U ∧ q x = 0) ∧
      (∀ x, x ∈ coset a₁ V ↔ x ∈ coset a U ∧ q x = 1) := by
  classical
  obtain ⟨v,hv,hvw⟩ := IsConcreteLE.exists_of_lt hle
  obtain ⟨q,hq,hW⟩ := Submodule.exists_le_ker_of_notMem hvw
  have hq1 : q v = 1 := by
    have h : ∀ x : F, x ≠ 0 → x = 1 := by decide
    exact h _ hq
  let V := U ⊓ LinearMap.ker q
  have hker : LinearMap.ker (q.domRestrict U) = V.comap U.subtype := by
    ext x
    simp [V]
  have hrank : rk V + 1 = rk U := by
    have hne : q.domRestrict U ≠ 0 := by
      intro hzero
      have hh := DFunLike.congr_fun hzero ⟨v,hv⟩
      exact hq (by simpa using hh)
    have hr := Module.Dual.finrank_ker_add_one_of_ne_zero hne
    rw [hker, (Submodule.comapSubtypeEquivOfLe (inf_le_left : V ≤ U)).finrank_eq] at hr
    exact hr
  let a₀ := a - q a • v
  let a₁ := a₀ + v
  have ha₀ : a₀ ∈ coset a U := by simp [a₀, U.neg_mem (U.smul_mem _ hv)]
  have ha₁ : a₁ ∈ coset a U := by
    have hh := U.add_mem ha₀ hv
    change a₁ - a ∈ U
    convert hh using 1 <;> dsimp [a₁] <;> abel
  have q₀ : q a₀ = 0 := by simp [a₀, hq1]
  have q₁ : q a₁ = 1 := by simp [a₁, q₀, hq1]
  have hchar (b : E n) (hb : b ∈ coset a U) (x : E n) :
      x ∈ coset b V ↔ x ∈ coset a U ∧ q x = q b := by
    simp only [mem_coset, V, Submodule.mem_inf, LinearMap.mem_ker, map_sub, sub_eq_zero]
    constructor
    · rintro ⟨hx,hxq⟩
      exact ⟨by simpa using U.add_mem hx hb, hxq⟩
    · rintro ⟨hx,hxq⟩
      exact ⟨by simpa using U.sub_mem hx hb, hxq⟩
  exact ⟨q,V,a₀,a₁,le_inf hle.le hW,inf_le_left,hrank,
    fun x => by simpa only [q₀] using hchar a₀ ha₀ x,
    fun x => by simpa only [q₁] using hchar a₁ ha₁ x⟩

abbrev Tree (n m : ℕ) := PTree (Query n) (Fin m)

inductive Run {n m : ℕ} (x : E n) : Tree n m → ℕ → Fin m → Prop where
  | leaf (i) : Run x (.leaf i) 0 i
  | left {q l r d i} : q x = 0 → Run x l d i → Run x (.branch q l r) (d+1) i
  | right {q l r d i} : q x = 1 → Run x r d i → Run x (.branch q l r) (d+1) i

inductive Valid {n m : ℕ} (C : Fin m → Set (E n)) :
    E n → Dir n → Tree n m → Prop where
  | leaf {a U i} : coset a U ⊆ C i → Valid C a U (.leaf i)
  | branch {a a₀ a₁ U V q l r} :
      rk V + 1 = rk U →
      (∀ x, x ∈ coset a₀ V ↔ x ∈ coset a U ∧ q x = 0) →
      (∀ x, x ∈ coset a₁ V ↔ x ∈ coset a U ∧ q x = 1) →
      Valid C a₀ V l → Valid C a₁ V r → Valid C a U (.branch q l r)

theorem valid_output {n m : ℕ} {C : Fin m → Set (E n)} {a U t}
    (ht : Valid C a U t) {x d i} (hx : x ∈ coset a U) (hr : Run x t d i) : x ∈ C i := by
  induction ht generalizing d i with
  | leaf h => cases hr; exact h hx
  | branch _ hl hr' _ _ ihl ihr =>
    cases hr with
    | left h hr => exact ihl ((hl _).2 ⟨hx,h⟩) hr
    | right h hr => exact ihr ((hr' _).2 ⟨hx,h⟩) hr

private theorem peel {n m : ℕ} {C : Fin m → Set (E n)} (f : Fin m → ℕ)
    (a : E n) (U W : Dir n) (hWU : W ≤ U)
    (finish : ∀ b, coset b W ⊆ coset a U → ∃ t, Valid C b W t ∧
      ∀ x d i, x ∈ coset b W → Run x t d i → d ≤ f i) :
    ∃ t, Valid C a U t ∧
      ∀ x d i, x ∈ coset a U → Run x t d i → d ≤ rk U - rk W + f i := by
  classical
  by_cases h : W = U
  · subst W
    simpa using finish a subset_rfl
  · obtain ⟨q,V,a₀,a₁,hWV,_,hr,h₀,h₁⟩ := split a (lt_of_le_of_ne hWU h)
    obtain ⟨l,hl,bl⟩ := peel f a₀ V W hWV (fun b hb => finish b (hb.trans fun x hx => ((h₀ x).1 hx).1))
    obtain ⟨r,hr',br⟩ := peel f a₁ V W hWV (fun b hb => finish b (hb.trans fun x hx => ((h₁ x).1 hx).1))
    refine ⟨.branch q l r, .branch hr h₀ h₁ hl hr', ?_⟩
    have hw := Submodule.finrank_mono hWV
    intro x d i hx run
    cases run with
    | left hq ht =>
      have hb := bl _ _ _ ((h₀ _).2 ⟨hx,hq⟩) ht
      unfold rk at *
      omega
    | right hq ht =>
      have hb := br _ _ _ ((h₁ _).2 ⟨hx,hq⟩) ht
      unfold rk at *
      omega
termination_by rk U
decreasing_by all_goals omega

end AffineQueries
end PCX360

namespace PCX360

noncomputable section CellEquations
open BooleanCoordinates
open scoped BigOperators

def eqQuery {n : ℕ} (s : Finset (Fin n)) : Query n := ∑ j ∈ s, LinearMap.proj j

theorem eqQuery_support {n : ℕ} (s : Finset (Fin n)) : support (eqQuery s) = s := by
  classical
  ext j
  simp only [mem_support, eqQuery, LinearMap.sum_apply, LinearMap.proj_apply, Pi.single_apply]
  by_cases hj : j ∈ s
  · rw [Finset.sum_eq_single j] <;> simp_all [eq_comm]
  · have hzero : ∑ k ∈ s, (if k = j then (1 : F) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [show k ≠ j from fun e => hj (e ▸ hk)]
    simpa only [eq_comm (a := j), hzero, zero_ne_one, hj]

theorem query_bit {n : ℕ} (q : Query n) (x : Fin n → Bool) (b : Bool) :
    q (vector x) = bit b ↔ decide (((support q).filter (fun j => x j)).card % 2 = 1) = b := by
  cases b
  · have two : ∀ a : F, a ≠ 1 ↔ a = 0 := by decide
    simpa only [bit_false, decide_eq_false_iff_not, ← apply_vector_eq_one_iff] using (two (q (vector x))).symm
  · simpa only [bit_true, decide_eq_true_eq] using apply_vector_eq_one_iff q x

def cellDir {n : ℕ} (s : Finset (Finset (Fin n) × Bool)) : Dir n :=
  ⨅ (e : Finset (Fin n) × Bool) (_ : e ∈ s), LinearMap.ker (eqQuery e.1)

def cellSet {n : ℕ} (s : Finset (Finset (Fin n) × Bool)) : Set (E n) :=
  {x | ∀ e ∈ s, eqQuery e.1 x = bit e.2}

theorem cell_coset {n : ℕ} (s : Finset (Finset (Fin n) × Bool)) {a : E n}
    (ha : a ∈ cellSet s) : cellSet s = coset a (cellDir s) := by
  ext x
  simp only [cellSet, Set.mem_setOf_eq, mem_coset, cellDir, Submodule.mem_iInf,
    LinearMap.mem_ker, map_sub, sub_eq_zero]
  exact forall_congr' fun e => forall_congr' fun he => by rw [ha e he]

def insideBool {n : ℕ} (s : Finset (Finset (Fin n) × Bool)) (x : Fin n → Bool) : Bool :=
  decide (((s.filter fun e => decide ((e.1.filter fun v => x v).card % 2 = 1) ≠ e.2)).card = 0)

theorem insideBool_iff {n : ℕ} (s : Finset (Finset (Fin n) × Bool)) (x : Fin n → Bool) :
    insideBool s x = true ↔ vector x ∈ cellSet s := by
  classical
  simp only [insideBool, decide_eq_true_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    not_ne_iff, cellSet, Set.mem_setOf_eq]
  exact forall_congr' fun e => forall_congr' fun _ => by rw [query_bit, eqQuery_support]

theorem card_vector {n : ℕ} (p : (Fin n → Bool) → Prop) [DecidablePred p] (S : Set (E n))
    (h : ∀ x, p x ↔ vector x ∈ S) : (Finset.univ.filter p).card = (enum S).card := by
  classical
  apply Finset.card_bij (fun x _ => vector x)
  · intro x hx
    exact mem_enum.mpr ((h x).mp (Finset.mem_filter.mp hx).2)
  · intro x hx y hy he
    exact (vectorEquiv n).injective he
  · intro z hz
    let x := (vectorEquiv n).symm z
    have hx : vector x = z := (vectorEquiv n).apply_symm_apply z
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h x).mpr (hx ▸ mem_enum.mp hz)⟩, hx⟩

end CellEquations
end PCX360

namespace PCX360

noncomputable section QueryStrategy

def rel {n : ℕ} (U W : Dir n) := rk U - rk (U ⊓ W)

theorem translated_coset {n : ℕ} (a : E n) (U : Dir n) :
    (fun w : E n => a + w) '' (U : Set (E n)) = coset a U := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [mem_coset, add_comm a w] using hw
  · intro hx
    exact ⟨x-a, hx, by abel⟩

private theorem strategy {n m : ℕ} (A : Fin m → E n) (W : Fin m → Dir n)
    (cover : ∀ x, ∃! i, x ∈ coset (A i) (W i)) (a : E n) (U : Dir n) :
    ∃ t, Valid (fun i => coset (A i) (W i)) a U t ∧
      ∀ x d i, x ∈ coset a U → Run x t d i → d ≤ potential m (rel U (W i)) := by
  classical
  let C := fun i => coset (A i) (W i)
  let D := coset a U
  let T := fun i => enum (D ∩ C i)
  have hmass (i : Fin m) (hi : (T i).Nonempty) :
      (T i).card * 2 ^ rel U (W i) = (enum D).card := by
    obtain ⟨x,hx⟩ := hi
    have hx' : x ∈ D ∩ C i := mem_enum.mp hx
    have hle := Submodule.finrank_mono (inf_le_left : U ⊓ W i ≤ U)
    change (enum (coset a U ∩ coset (A i) (W i))).card * _ = _
    rw [coset_inter hx'.1 hx'.2, card_coset, card_coset, ← pow_add]
    congr 1
    unfold rel rk at *
    omega
  have hc : enum D ⊆ Finset.univ.biUnion T := by
    intro x hx
    obtain ⟨i,hi,_⟩ := cover x
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,mem_enum.mpr ⟨mem_enum.mp hx,hi⟩⟩
  obtain ⟨k,hk,hlog,hmin⟩ := exists_min_codimension_by_mass T (fun i => rel U (W i))
    ⟨a,mem_enum.mpr (self_mem_coset a U)⟩ hc hmass
  obtain ⟨z,hz⟩ := hk
  have hz' : z ∈ D ∩ C k := mem_enum.mp hz
  let V := U ⊓ W k
  have hV : V ≤ U := inf_le_left
  have hUV : D ∩ C k = coset z V := coset_inter hz'.1 hz'.2
  by_cases h : V = U
  · have hdz : coset z U = D := by
      ext x
      change x - z ∈ U ↔ x - a ∈ U
      exact ⟨fun hx => by simpa using U.add_mem hx hz'.1,
        fun hx => by simpa using U.sub_mem hx hz'.1⟩
    have hsub : D ⊆ C k := by
      intro x hx
      have hmem : x ∈ D ∩ C k := by rwa [hUV,h,hdz]
      exact hmem.2
    exact ⟨.leaf k, .leaf hsub, fun x d i hx hr => by cases hr; exact Nat.zero_le _⟩
  · have hrank := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hV h)
    let f := fun i => potential m (rel V (W i))
    obtain ⟨t,ht,hdepth⟩ := peel f a U V hV (fun b hb => strategy A W cover b V)
    refine ⟨t,ht,?_⟩
    intro x d i hx hrun
    have hxi : x ∈ C i := valid_output ht hx hrun
    have hsmall := hmin i ⟨x,mem_enum.mpr ⟨hx,hxi⟩⟩
    have hstrict : rel V (W i) < rel U (W i) := by
      by_cases hi : i = k
      · subst i
        have hVi : V ⊓ W k = V := inf_eq_left.mpr inf_le_right
        unfold rel
        rw [hVi]
        have hh : rk V < rk U := hrank
        change rk V - rk V < rk U - rk V
        omega
      · let J := U ⊓ W i
        have hJ : D ∩ C i = coset x J := coset_inter hx hxi
        have hab : z - x ∈ U := by simpa using U.sub_mem hz'.1 hx
        have hdis : Disjoint (coset z V) (coset x J) := by
          rw [← hUV, ← hJ]
          apply Set.disjoint_left.mpr
          intro y hyk hyi
          obtain ⟨l,_,hl⟩ := cover y
          exact hi ((hl i hyi.2).trans (hl k hyk.2).symm)
        have hdrop := finrank_sub_inf_lt_of_disjoint_translates hV (inf_le_left : J ≤ U) hab
          (by simpa only [translated_coset] using hdis)
        have hh : V ⊓ J = V ⊓ W i := by
          change V ⊓ (U ⊓ W i) = V ⊓ W i
          rw [← inf_assoc, inf_eq_left.mpr hV]
        rw [inf_comm J V,hh] at hdrop
        have hr : rk (V ⊓ W i) ≤ rk V := Submodule.finrank_mono inf_le_left
        have hJrk : rk J ≤ rk U := Submodule.finrank_mono inf_le_left
        change rk J - rk (V ⊓ W i) < rk U - rk V at hdrop
        change rk V - rk (V ⊓ W i) < rk U - rk J
        omega
    exact (hdepth x d i hx hrun).trans (add_potential_le hstrict hsmall hlog)
termination_by rk U
decreasing_by exact hrank

end QueryStrategy
end PCX360

namespace PCX360

noncomputable section PathSemantics
open BooleanCoordinates

def evalQuery {n : ℕ} (q : Query n) (x : E n) : Bool := bitEquiv.symm (q x)

theorem eval_eq {n : ℕ} (q : Query n) (x : E n) (v : Bool) :
    evalQuery q x = v ↔ q x = bit v := by
  exact (bitEquiv.symm.apply_eq_iff_eq_symm_apply)

private theorem at_path {n m : ℕ} {C : Fin m → Set (E n)} {a U t} (ht : Valid C a U t)
    {p : List Bool} {u : Tree n m} (hp : t.subtree p = some u) :
    ∃ b V, Valid C b V u ∧ rk V + p.length = rk U ∧
      ∀ x, x ∈ coset b V ↔ x ∈ coset a U ∧ t.restrict evalQuery p x := by
  induction ht generalizing p u with
  | leaf h =>
    cases p with
    | nil => cases hp; exact ⟨_,_,.leaf h, by simp, fun x => by simp [PTree.restrict]⟩
    | cons _ _ => simp [PTree.subtree] at hp
  | branch hr h₀ h₁ hl hh ihl ihr =>
    cases p with
    | nil => cases hp; exact ⟨_,_,.branch hr h₀ h₁ hl hh, by simp, fun x => by simp [PTree.restrict]⟩
    | cons v p =>
      cases v
      · obtain ⟨b,V,hV,he,hs⟩ := ihl hp
        refine ⟨b,V,hV,by simp only [List.length_cons]; omega, fun x => ?_⟩
        simpa only [PTree.restrict, eval_eq, bit_false, Bool.false_eq_true, if_false, and_assoc] using
          (hs x).trans (by rw [h₀]; exact and_assoc)
      · obtain ⟨b,V,hV,he,hs⟩ := ihr hp
        refine ⟨b,V,hV,by simp only [List.length_cons]; omega, fun x => ?_⟩
        simpa only [PTree.restrict, eval_eq, bit_true, if_true, and_assoc] using
          (hs x).trans (by rw [h₁]; exact and_assoc)

theorem run_at_leaf {n m : ℕ} (t : Tree n m) {p : List Bool} {i : Fin m} {x : E n}
    (ht : t.subtree p = some (.leaf i)) (hx : t.restrict evalQuery p x) : Run x t p.length i := by
  induction t generalizing p with
  | leaf k =>
    cases p with
    | nil => cases ht; exact .leaf i
    | cons _ _ => simp [PTree.subtree] at ht
  | branch q l r ihl ihr =>
    cases p with
    | nil => simp [PTree.subtree] at ht
    | cons v p =>
      cases v
      · exact .left ((eval_eq _ _ _).1 hx.1) (ihl ht hx.2)
      · exact .right ((eval_eq _ _ _).1 hx.1) (ihr ht hx.2)

theorem leaves_unique {Q I X : Type} (eval : Q → X → Bool) (t : PTree Q I)
    {p s : List Bool} {i j : I} (hp : t.subtree p = some (.leaf i))
    (hs : t.subtree s = some (.leaf j)) (x : X)
    (hxp : t.restrict eval p x) (hxs : t.restrict eval s x) : p = s := by
  induction t generalizing p s with
  | leaf k => cases p <;> cases s <;> simp_all [PTree.subtree]
  | branch q l r ihl ihr =>
    cases p with
    | nil => simp [PTree.subtree] at hp
    | cons b p =>
      cases s with
      | nil => simp [PTree.subtree] at hs
      | cons c s =>
        have hc : b = c := hxp.1.symm.trans hxs.1
        subst c
        cases b
        · exact congrArg (List.cons false) (ihl hp hs hxp.2 hxs.2)
        · exact congrArg (List.cons true) (ihr hp hs hxp.2 hxs.2)

end PathSemantics
end PCX360

namespace PCX360

noncomputable section LeafCounting

private theorem count_leaves {n m : ℕ} (t : Tree n m) (dflt : Fin m) (i : Fin m)
    (D : List Bool → Set (E n)) (C : Set (E n)) (c B : ℕ) (hB : B ≤ n)
    (hC : (enum C).card = 2 ^ (n-c))
    (hdom : ∀ p ∈ (t.nodes \ t.inner).filter (fun p => t.out dflt p = i),
      p.length ≤ B ∧ (enum (D p)).card = 2 ^ (n-p.length) ∧ D p ⊆ C ∧
      ∀ x ∈ D p, t.restrict evalQuery p x) :
    ((t.nodes \ t.inner).filter (fun p => t.out dflt p = i)).card ≤ 2 ^ (B-c) := by
  classical
  let L := (t.nodes \ t.inner).filter (fun p => t.out dflt p = i)
  have hpair : (L : Set (List Bool)).PairwiseDisjoint (fun p => enum (D p)) := by
    intro p hp s hs hne
    apply Finset.disjoint_left.mpr
    intro x hxp hxs
    have hp' : p ∈ t.nodes \ t.inner := (Finset.mem_filter.mp hp).1
    have hs' : s ∈ t.nodes \ t.inner := (Finset.mem_filter.mp hs).1
    exact hne (leaves_unique evalQuery t (t.subtree_eq_out_of_mem_leaves dflt hp')
      (t.subtree_eq_out_of_mem_leaves dflt hs') x ((hdom p hp).2.2.2 x (mem_enum.mp hxp))
      ((hdom s hs).2.2.2 x (mem_enum.mp hxs)))
  have hsub : L.biUnion (fun p => enum (D p)) ⊆ enum C := by
    intro x hx
    obtain ⟨p,hp,hx⟩ := Finset.mem_biUnion.mp hx
    exact mem_enum.mpr ((hdom p hp).2.2.1 (mem_enum.mp hx))
  have hmul : L.card * 2 ^ (n-B) ≤ 2 ^ (n-c) := by
    calc
      L.card * 2 ^ (n-B) = ∑ _p ∈ L, 2 ^ (n-B) := by simp
      _ ≤ ∑ p ∈ L, (enum (D p)).card := by
        apply Finset.sum_le_sum
        intro p hp
        rw [(hdom p hp).2.1]
        exact pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (Nat.sub_le_sub_left (hdom p hp).1 n)
      _ = (L.biUnion (fun p => enum (D p))).card := (Finset.card_biUnion hpair).symm
      _ ≤ 2 ^ (n-c) := hC ▸ Finset.card_le_card hsub
  have he : n-c ≤ (B-c) + (n-B) := by omega
  have hmul' := hmul.trans (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) he)
  rw [pow_add] at hmul'
  exact Nat.le_of_mul_le_mul_right hmul' (by positivity)

end LeafCounting
end PCX360

end Base

open PEqualNP.Outside.L_pcx_361_aux.Base
open PEqualNP.Outside.L_pcx_361_aux.Base.PCX360
open PEqualNP.Outside.L_pcx_361_aux.Base.BooleanCoordinates

theorem partition :
  ∀ (n m : ℕ) (cells : Fin m → Finset (PEqualNP.ProofComplexity.LinEq (Fin n)))
      (c : Fin m → ℕ),
    let X := Fin n → Bool
    let inside : Fin m → X → Bool := fun i x => decide (((cells i).filter (fun e =>
      decide ((e.1.filter (fun v => x v)).card % 2 = 1) ≠ e.2)).card = 0)
    let budget := fun i : Fin m =>
      min n (∑ j ∈ Finset.range (c i), min (j+1) (Nat.log 2 m))
    (∀ x : X, ∃! i : Fin m, inside i x) →
    (∀ i, 2^(c i) * ((Finset.univ : Finset X).filter (fun x => inside i x = true)).card = 2^n) →
    ∃ (t : PTree (Query n) (Fin m)) (default : Fin m),
      (∀ p ∈ t.nodes \ t.inner,∀ x : X,
        t.restrict evalQuery p (vector x) → inside (t.out default p) x) ∧
      ∀ i, ((t.nodes \ t.inner).filter (fun p => t.out default p = i)).card ≤ 2^(budget i - c i) := by
  classical
  dsimp only
  intro n m cells c hpart hsize
  let C := fun i : Fin m => cellSet (cells i)
  have hC (i : Fin m) (x : Fin n → Bool) :
      insideBool (cells i) x = true ↔ vector x ∈ C i := insideBool_iff _ _
  have hcsize (i : Fin m) : 2^(c i) * (enum (C i)).card = 2^n := by
    rw [← card_vector _ _ (hC i)]
    exact hsize i
  have hex (i : Fin m) : ∃ a, a ∈ C i := by
    have hne : (enum (C i)).card ≠ 0 := by
      intro hz
      have := hcsize i
      rw [hz, mul_zero] at this
      exact (by positivity : 0 < (2 : ℕ)^n).ne this
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    exact ⟨a,mem_enum.mp ha⟩
  choose A hA using hex
  let W := fun i : Fin m => cellDir (cells i)
  have hcos (i : Fin m) : C i = coset (A i) (W i) := cell_coset _ (hA i)
  have hcovC (x : E n) : ∃! i, x ∈ C i := by
    let y := (vectorEquiv n).symm x
    have hy : vector y = x := (vectorEquiv n).apply_symm_apply x
    obtain ⟨i,hi,hu⟩ := hpart y
    exact ⟨i,hy ▸ (hC i y).mp hi,fun j hj => hu j ((hC j y).mpr (hy ▸ hj))⟩
  have hcov (x : E n) : ∃! i, x ∈ coset (A i) (W i) := by
    simpa only [← hcos] using hcovC x
  obtain ⟨default,_,_⟩ := hcov 0
  have hcod (i : Fin m) : c i + rk (W i) = n := by
    have hm := hcsize i
    rw [hcos, card_coset, ← pow_add] at hm
    exact (pow_right_injective₀ (by decide : (0 : ℕ) < 2) (by decide : (2 : ℕ) ≠ 1)) hm
  have hcard (i : Fin m) : (enum (C i)).card = 2 ^ (n-c i) := by
    rw [hcos, card_coset]
    have hh := hcod i
    congr 1
    omega
  obtain ⟨t,ht,hdep⟩ := strategy A W hcov 0 ⊤
  have ht' : Valid C 0 ⊤ t := by simpa only [← hcos] using ht
  let B := fun i : Fin m => min n (potential m (c i))
  let ask := fun p => support (t.ask 0 p)
  let out := t.out default
  have htop (x : E n) : x ∈ coset 0 (⊤ : Dir n) := by simp [mem_coset]
  have hrel (i : Fin m) : rel (⊤ : Dir n) (W i) = c i := by
    rw [rel, top_inf_eq, rk_top]
    have hh := hcod i
    omega
  have hpath (p : List Bool) (hp : p ∈ t.nodes) :
      ∃ b V u, t.subtree p = some u ∧ Valid C b V u ∧ rk V + p.length = n ∧
        ∀ x, x ∈ coset b V ↔ t.restrict evalQuery p x := by
    obtain ⟨u,hu⟩ := (t.mem_nodes_iff p).mp hp
    obtain ⟨b,V,hv,hr,hs⟩ := at_path ht' hu
    exact ⟨b,V,u,hu,hv,by simpa only [rk_top] using hr,
      fun x => (hs x).trans (and_iff_right (htop x))⟩
  let S := fun p => {x : E n | t.restrict evalQuery p x}
  have hpath_card (p : List Bool) (hp : p ∈ t.nodes) :
      p.length ≤ n ∧ (enum (S p)).card = 2^(n-p.length) := by
    obtain ⟨b,V,u,hu,hv,hr,hs⟩ := hpath p hp
    have he : S p = coset b V := Set.ext fun x => (hs x).symm
    rw [he, card_coset]
    refine ⟨by omega, ?_⟩
    congr 1
    omega
  have hleaf (p : List Bool) (hp : p ∈ t.nodes \ t.inner) :
      p.length ≤ B (out p) ∧ S p ⊆ C (out p) := by
    have hp' := (Finset.mem_sdiff.mp hp).1
    have hu := t.subtree_eq_out_of_mem_leaves default hp
    obtain ⟨b,V,u,he,hv,hr,hs⟩ := hpath p hp'
    rw [hu] at he
    cases he
    have hsub : coset b V ⊆ C (out p) := by cases hv; assumption
    have hrun := run_at_leaf t hu ((hs b).mp (self_mem_coset b V))
    have hdb := hdep b p.length (out p) (htop b) hrun
    rw [hrel] at hdb
    exact ⟨le_min (by omega) hdb, fun ⦃x⦄ hx => hsub ((hs x).mpr hx)⟩
  let e := fun (q : Query n) (x : Fin n → Bool) =>
    decide (((support q).filter fun v => x v).card % 2 = 1)
  have hev (q : Query n) (x : Fin n → Bool) : e q x = evalQuery q (vector x) :=
    (query_bit q x _).mp ((eval_eq q (vector x) _).mp rfl)
  have hfollow (p : List Bool) (hp : p ∈ t.nodes) (x : Fin n → Bool) :
      t.follows e 0 p x = true ↔ vector x ∈ S p := by
    rw [PTree.follows_eq_true_iff]
    change (∀ j : Fin p.length, e (t.ask 0 (p.take j.val)) x = p.get j) ↔ _
    simp only [hev]
    exact (t.follows_eq_true_iff evalQuery 0 p (vector x)).symm.trans
      (t.follows_iff_restrict evalQuery 0 hp (vector x))
  refine ⟨t,default,?_,?_⟩
  · intro p hp x hx
    exact (hC _ _).mpr ((hleaf p hp).2 hx)
  · intro i
    exact count_leaves t default i S (C i) (c i) (B i) (min_le_left _ _) (hcard i)
      (fun p hp => by
        obtain ⟨hpl, hpi⟩ := Finset.mem_filter.mp hp
        have hh := hleaf p hpl
        rw [show out p = i from hpi] at hh
        exact ⟨hh.1,(hpath_card p (Finset.mem_sdiff.mp hpl).1).2,hh.2,fun _ hx => hx⟩)

open PEqualNP.ProofComplexity Base Base.BooleanCoordinates Base.PCX360

variable {V W : Type} [DecidableEq V] [DecidableEq W]

abbrev img (project : LinEq V → LinEq W) (L : LinKLine V) : LinKLine W :=
  L.image (fun T => T.image project)

theorem width_img (project : LinEq V → LinEq W) {k : ℕ} {L : LinKLine V}
    (h : ∀ T ∈ L, T.card ≤ k) : ∀ T ∈ img project L, T.card ≤ k := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
  exact Finset.card_image_le.trans (h S hS)

theorem weak_sub {L M : LinKLine W} (h : L ⊆ M) : IsLinKWeakening L M :=
  fun T hT => Or.inl ⟨T, h hT, fun _ ha => ha⟩

theorem termSat_img (project : LinEq V → LinEq W) (extend : (W → Bool) → V → Bool)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) (a : W → Bool)
    (T : LinTerm V) : LinTermSat a (T.image project) ↔ LinTermSat (extend a) T := by
  constructor
  · intro h e he
    exact (hsat a e).1 (h _ (Finset.mem_image_of_mem _ he))
  · intro h q hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hq
    exact (hsat a e).2 (h e he)

theorem sat_single (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a (({v} : Finset V), s) ↔ a v = s := by
  cases h : a v <;> cases s <;> simp [LinEqSat, h, Finset.filter_singleton]

theorem cut_img (project : LinEq V → LinEq W)
    (hneg : ∀ e, project (negLinEq e) = negLinEq (project e)) {C D R : LinKLine V}
    (h : IsLinKCut C D R) :
    ∃ R', IsLinKCut (img project C) (img project D) R' ∧ R' ⊆ img project R := by
  obtain ⟨T, hT, hD, rfl⟩ := h
  refine ⟨(img project C).erase (T.image project) ∪ (img project D \
    (T.image project).image (fun e => ({negLinEq e} : LinTerm W))),
    ⟨T.image project, Finset.mem_image_of_mem _ hT, ?_, rfl⟩, ?_⟩
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.1 he
    have h1 : ({negLinEq e0} : LinTerm V).image project = {negLinEq (project e0)} := by
      rw [Finset.image_singleton, hneg]
    rw [← h1]
    exact Finset.mem_image_of_mem (fun T : LinTerm V => T.image project) (hD e0 he0)
  · intro S hS
    rcases Finset.mem_union.1 hS with h1 | h1
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 h1
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _ (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hUT, hU⟩))
    · obtain ⟨hS, hn⟩ := Finset.mem_sdiff.1 h1
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      refine Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hU, ?_⟩))
      intro hU'
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hU'
      apply hn
      refine Finset.mem_image.2 ⟨project e, Finset.mem_image_of_mem _ he, ?_⟩
      rw [Finset.image_singleton, hneg]

theorem and_img (project : LinEq V → LinEq W) {C D R : LinKLine V}
    (h : IsLinKAndIntro C D R) :
    ∃ R', IsLinKAndIntro (img project C) (img project D) R' ∧ R' ⊆ img project R := by
  obtain ⟨T₁, T₂, h1, h2, rfl⟩ := h
  refine ⟨((img project C).erase (T₁.image project) ∪ (img project D).erase (T₂.image project))
    ∪ {T₁.image project ∪ T₂.image project},
    ⟨_, _, Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2, rfl⟩, ?_⟩
  intro S hS
  rcases Finset.mem_union.1 hS with hS | hS
  · rcases Finset.mem_union.1 hS with hS | hS
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 hS
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T₁ := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hUT, hU⟩)))
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 hS
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T₂ := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hUT, hU⟩)))
  · rw [Finset.mem_singleton.1 hS, ← Finset.image_union]
    exact Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))

theorem weak_img (project : LinEq V → LinEq W) (extend : (W → Bool) → V → Bool)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) {L M : LinKLine V}
    (h : IsLinKWeakening L M) : IsLinKWeakening (img project L) (img project M) := by
  intro T' hT'
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hT'
  rcases h T hT with ⟨S, hS, hTS⟩ | hq
  · exact Or.inl ⟨S.image project, Finset.mem_image_of_mem _ hS, fun a ha =>
      (termSat_img project extend hsat a S).2 (hTS _ ((termSat_img project extend hsat a T).1 ha))⟩
  · right
    intro a ha
    obtain ⟨q, hq1, hq2⟩ := hq _ ((termSat_img project extend hsat a T).1 ha)
    refine ⟨project q, ?_, (hsat a q).2 hq2⟩
    rw [show ({project q} : LinTerm W) = ({q} : LinTerm V).image project from
      (Finset.image_singleton _ _).symm]
    exact Finset.mem_image_of_mem (fun T : LinTerm V => T.image project) hq1

open Base.BooleanCoordinates Base.PCX360
abbrev Eqn (n : Nat) := LinEq (Fin n)
abbrev Word (n : Nat) := Fin n → Bool
def parity {n} (S : Finset (Fin n)) (z : Word n) : Bool := decide ((S.filter (fun v=>z v)).card % 2=1)
def chartEmb {n d} (h : Fin n→Eqn d) (z : Word d) : Word n := fun j=>parity (h j).1 z == (h j).2

theorem eq_sat_iff {n} (z : Word n) (e : Eqn n) : LinEqSat z e ↔ parity e.1 z=e.2 := by
  rcases e with ⟨s,b⟩
  cases b <;> simp [LinEqSat, parity, Nat.odd_iff]

theorem vec_par {n} (s : Finset (Fin n)) (x : Word n) : eqQuery s (vector x)=bit (parity s x) := by
  apply (query_bit _ _ _).mpr
  rw [eqQuery_support]; rfl

theorem eq_sat_vec {n} (z : Word n) (e : Eqn n) : LinEqSat z e ↔ eqQuery e.1 (vector z)=bit e.2 := by
  rw [eq_sat_iff, vec_par]
  exact bitEquiv.injective.eq_iff.symm

def offset {n d} (h : Fin n→Eqn d) : E n := fun j=>if (h j).2 then 0 else 1
noncomputable def chartMap {n d} (h : Fin n→Eqn d) : E d→ₗ[F] E n := LinearMap.pi fun j=>eqQuery (h j).1
theorem bit_beq (a b : Bool) : bit (a==b)=bit a+(if b then 0 else 1) := by cases a <;> cases b <;> decide
theorem chart_vector {n d} (h : Fin n→Eqn d) (z : Word d) :
    vector (chartEmb h z) = chartMap h (vector z)+offset h := by
  ext j; change bit (parity (h j).1 z == (h j).2) = eqQuery (h j).1 (vector z)+_
  rw [vec_par,bit_beq]; rfl
theorem chart_inj {n d} (h : Fin n→Eqn d) (hi : Function.Injective (chartEmb h)) :
    Function.Injective (chartMap h) := by
  intro x y he
  obtain ⟨u,rfl⟩ := (vectorEquiv d).surjective x
  obtain ⟨v,rfl⟩ := (vectorEquiv d).surjective y
  apply congrArg _
  apply hi; apply (vectorEquiv n).injective
  change vector (chartEmb h u)=vector (chartEmb h v)
  rw [chart_vector,chart_vector]; exact congrArg (· + offset h) he

theorem bit_toggle (b : Bool) (a : F) :
    bitEquiv.symm (bit (!b)+a) = !(bitEquiv.symm (bit b+a)) := by
  have two : ∀v : F,v=0 ∨ v=1 := by decide
  rcases two a with rfl|rfl <;> cases b <;> decide

theorem chart_pullback {n d} (h : Fin n→Eqn d) (hi : Function.Injective (chartEmb h)) :
    ∃ (P : Eqn d→Eqn n) (ext : Word n→Word d),
      (∀e,P (negLinEq e)=negLinEq (P e)) ∧
      (∀a e,LinEqSat a (P e) ↔ LinEqSat (ext a) e) ∧ ∀z,ext (chartEmb h z)=z := by
  classical
  obtain ⟨R,left⟩ := LinearMap.exists_leftInverse_of_injective (chartMap h)
    (LinearMap.ker_eq_bot.mpr (chart_inj h hi))
  let extn := fun a : Word n=>(vectorEquiv d).symm (R (vector a-offset h))
  let L := fun s : Finset (Fin d)=>(eqQuery s).comp R
  let P := fun e : Eqn d=>(support (L e.1),bitEquiv.symm (bit e.2+(L e.1) (offset h)))
  refine ⟨P,extn,?_,?_,?_⟩
  · intro e; exact Prod.ext rfl (bit_toggle _ _)
  · intro a e
    rw [eq_sat_iff, eq_sat_vec]
    change parity (support (L e.1)) a=bitEquiv.symm _ ↔ _
    have hh := query_bit (L e.1) a (bitEquiv.symm (bit e.2+L e.1 (offset h)))
    change _ ↔ parity _ _=_ at hh
    rw [←hh]
    have eb : bit (bitEquiv.symm (bit e.2+L e.1 (offset h)))=_ := bitEquiv.apply_symm_apply _
    rw [eb]
    have ee : vector (extn a)=R (vector a-offset h) := (vectorEquiv d).apply_symm_apply _
    rw [ee]
    change (L e.1) (vector a)=bit e.2+(L e.1) (offset h) ↔ (L e.1) (vector a-offset h)=bit e.2
    rw [map_sub]; exact sub_eq_iff_eq_add.symm
  · intro z; apply (vectorEquiv d).injective
    change vectorEquiv d ((vectorEquiv d).symm _)=_
    rw [Equiv.apply_symm_apply,chart_vector,add_sub_cancel_right]
    exact DFunLike.congr_fun left (vector z)

def escape {n} (s : Finset (Eqn n)) : LinKLine (Fin n) := s.image fun e=>({negLinEq e} : LinTerm (Fin n))
def markedAx {n d} (h : Fin n→Eqn d) (C : Clause (Fin n)) : LinKLine (Fin d) :=
  C.image (fun l=>({(if l.2 then h l.1 else negLinEq (h l.1))} : LinTerm (Fin d)))

theorem inside_eq_sat {n} (s : Finset (Eqn n)) (a : Word n) :
    insideBool s a = true ↔ ∀e∈s,LinEqSat a e := by
  simp only [insideBool,decide_eq_true_eq,Finset.card_eq_zero,Finset.filter_eq_empty_iff,not_ne_iff,eq_sat_iff]
  rfl
theorem neg_sat_iff {n} (a : Word n) (e : Eqn n) : LinEqSat a (negLinEq e) ↔ ¬LinEqSat a e := by
  rw [eq_sat_iff,eq_sat_iff]
  change parity e.1 a = !e.2 ↔ _
  cases parity e.1 a <;> cases e.2 <;> decide
theorem marked_sat {n d} (h : Fin n→Eqn d) (j : Fin n) (b : Bool) (z : Word d) :
    LinEqSat z (if b then h j else negLinEq (h j)) ↔ chartEmb h z j=b := by
  cases b
  · change LinEqSat z (negLinEq (h j)) ↔ (parity (h j).1 z == (h j).2)=false
    rw [neg_sat_iff,eq_sat_iff]
    cases parity (h j).1 z <;> cases (h j).2 <;> decide
  · change LinEqSat z (h j) ↔ (parity (h j).1 z == (h j).2)=true
    rw [eq_sat_iff]; simp

abbrev liftL (P : LinEq V → LinEq W) (G : LinKLine W) (L : LinKLine V) := img P L ∪ G

theorem cut_union (G : LinKLine W) {C D R : LinKLine W} (h : IsLinKCut C D R) :
    ∃ U, IsLinKCut (C∪G) (D∪G) U ∧ U ⊆ R∪G := by
  obtain ⟨T,hT,ha,rfl⟩ := h
  refine ⟨_,⟨T,Finset.mem_union_left _ hT,(fun e he=>Finset.mem_union_left _ (ha e he)),rfl⟩,?_⟩
  intro s hs
  simp only [Finset.mem_union,Finset.mem_erase,Finset.mem_sdiff] at hs ⊢
  tauto

theorem and_union (G : LinKLine W) {C D R : LinKLine W} (h : IsLinKAndIntro C D R) :
    ∃ U, IsLinKAndIntro (C∪G) (D∪G) U ∧ U ⊆ R∪G := by
  obtain ⟨T,S,hT,hS,rfl⟩ := h
  refine ⟨_,⟨T,S,Finset.mem_union_left _ hT,Finset.mem_union_left _ hS,rfl⟩,?_⟩
  intro u hu
  simp only [Finset.mem_union,Finset.mem_erase] at hu ⊢
  tauto

theorem weak_union (G : LinKLine W) {C D : LinKLine W} (h : IsLinKWeakening C D) :
    IsLinKWeakening (C∪G) (D∪G) := by
  intro T ht
  rcases Finset.mem_union.mp ht with ht|ht
  · rcases h T ht with ⟨S,hs,hh⟩|hh
    · exact Or.inl ⟨S,Finset.mem_union_left _ hs,hh⟩
    · right; intro a ha
      obtain ⟨q,hq,ea⟩ := hh a ha
      exact ⟨q,Finset.mem_union_left _ hq,ea⟩
  · exact Or.inl ⟨T,Finset.mem_union_right _ ht,fun _ h=>h⟩

theorem lift_deriv {k : ℕ} (hk : 1≤k) (P : LinEq V→LinEq W)
    (neg : ∀e,P (negLinEq e)=negLinEq (P e)) (extend : (W→Bool)→V→Bool)
    (sat : ∀a e,LinEqSat a (P e) ↔ LinEqSat (extend a) e)
    (G : LinKLine W) (gw : ∀T∈G,T.card≤k)
    (F : Set (Clause W)) (axi : Clause W→LinKLine V)
    (aw : ∀C∈F,IsLinKWeakening (linKOfClause C) (liftL P G (axi C)))
    {π} (der : IsLinKDerivation k IsLinKWeakening (axi '' F) π) {seed}
    (dseed : IsLinKDerivation k IsLinKWeakening (linKOfClause '' F) seed) :
    ∃ τ : List (LinKLine W), IsLinKDerivation k IsLinKWeakening (linKOfClause '' F) (τ++seed) ∧
      τ.length≤2*π.length ∧ ∀L∈π,liftL P G L ∈ τ++seed := by
  have wd (L : LinKLine V) (h : ∀T∈L,T.card≤k) : ∀T∈liftL P G L,T.card≤k := by
    intro T ht
    rcases Finset.mem_union.mp ht with ht|ht
    · exact width_img P h T ht
    · exact gw _ ht
  induction der with
  | nil => exact ⟨[],dseed,by simp,by simp⟩
  | @ax π C _ hC hw ih =>
    obtain ⟨τ,dt,len,mem⟩ := ih
    obtain ⟨D,hD,rfl⟩ := hC
    have wa (T) (ht:T∈linKOfClause D) : T.card≤k := by
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ht
      simpa using hk
    refine ⟨liftL P G (axi D)::linKOfClause D::τ,
      .weak (.ax dt ⟨D,hD,rfl⟩ wa) (List.mem_cons_self) (aw D hD) (wd _ hw),?_,?_⟩
    · simp only [List.length_cons]; omega
    · intro L h; rcases List.mem_cons.mp h with rfl|h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem _ h))
  | @cut π C D R _ hC hD hcut hw ih =>
    obtain ⟨τ,dt,len,mem⟩ := ih
    obtain ⟨R',hr,sub⟩ := cut_img P neg hcut
    obtain ⟨U,hu,su⟩ := cut_union G hr
    have ss : U⊆liftL P G R := su.trans (Finset.union_subset_union sub (Finset.Subset.refl G))
    refine ⟨liftL P G R::U::τ,.weak (.cut dt (mem _ hC) (mem _ hD) hu (fun T ht=>wd _ hw T (ss ht)))
      List.mem_cons_self (weak_sub ss) (wd _ hw),?_,?_⟩
    · simp only [List.length_cons]; omega
    · intro L h; rcases List.mem_cons.mp h with rfl|h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem _ h))
  | @andIntro π C D R _ hC hD hand hw ih =>
    obtain ⟨τ,dt,len,mem⟩ := ih
    obtain ⟨R',hr,sub⟩ := and_img P hand
    obtain ⟨U,hu,su⟩ := and_union G hr
    have ss : U⊆liftL P G R := su.trans (Finset.union_subset_union sub (Finset.Subset.refl G))
    refine ⟨liftL P G R::U::τ,.weak (.andIntro dt (mem _ hC) (mem _ hD) hu (fun T ht=>wd _ hw T (ss ht)))
      List.mem_cons_self (weak_sub ss) (wd _ hw),?_,?_⟩
    · simp only [List.length_cons]; omega
    · intro L h; rcases List.mem_cons.mp h with rfl|h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem _ h))
  | @weak π C D _ hC hW hw ih =>
    obtain ⟨τ,dt,len,mem⟩ := ih
    refine ⟨liftL P G D::τ,.weak dt (mem _ hC) (weak_union G (weak_img P extend sat hW)) (wd _ hw),?_,?_⟩
    · simp only [List.length_cons]; omega
    · intro L h; rcases List.mem_cons.mp h with rfl|h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem _ h)

def singleLine {n} (B : Finset (Eqn n)) : LinKLine (Fin n) := B.image fun e=>({e} : LinTerm (Fin n))
theorem single_width {n k} (hk : 1≤k) (B : Finset (Eqn n)) (T) (ht:T∈singleLine B) : T.card≤k := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ht; simpa using hk
theorem escape_weak {n} (s B : Finset (Eqn n))
    (imp : ∀a : Word n,(∀q∈B,¬LinEqSat a q) → insideBool s a=true) :
    IsLinKWeakening (escape s) (singleLine B) := by
  classical
  intro T ht; obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ht
  right; intro a ha
  by_contra! bad
  have yes := (inside_eq_sat s a).mp (imp a (fun q hq=>bad q (Finset.mem_image_of_mem (fun z=>({z} : LinTerm (Fin n))) hq)))
  exact (neg_sat_iff a e).mp (ha _ (Finset.mem_singleton_self _)) (yes e he)

theorem cut_prefix {n} (B : Finset (Eqn n)) (e : Eqn n) :
    IsLinKCut (singleLine (insert e B)) (singleLine (insert (negLinEq e) B)) (singleLine B) := by
  classical
  refine ⟨{e},by simp [singleLine],?_,?_⟩
  · intro u hu; obtain rfl := Finset.mem_singleton.mp hu; simp [singleLine]
  · ext T
    have diff : ({e} : LinTerm (Fin n))≠{negLinEq e} := by
      intro h; have := congrArg Prod.snd (Finset.singleton_injective h)
      rcases e with ⟨s,b⟩; cases b <;> simp [negLinEq] at this
    simp only [singleLine,Finset.image_insert,Finset.image_singleton,Finset.mem_union,Finset.mem_erase,
      Finset.mem_insert,Finset.mem_sdiff,Finset.mem_singleton]
    grind

theorem branch_card {Q I : Type} (q : Q) (l r : PTree Q I) :
    ((PTree.branch q l r).nodes \ (PTree.branch q l r).inner).card =
    (l.nodes \ l.inner).card + (r.nodes \ r.inner).card := by
  classical
  let L := l.nodes \ l.inner
  let R := r.nodes \ r.inner
  have eqs : (PTree.branch q l r).nodes \ (PTree.branch q l r).inner = L.image (false::·) ∪ R.image (true::·) := by
    ext p; cases p with
    | nil => simp [PTree.inner]
    | cons b p => cases b <;> simp [L,R,PTree.mem_nodes_cons_branch,PTree.mem_inner_cons_branch]
  rw [eqs,Finset.card_union_of_disjoint,Finset.card_image_of_injective,Finset.card_image_of_injective]
  · intro p t e; exact (List.cons.inj e).2
  · intro p t e; exact (List.cons.inj e).2
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,h⟩ := Finset.mem_image.mp hy
    simp at h

theorem glue {n m k} (hk : 1≤k) (F0 : Set (Clause (Fin n))) (s : Fin m→Finset (Eqn n))
    (default : Fin m) (t : PTree (Query n) (Fin m)) (B : Finset (Eqn n))
    (imp : ∀p∈t.nodes \ t.inner,∀a : Word n,(∀e∈B,¬LinEqSat a e) →
      t.restrict evalQuery p (vector a) → insideBool (s (t.out default p)) a=true)
    (seed : List (LinKLine (Fin n))) (ds : IsLinKDerivation k IsLinKWeakening (linKOfClause '' F0) seed)
    (hs : ∀i,escape (s i)∈seed) :
    ∃τ : List (LinKLine (Fin n)), IsLinKDerivation k IsLinKWeakening (linKOfClause '' F0) (τ++seed) ∧
      τ.length+1 ≤ 2*(t.nodes \ t.inner).card ∧ singleLine B∈τ++seed := by
  classical
  induction t generalizing B seed with
  | leaf i =>
    have h := escape_weak (s i) B (fun a avoid=>imp [] (by simp [PTree.nodes,PTree.inner]) a avoid trivial)
    refine ⟨[singleLine B],.weak ds (hs i) h (single_width hk _),by simp [PTree.nodes,PTree.inner],by simp⟩
  | branch q l r il ir =>
    let e : Eqn n := (support q,true)
    have ev (a : Word n) (b : Bool) : LinEqSat a (support q,b) ↔ evalQuery q (vector a)=b := by
      rw [eq_sat_iff,eval_eq,query_bit]; rfl
    have left : ∀p∈l.nodes \ l.inner,∀a : Word n,(∀u∈insert e B,¬LinEqSat a u) →
        l.restrict evalQuery p (vector a) → insideBool (s (l.out default p)) a=true := by
      intro p hp a avoid run
      apply imp (false::p) (by simpa [PTree.mem_nodes_cons_branch,PTree.mem_inner_cons_branch] using hp) a
        (fun u hu=>avoid u (Finset.mem_insert_of_mem hu))
      change evalQuery q (vector a)=false ∧ _
      have h := avoid e (Finset.mem_insert_self ..)
      exact ⟨by simpa [e,ev] using h,run⟩
    obtain ⟨u,du,lu,hu⟩ := il (insert e B) left seed ds hs
    have right : ∀p∈r.nodes \ r.inner,∀a : Word n,(∀v∈insert (negLinEq e) B,¬LinEqSat a v) →
        r.restrict evalQuery p (vector a) → insideBool (s (r.out default p)) a=true := by
      intro p hp a avoid run
      apply imp (true::p) (by simpa [PTree.mem_nodes_cons_branch,PTree.mem_inner_cons_branch] using hp) a
        (fun v hv=>avoid v (Finset.mem_insert_of_mem hv))
      change evalQuery q (vector a)=true ∧ _
      have h := avoid (negLinEq e) (Finset.mem_insert_self ..)
      change ¬LinEqSat a (support q,false) at h
      exact ⟨by simpa [ev] using h,run⟩
    obtain ⟨v,dv,lv,hv⟩ := ir _ right (u++seed) du (fun i=>List.mem_append_right _ (hs i))
    refine ⟨singleLine B::(v++u),?_,?_,by simp⟩
    · simp only [List.cons_append,List.append_assoc]
      exact .cut dv (List.mem_append_right _ hu) hv (cut_prefix B e) (single_width hk B)
    · rw [branch_card]; simp only [List.length_cons,List.length_append]; omega

theorem lift_cell {n d k} (hk : 1≤k) (F0 : Set (Clause (Fin n))) (s : Finset (Eqn n))
    (h : Fin n→Eqn d) (hinj : Function.Injective (chartEmb h))
    (cover : ∀a,insideBool s a = true ↔ ∃z,chartEmb h z=a)
    {π : List (LinKLine (Fin d))} (dπ : IsLinKDerivation k IsLinKWeakening (markedAx h '' F0) π)
    (empty : ∅∈π) {seed} (dseed : IsLinKDerivation k IsLinKWeakening (linKOfClause '' F0) seed) :
    ∃ τ : List (LinKLine (Fin n)), IsLinKDerivation k IsLinKWeakening (linKOfClause '' F0) (τ++seed) ∧
    τ.length ≤ 2*π.length ∧ escape s∈τ++seed := by
  classical
  obtain ⟨P,extn,neg,sat,left⟩ := chart_pullback h hinj
  have gw (T) (ht : T∈escape s) : T.card ≤ k := by
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ht; simpa using hk
  have axw (C : Clause (Fin n)) (_ : C ∈ F0) :
      IsLinKWeakening (linKOfClause C) (liftL P (escape s) (markedAx h C)) := by
    intro T ht; right; intro a ha
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hq
    have hlit : a l.1=l.2 := (sat_single a l.1 l.2).mp (ha _ (Finset.mem_singleton_self _))
    by_cases inside : insideBool s a = true
    · obtain ⟨z,rfl⟩ := (cover a).mp inside
      let e := if l.2 then h l.1 else negLinEq (h l.1)
      have he : ({e} : LinTerm (Fin d))∈markedAx h C := Finset.mem_image_of_mem (fun l=>({(if l.2 then h l.1 else negLinEq (h l.1))} : LinTerm (Fin d))) hl
      have hh := Finset.mem_image_of_mem (fun t : LinTerm (Fin d)=>t.image P) he
      simp only [Finset.image_singleton] at hh
      refine ⟨P e,Finset.mem_union_left _ hh,(sat _ _).mpr ?_⟩
      rw [left]; exact (marked_sat h l.1 l.2 z).mpr hlit
    · rw [inside_eq_sat] at inside; push_neg at inside
      obtain ⟨e,he,ne⟩ := inside
      exact ⟨negLinEq e,Finset.mem_union_right _ (Finset.mem_image_of_mem (fun e=>({negLinEq e} : LinTerm (Fin n))) he),
        (neg_sat_iff a e).mpr ne⟩
  obtain ⟨τ,dt,len,mem⟩ := lift_deriv hk P neg extn sat (escape s) gw F0 (markedAx h) axw dπ dseed
  exact ⟨τ,dt,len,by simpa [liftL,img] using mem ∅ empty⟩

theorem collect {n m k} (F0 : Set (Clause (Fin n))) (cells : Fin m→Finset (Eqn n)) (cost : Fin m→ℕ)
    (add : ∀i (seed : List (LinKLine (Fin n))),IsLinKDerivation k IsLinKWeakening (linKOfClause '' F0) seed →
      ∃ τ : List (LinKLine (Fin n)), IsLinKDerivation k IsLinKWeakening (linKOfClause '' F0) (τ++seed) ∧
      τ.length≤2*cost i ∧ escape (cells i)∈τ++seed)
    (S : Finset (Fin m)) : ∃ π : List (LinKLine (Fin n)),IsLinKDerivation k IsLinKWeakening (linKOfClause '' F0) π ∧
      π.length ≤ 2*∑i∈S,cost i ∧ ∀i∈S,escape (cells i)∈π := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨[],.nil,by simp,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨π,dp,len,mem⟩ := ih
    obtain ⟨τ,dt,lt,havei⟩ := add i π dp
    refine ⟨τ++π,dt,?_,?_⟩
    · rw [Finset.sum_insert hi,List.length_append]; omega
    · intro j hj; rcases Finset.mem_insert.mp hj with rfl|hj
      · exact havei
      · exact List.mem_append_right _ (mem _ hj)

end PEqualNP.Outside.L_pcx_361_aux

open PEqualNP.Outside.L_pcx_361_aux in
theorem PEqualNP.Outside.L_pcx_361 : ∀ (n m k : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (cells : Fin m → Finset (PEqualNP.ProofComplexity.LinEq (Fin n))) (c : Fin m → ℕ),
  let X := Fin n → Bool
  let inside : Fin m → X → Bool := fun i x => decide (((cells i).filter (fun e =>
    decide ((e.1.filter (fun v => x v)).card % 2 = 1) ≠ e.2)).card = 0)
  let budget := fun i : Fin m =>
    min n (∑ j ∈ Finset.range (c i), min (j+1) (Nat.log 2 m))
  1 ≤ k → (∀ x : X, ∃! i : Fin m, inside i x) →
  (∀ i, 2^(c i) * ((Finset.univ : Finset X).filter (fun x => inside i x = true)).card = 2^n) →
  ∀ chart : (i : Fin m) → Fin n → PEqualNP.ProofComplexity.LinEq (Fin (n-c i)),
    let embed := fun (i : Fin m) (z : Fin (n-c i) → Bool) (j : Fin n) =>
      decide (((chart i j).1.filter (fun v => z v)).card % 2 = 1) == (chart i j).2
    (∀ i, Function.Injective (embed i) ∧ ∀ x : X, inside i x ↔ ∃ z, embed i z = x) →
    let ax := fun (i : Fin m) (C : PEqualNP.ProofComplexity.Clause (Fin n)) =>
      C.image (fun l => ({(if l.2 then chart i l.1
        else PEqualNP.ProofComplexity.negLinEq (chart i l.1))} :
        PEqualNP.ProofComplexity.LinTerm (Fin (n-c i))))
    ∀ proofs : (i : Fin m) → List (PEqualNP.ProofComplexity.LinKLine (Fin (n-c i))),
      (∀ i, PEqualNP.ProofComplexity.IsLinKDerivation k
        PEqualNP.ProofComplexity.IsLinKWeakening (Set.image (ax i) F) (proofs i) ∧ ∅ ∈ proofs i) →
      ∃ π : List (PEqualNP.ProofComplexity.LinKLine (Fin n)),
        PEqualNP.ProofComplexity.IsLinKRefutation k F π ∧
        π.length ≤ 2*((∑ i, (proofs i).length) + ∑ i, 2^(budget i - c i)) := by
  classical
  dsimp only
  intro n m k F cells c hk part size charts hchart proofs hproof
  let budget := fun i : Fin m=>min n (∑ j ∈ Finset.range (c i),min (j+1) (Nat.log 2 m))
  obtain ⟨t,dflt,leaf,bound⟩ := partition n m cells c part size
  have add (i : Fin m) (seed : List (PEqualNP.ProofComplexity.LinKLine (Fin n)))
      (ds : PEqualNP.ProofComplexity.IsLinKDerivation k PEqualNP.ProofComplexity.IsLinKWeakening (PEqualNP.ProofComplexity.linKOfClause '' F) seed) :=
    lift_cell hk F (cells i) (charts i) (hchart i).1 (hchart i).2 (hproof i).1 (hproof i).2 ds
  obtain ⟨seed,ds,len,esc⟩ := collect F cells (fun i=>(proofs i).length) add Finset.univ
  have hn : (t.nodes \ t.inner).card ≤ ∑ i, 2^(budget i-c i) := by
    calc
      _ = ∑ i : Fin m,((t.nodes \ t.inner).filter (fun p=>t.out dflt p=i)).card :=
        Finset.card_eq_sum_card_fiberwise (fun p hp=>Finset.mem_univ _)
      _ ≤ _ := Finset.sum_le_sum (fun i _=>bound i)
  obtain ⟨τ,dt,lt,mem⟩ := glue hk F cells dflt t ∅ (fun p hp x _ h=>leaf p hp x h) seed ds
    (fun i=>esc i (Finset.mem_univ i))
  refine ⟨τ++seed,⟨dt,by simpa [singleLine] using mem⟩,?_⟩
  change (τ++seed).length ≤ 2*((∑i,(proofs i).length)+∑i,2^(budget i-c i))
  rw [List.length_append]; omega

