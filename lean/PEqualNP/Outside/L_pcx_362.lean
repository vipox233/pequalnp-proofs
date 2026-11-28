import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_pcx_362_aux

def Shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def Queries (V : Type) [AddCommGroup V] [Module (ZMod 2) V] : Set (V → Bool) :=
  {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}

def Reach {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) : Prop :=
  ∀ j : Fin p.length, q (p.take j.val) x = p.get j

def Cert {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
    (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) : Prop :=
  Shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
    Reach q p x → ok x (out p)

def sub (S : Finset (List Bool)) (p : List Bool) : Finset (List Bool) :=
  (S.filter (fun r => r.take p.length = p)).image (fun r => r.drop p.length)

def leafCount (N J : Finset (List Bool)) (p : List Bool) : ℕ :=
  (sub (N \ J) p).card

lemma mem_sub_iff (S : Finset (List Bool)) (p u : List Bool) :
    u ∈ sub S p ↔ p ++ u ∈ S := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨r, hr, rfl⟩
    rcases Finset.mem_filter.mp hr with ⟨hrS, htake⟩
    have hcat : p ++ r.drop p.length = r := by
      calc p ++ r.drop p.length = r.take p.length ++ r.drop p.length := by rw [htake]
        _ = r := List.take_append_drop p.length r
    rw [hcat]
    exact hrS
  · intro h
    refine Finset.mem_image.mpr ⟨p ++ u, Finset.mem_filter.mpr ⟨h, ?_⟩, ?_⟩
    · simp
    · simp

lemma sub_nil (S : Finset (List Bool)) : sub S [] = S := by
  ext u
  simp [mem_sub_iff]

lemma leafCount_nil (N J : Finset (List Bool)) : leafCount N J [] = (N \ J).card := by
  simp [leafCount, sub_nil]

lemma anc_mem_J {N J : Finset (List Bool)} (hS : Shape N J) :
    ∀ (u p : List Bool), p ++ u ∈ N → u ≠ [] → p ∈ J := by
  intro u
  refine List.reverseRecOn u ?_ ?_
  · intro p _ hne
    exact (hne rfl).elim
  · intro u' b ih p hmem _
    have hmem' : (p ++ u') ++ [b] ∈ N := by simpa [List.append_assoc] using hmem
    have hpJ : p ++ u' ∈ J := hS.2.2.1 (p ++ u') b hmem'
    cases u' with
    | nil => simpa using hpJ
    | cons c t => exact ih p (hS.2.1 hpJ) (List.cons_ne_nil c t)

lemma sub_leaf_eq_singleton {N J : Finset (List Bool)} (hS : Shape N J)
    {p : List Bool} (hpN : p ∈ N) (hpJ : p ∉ J) : sub (N \ J) p = {[]} := by
  ext u
  simp only [mem_sub_iff, Finset.mem_singleton, Finset.mem_sdiff]
  constructor
  · rintro ⟨hN, _⟩
    by_contra hne
    exact hpJ (anc_mem_J hS u p hN hne)
  · rintro rfl
    simpa using ⟨hpN, hpJ⟩

lemma leafCount_of_leaf {N J : Finset (List Bool)} (hS : Shape N J)
    {p : List Bool} (hpN : p ∈ N) (hpJ : p ∉ J) : leafCount N J p = 1 := by
  simp [leafCount, sub_leaf_eq_singleton hS hpN hpJ]

lemma sub_card_lt {N J : Finset (List Bool)} (hS : Shape N J)
    {p : List Bool} (hpJ : p ∈ J) (b : Bool) :
    (sub N (p ++ [b])).card < (sub N p).card := by
  have hsub : (sub N (p ++ [b])).image (fun u => b :: u) ⊆ (sub N p).erase [] := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
    rw [mem_sub_iff] at hu
    refine Finset.mem_erase.mpr ⟨List.cons_ne_nil b u, ?_⟩
    rw [mem_sub_iff]
    simpa [List.append_assoc] using hu
  have hinj : Function.Injective (fun u : List Bool => b :: u) :=
    fun _ _ h => (List.cons.inj h).2
  have hle : (sub N (p ++ [b])).card ≤ ((sub N p).erase []).card := by
    rw [← Finset.card_image_of_injective (sub N (p ++ [b])) hinj]
    exact Finset.card_le_card hsub
  have hnil : [] ∈ sub N p := by
    rw [mem_sub_iff]
    simpa using hS.2.1 hpJ
  exact lt_of_le_of_lt hle (Finset.card_erase_lt_of_mem hnil)

lemma leafCount_internal {N J : Finset (List Bool)}
    {p : List Bool} (hpJ : p ∈ J) :
    leafCount N J p = leafCount N J (p ++ [false]) + leafCount N J (p ++ [true]) := by
  let S0 := (sub (N \ J) (p ++ [false])).image (fun u => false :: u)
  let S1 := (sub (N \ J) (p ++ [true])).image (fun u => true :: u)
  have heq : sub (N \ J) p = S0 ∪ S1 := by
    ext u
    cases u with
    | nil =>
      simp only [S0, S1, mem_sub_iff, Finset.mem_union, Finset.mem_image, List.append_nil,
        Finset.mem_sdiff, reduceCtorEq, and_false, exists_false, or_self, iff_false, not_and]
      intro _
      exact not_not.mpr hpJ
    | cons c t =>
      cases c
      · simp only [S0, S1, mem_sub_iff, Finset.mem_union, Finset.mem_image, List.cons.injEq,
          true_and, false_and, exists_false, or_false, exists_eq_right, reduceCtorEq]
        simp [List.append_assoc]
      · simp only [S0, S1, mem_sub_iff, Finset.mem_union, Finset.mem_image, List.cons.injEq,
          true_and, false_and, exists_false, false_or, exists_eq_right, reduceCtorEq]
        simp [List.append_assoc]
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro v hv0 hv1
    rcases Finset.mem_image.mp hv0 with ⟨u0, _, rfl⟩
    rcases Finset.mem_image.mp hv1 with ⟨u1, _, h⟩
    exact Bool.false_ne_true (List.cons.inj h).1.symm
  have hinj0 : Function.Injective (fun u : List Bool => false :: u) :=
    fun _ _ h => (List.cons.inj h).2
  have hinj1 : Function.Injective (fun u : List Bool => true :: u) :=
    fun _ _ h => (List.cons.inj h).2
  unfold leafCount
  rw [heq, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinj0, Finset.card_image_of_injective _ hinj1]

lemma leafCount_pos {N J : Finset (List Bool)} (hS : Shape N J) :
    ∀ c p, (sub N p).card = c → p ∈ N → 1 ≤ leafCount N J p := by
  intro c
  refine Nat.strongRecOn c ?_
  intro c ih p hcard hpN
  by_cases hpJ : p ∈ J
  · have hlt : (sub N (p ++ [false])).card < c := by
      rw [← hcard]
      exact sub_card_lt hS hpJ false
    have hpos := ih (sub N (p ++ [false])).card hlt (p ++ [false]) rfl (hS.2.2.2 p hpJ).1
    rw [leafCount_internal hpJ]
    omega
  · rw [leafCount_of_leaf hS hpN hpJ]

lemma reach_nil {V : Type} (q : List Bool → V → Bool) (x : V) : Reach q [] x :=
  fun j => Fin.elim0 j

lemma reach_snoc {V : Type} {q : List Bool → V → Bool} {p : List Bool} {x : V} {b : Bool}
    (hr : Reach q p x) (hq : q p x = b) : Reach q (p ++ [b]) x := by
  intro j
  have hj : j.val < p.length + 1 := by simpa using j.isLt
  by_cases hlt : j.val < p.length
  · have htake : (p ++ [b]).take j.val = p.take j.val :=
      List.take_append_of_le_length (Nat.le_of_lt hlt)
    have hget : (p ++ [b]).get j = p.get ⟨j.val, hlt⟩ := by
      simp [List.get_eq_getElem, List.getElem_append_left hlt]
    rw [htake, hget]
    exact hr ⟨j.val, hlt⟩
  · have heq : j.val = p.length := by omega
    have htake : (p ++ [b]).take j.val = p := by
      simp [heq]
    have hget : (p ++ [b]).get j = b := by
      simp [List.get_eq_getElem, heq]
    rw [htake, hget]
    exact hq

abbrev Vec (d : ℕ) : Type := Fin d → ZMod 2

lemma zmod2_eq_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide

lemma zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by
  decide

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 :=
  (zmod2_eq_zero_or_one a).resolve_left h

lemma zmod2_add_eq_iff : ∀ a b c : ZMod 2, a + b = c ↔ a = c + b := by
  decide

lemma decide_add_one_eq_not : ∀ a b : ZMod 2, decide (a + 1 = b) = !decide (a = b) := by
  decide

def dot {m : ℕ} (y g : Vec m) : ZMod 2 := ∑ i : Fin m, y i * g i

lemma dot_zero {m : ℕ} (g : Vec m) : dot (0 : Vec m) g = 0 := by
  simp [dot]

lemma dot_add {m : ℕ} (y1 y2 g : Vec m) : dot (y1 + y2) g = dot y1 g + dot y2 g := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_smul {m : ℕ} (c : ZMod 2) (y g : Vec m) : dot (c • y) g = c * dot y g := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_single {m : ℕ} (i : Fin m) (g : Vec m) : dot (Pi.single i 1) g = g i := by
  unfold dot
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact (h (Finset.mem_univ i)).elim

lemma linear_eq_dot {m : ℕ} (α : Vec m →ₗ[ZMod 2] ZMod 2) (y : Vec m) :
    α y = dot y (fun i => α (Pi.single i 1)) := by
  have hy : y = ∑ i : Fin m, y i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dot]

noncomputable section
open Classical

noncomputable def pickIdx {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) : Fin (d + 1) :=
  Classical.choose (Function.ne_iff.mp hg)

lemma pickIdx_spec {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) : g (pickIdx g hg) = 1 :=
  zmod2_eq_one_of_ne_zero (Classical.choose_spec (Function.ne_iff.mp hg))

def liftZero {d : ℕ} (i0 : Fin (d + 1)) (y' : Vec d) : Vec (d + 1) :=
  i0.insertNth 0 y'

lemma liftZero_add {d : ℕ} (i0 : Fin (d + 1)) (y1 y2 : Vec d) :
    liftZero i0 (y1 + y2) = liftZero i0 y1 + liftZero i0 y2 := by
  funext j
  refine Fin.succAboveCases i0 ?_ ?_ j
  · simp [liftZero]
  · intro k
    simp [liftZero]

lemma liftZero_smul {d : ℕ} (i0 : Fin (d + 1)) (c : ZMod 2) (y' : Vec d) :
    liftZero i0 (c • y') = c • liftZero i0 y' := by
  funext j
  refine Fin.succAboveCases i0 ?_ ?_ j
  · simp [liftZero]
  · intro k
    simp [liftZero]

noncomputable def toSplit {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) (y : Vec (d + 1)) :
    ZMod 2 × Vec d :=
  (dot y g, (pickIdx g hg).removeNth y)

noncomputable def ofSplit {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) (p : ZMod 2 × Vec d) :
    Vec (d + 1) :=
  (pickIdx g hg).insertNth (p.1 + dot (liftZero (pickIdx g hg) p.2) g) p.2

lemma ofSplit_eq_linear {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) (δ : ZMod 2) (y' : Vec d) :
    ofSplit g hg (δ, y') =
      liftZero (pickIdx g hg) y' +
      (δ + dot (liftZero (pickIdx g hg) y') g) • Pi.single (pickIdx g hg) 1 := by
  funext j
  refine Fin.succAboveCases (pickIdx g hg) ?_ ?_ j
  · simp [ofSplit, liftZero]
  · intro k
    simp [ofSplit, liftZero, Pi.single_eq_of_ne (Fin.succAbove_ne (pickIdx g hg) k)]

lemma dot_ofSplit {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) (p : ZMod 2 × Vec d) :
    dot (ofSplit g hg p) g = p.1 := by
  rcases p with ⟨δ, y'⟩
  rw [ofSplit_eq_linear, dot_add, dot_smul, dot_single, pickIdx_spec g hg, mul_one]
  have hself := zmod2_add_self (dot (liftZero (pickIdx g hg) y') g)
  calc dot (liftZero (pickIdx g hg) y') g + (δ + dot (liftZero (pickIdx g hg) y') g)
      = δ + (dot (liftZero (pickIdx g hg) y') g + dot (liftZero (pickIdx g hg) y') g) := by ring
    _ = δ + 0 := by rw [hself]
    _ = δ := by ring

lemma toSplit_ofSplit {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) (p : ZMod 2 × Vec d) :
    toSplit g hg (ofSplit g hg p) = p := by
  rcases p with ⟨δ, y'⟩
  apply Prod.ext
  · exact dot_ofSplit g hg (δ, y')
  · exact Fin.removeNth_insertNth (α := fun _ => ZMod 2) (pickIdx g hg)
      (δ + dot (liftZero (pickIdx g hg) y') g) y'

lemma vec_decomp {d : ℕ} (i0 : Fin (d + 1)) (y : Vec (d + 1)) :
    y = liftZero i0 (i0.removeNth y) + (y i0) • Pi.single i0 1 := by
  funext j
  refine Fin.succAboveCases i0 ?_ ?_ j
  · simp [liftZero]
  · intro k
    simp [liftZero, Fin.removeNth, Pi.single_eq_of_ne (Fin.succAbove_ne i0 k)]

lemma ofSplit_toSplit {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) (y : Vec (d + 1)) :
    ofSplit g hg (toSplit g hg y) = y := by
  let i0 := pickIdx g hg
  have hdec := vec_decomp i0 y
  have hdot : dot y g = dot (liftZero i0 (i0.removeNth y)) g + y i0 := by
    conv_lhs => rw [hdec]
    rw [dot_add, dot_smul, dot_single, pickIdx_spec g hg, mul_one]
  have hcoord : dot y g + dot (liftZero i0 (i0.removeNth y)) g = y i0 := by
    have h1 : y i0 + dot (liftZero i0 (i0.removeNth y)) g = dot y g := by
      rw [add_comm]
      exact hdot.symm
    exact ((zmod2_add_eq_iff (y i0) (dot (liftZero i0 (i0.removeNth y)) g) (dot y g)).mp h1).symm
  unfold ofSplit toSplit
  dsimp only
  change i0.insertNth (dot y g + dot (liftZero i0 (i0.removeNth y)) g) (i0.removeNth y) = y
  rw [hcoord]
  exact Fin.insertNth_self_removeNth i0 y

noncomputable def splitLin {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) :
    Vec d →ₗ[ZMod 2] Vec (d + 1) where
  toFun := fun y' => ofSplit g hg (0, y')
  map_add' := by
    intro y1 y2
    simp only [ofSplit_eq_linear, liftZero_add, dot_add, zero_add, add_smul]
    abel
  map_smul' := by
    intro c y'
    simp only [ofSplit_eq_linear, liftZero_smul, dot_smul, zero_add, RingHom.id_apply, smul_add,
      smul_smul]

lemma splitLin_injective {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) :
    Function.Injective (splitLin g hg) := by
  intro y1 y2 h
  have hrm := congrArg (fun z => (pickIdx g hg).removeNth z) h
  simpa [splitLin, ofSplit, Fin.removeNth_insertNth] using hrm

noncomputable def splitShift {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) : Vec (d + 1) :=
  Pi.single (pickIdx g hg) 1

lemma ofSplit_zero {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) (y' : Vec d) :
    ofSplit g hg (0, y') = splitLin g hg y' := rfl

lemma ofSplit_one {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) (y' : Vec d) :
    ofSplit g hg (1, y') = splitShift g hg + splitLin g hg y' := by
  simp only [splitLin, LinearMap.coe_mk, AddHom.coe_mk, splitShift, ofSplit_eq_linear,
    zero_add, add_smul, one_smul]
  abel

noncomputable def glue {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) (u0 u1 : Vec d → Vec d)
    (y : Vec (d + 1)) : Vec (d + 1) :=
  let p := toSplit g hg y
  ofSplit g hg (p.1, if p.1 = 0 then u0 p.2 else u1 p.2)

lemma glue_ofSplit_zero {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) (u0 u1 : Vec d → Vec d)
    (y' : Vec d) :
    glue g hg u0 u1 (ofSplit g hg (0, y')) = ofSplit g hg (0, u0 y') := by
  simp [glue, toSplit_ofSplit]

lemma glue_ofSplit_one {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) (u0 u1 : Vec d → Vec d)
    (y' : Vec d) :
    glue g hg u0 u1 (ofSplit g hg (1, y')) = ofSplit g hg (1, u1 y') := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  simp [glue, toSplit_ofSplit, h10]

def IsMatching {α : Type*} (v : α → α) : Prop :=
  ∀ x, v (v x) = x ∧ v x ≠ x

lemma isMatching_glue {d : ℕ} (g : Vec (d + 1)) (hg : g ≠ 0) {u0 u1 : Vec d → Vec d}
    (h0 : IsMatching u0) (h1 : IsMatching u1) : IsMatching (glue g hg u0 u1) := by
  intro y
  have hy : y = ofSplit g hg (toSplit g hg y) := (ofSplit_toSplit g hg y).symm
  rcases hsplit : toSplit g hg y with ⟨δ, y'⟩
  rw [hsplit] at hy
  rcases zmod2_eq_zero_or_one δ with rfl | rfl
  · rw [hy, glue_ofSplit_zero, glue_ofSplit_zero, (h0 y').1]
    refine ⟨rfl, ?_⟩
    intro heq
    have h2 := congrArg (fun z => (toSplit g hg z).2) heq
    simp only [toSplit_ofSplit] at h2
    exact (h0 y').2 h2
  · rw [hy, glue_ofSplit_one, glue_ofSplit_one, (h1 y').1]
    refine ⟨rfl, ?_⟩
    intro heq
    have h2 := congrArg (fun z => (toSplit g hg z).2) heq
    simp only [toSplit_ofSplit] at h2
    exact (h1 y').2 h2

noncomputable def recog : ∀ d : ℕ, Finset (Vec d → Vec d)
  | 0 => ∅
  | 1 => {fun (y : Vec 1) => y + (fun (_ : Fin 1) => (1 : ZMod 2))}
  | d + 2 =>
      (Finset.univ.erase (0 : Vec (d + 2))).attach.biUnion (fun p =>
        (recog (d + 1) ×ˢ recog (d + 1)).image (fun (uv : (Vec (d + 1) → Vec (d + 1)) × (Vec (d + 1) → Vec (d + 1))) =>
          glue p.1 (Finset.mem_erase.mp p.2).1 uv.1 uv.2))

lemma mem_recog_glue {d : ℕ} {g : Vec (d + 2)} (hg : g ≠ 0) {u0 u1 : Vec (d + 1) → Vec (d + 1)}
    (h0 : u0 ∈ recog (d + 1)) (h1 : u1 ∈ recog (d + 1)) :
    glue g hg u0 u1 ∈ recog (d + 2) := by
  simp only [recog, Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists]
  refine ⟨g, Finset.mem_erase.mpr ⟨hg, Finset.mem_univ g⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨(u0, u1), Finset.mem_product.mpr ⟨h0, h1⟩, rfl⟩

lemma isMatching_of_mem_recog : ∀ {d : ℕ}, 1 ≤ d → ∀ u ∈ recog d, IsMatching u
  | 0, hd, _, _ => by omega
  | 1, _, u, hu => by
    have hu' : u = fun (y : Vec 1) => y + (fun (_ : Fin 1) => (1 : ZMod 2)) :=
      Finset.mem_singleton.mp hu
    subst hu'
    intro y
    constructor
    · ext i
      simp only [Pi.add_apply]
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [add_assoc, h11, add_zero]
    · intro h
      have h0 := congrFun h 0
      simp only [Pi.add_apply] at h0
      have hne : ∀ a : ZMod 2, a + 1 ≠ a := by decide
      exact hne (y 0) h0
  | d + 2, _, u, hu => by
    simp only [recog, Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists] at hu
    rcases hu with ⟨g, hg, himg⟩
    rcases Finset.mem_image.mp himg with ⟨⟨u0, u1⟩, hprod, rfl⟩
    rcases Finset.mem_product.mp hprod with ⟨hu0, hu1⟩
    exact isMatching_glue g (Finset.mem_erase.mp hg).1
      (isMatching_of_mem_recog (by omega) u0 hu0)
      (isMatching_of_mem_recog (by omega) u1 hu1)

lemma card_vec (d : ℕ) : Fintype.card (Vec d) = 2 ^ d := by
  simp [Vec, Fintype.card_fun, ZMod.card]

lemma recog_card_step (d : ℕ) :
    (recog (d + 2)).card ≤ 2 ^ (d + 2) * ((recog (d + 1)).card * (recog (d + 1)).card) := by
  rw [recog]
  calc ((Finset.univ.erase (0 : Vec (d + 2))).attach.biUnion (fun p =>
          (recog (d + 1) ×ˢ recog (d + 1)).image (fun uv =>
            glue p.1 (Finset.mem_erase.mp p.2).1 uv.1 uv.2))).card
      ≤ ∑ p ∈ (Finset.univ.erase (0 : Vec (d + 2))).attach,
          ((recog (d + 1) ×ˢ recog (d + 1)).image (fun uv =>
            glue p.1 (Finset.mem_erase.mp p.2).1 uv.1 uv.2)).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ (Finset.univ.erase (0 : Vec (d + 2))).attach,
          (recog (d + 1) ×ˢ recog (d + 1)).card :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = (Finset.univ.erase (0 : Vec (d + 2))).card *
          ((recog (d + 1)).card * (recog (d + 1)).card) := by
        rw [Finset.sum_const, Finset.card_attach, smul_eq_mul, Finset.card_product]
    _ ≤ 2 ^ (d + 2) * ((recog (d + 1)).card * (recog (d + 1)).card) := by
        refine Nat.mul_le_mul_right _ ?_
        calc (Finset.univ.erase (0 : Vec (d + 2))).card
            ≤ (Finset.univ : Finset (Vec (d + 2))).card :=
              Finset.card_le_card (Finset.erase_subset _ _)
          _ = 2 ^ (d + 2) := by rw [Finset.card_univ, card_vec]

lemma linear_le_three_pow (d : ℕ) (hd : 1 ≤ d) : d + 2 ≤ 3 * 2 ^ (d - 1) := by
  induction d, hd using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ]
    simp only [Nat.add_sub_cancel]
    rw [hpow]
    omega

lemma recog_card_le (n : ℕ) (hn : 1 ≤ n) :
    (recog n).card ≤ 2 ^ (3 * 2 ^ (n - 1) - n - 2) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp [recog]
  | succ d hd ih =>
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hstep := recog_card_step d'
    have hlin := linear_le_three_pow (d' + 1) (by omega)
    have hmul : (recog (d' + 1)).card * (recog (d' + 1)).card ≤
        2 ^ (3 * 2 ^ d' - (d' + 1) - 2) * 2 ^ (3 * 2 ^ d' - (d' + 1) - 2) :=
      Nat.mul_le_mul ih ih
    have hle : (recog (d' + 2)).card ≤
        2 ^ (d' + 2) * (2 ^ (3 * 2 ^ d' - (d' + 1) - 2) * 2 ^ (3 * 2 ^ d' - (d' + 1) - 2)) :=
      le_trans hstep (Nat.mul_le_mul_left _ hmul)
    have hexp : (d' + 2) + ((3 * 2 ^ d' - (d' + 1) - 2) + (3 * 2 ^ d' - (d' + 1) - 2)) =
        3 * 2 ^ (d' + 1) - (d' + 2) - 2 := by
      have hpow : 2 ^ (d' + 1) = 2 ^ d' * 2 := pow_succ 2 d'
      simp only [Nat.add_sub_cancel] at hlin
      omega
    calc (recog (d' + 2)).card
        ≤ 2 ^ (d' + 2) *
            (2 ^ (3 * 2 ^ d' - (d' + 1) - 2) * 2 ^ (3 * 2 ^ d' - (d' + 1) - 2)) := hle
      _ = 2 ^ ((d' + 2) + ((3 * 2 ^ d' - (d' + 1) - 2) + (3 * 2 ^ d' - (d' + 1) - 2))) := by
          rw [← pow_add, ← pow_add]
      _ = 2 ^ (3 * 2 ^ (d' + 1) - (d' + 2) - 2) := by rw [hexp]

lemma exists_recog_of_cert {n : ℕ} {v : Vec n → Vec n} (hv : IsMatching v)
    {N J : Finset (List Bool)} {q : List Bool → Vec n → Bool} {out : List Bool → Finset (Vec n)}
    (hcert : Cert (Queries (Vec n)) (fun x a => a = {x, v x}) N J q out) :
    ∀ d : ℕ, 1 ≤ d →
      ∀ c : ℕ, ∀ (x0 : Vec n) (L : Vec d →ₗ[ZMod 2] Vec n),
        Function.Injective L →
        ∀ p : List Bool, p ∈ N → (sub N p).card = c →
        (∀ y : Vec d, Reach q p (x0 + L y)) →
        ∃ u ∈ recog d, ∃ s : ℕ,
          2 ^ d ≤ leafCount N J p + s ∧
          2 * s ≤ (Finset.univ.filter (fun y : Vec d => v (x0 + L y) = x0 + L (u y))).card := by
  intro d
  refine Nat.strongRecOn d ?_
  intro d ihd hd c
  refine Nat.strongRecOn c ?_
  intro c ihc x0 L hL p hpN hcard hreach
  by_cases hpJ : p ∈ J
  · rcases hcert.2.1 p hpJ with ⟨l, b, hq⟩
    let α : Vec d →ₗ[ZMod 2] ZMod 2 := l.comp L
    let g : Vec d := fun i => α (Pi.single i 1)
    have hdot : ∀ y : Vec d, l (x0 + L y) = l x0 + dot y g := by
      intro y
      rw [map_add]
      congr 1
      exact linear_eq_dot α y
    by_cases hg : g = 0
    · let b0 : Bool := decide (l x0 = b)
      have hstep : ∀ y : Vec d, q p (x0 + L y) = b0 := by
        intro y
        rw [hq]
        dsimp only
        rw [hdot y, hg, show dot y (0 : Vec d) = 0 by simp [dot], add_zero]
      have hreach' : ∀ y : Vec d, Reach q (p ++ [b0]) (x0 + L y) :=
        fun y => reach_snoc (hreach y) (hstep y)
      have hpN' : p ++ [b0] ∈ N := by
        cases b0
        · exact (hcert.1.2.2.2 p hpJ).1
        · exact (hcert.1.2.2.2 p hpJ).2
      have hlt : (sub N (p ++ [b0])).card < c := by
        rw [← hcard]
        exact sub_card_lt hcert.1 hpJ b0
      rcases ihc (sub N (p ++ [b0])).card hlt x0 L hL (p ++ [b0]) hpN' rfl hreach' with
        ⟨u, hu, s, hleaf, hfilt⟩
      have hleaf_le : leafCount N J (p ++ [b0]) ≤ leafCount N J p := by
        rw [leafCount_internal hpJ]
        cases b0 <;> omega
      exact ⟨u, hu, s, by omega, hfilt⟩
    · clear ihc
      rcases (show d = 1 ∨ ∃ d', d = d' + 2 from
        if h : d = 1 then Or.inl h else Or.inr ⟨d - 2, by omega⟩) with rfl | ⟨d', rfl⟩
      · refine ⟨fun (y : Vec 1) => y + (fun (_ : Fin 1) => (1 : ZMod 2)), Finset.mem_singleton_self _, 0, ?_, ?_⟩
        · have h0 := leafCount_pos hcert.1 (sub N (p ++ [false])).card (p ++ [false]) rfl
            (hcert.1.2.2.2 p hpJ).1
          have h1 := leafCount_pos hcert.1 (sub N (p ++ [true])).card (p ++ [true]) rfl
            (hcert.1.2.2.2 p hpJ).2
          rw [leafCount_internal hpJ]
          omega
        · exact Nat.zero_le _
      · let b0 : Bool := decide (l x0 = b)
        let b1 : Bool := decide (l x0 + 1 = b)
        have hb1 : b1 = !b0 := decide_add_one_eq_not (l x0) b
        let L' : Vec (d' + 1) →ₗ[ZMod 2] Vec n := L.comp (splitLin g hg)
        have hL' : Function.Injective L' := hL.comp (splitLin_injective g hg)
        let x1 : Vec n := x0 + L (splitShift g hg)
        have hreach0 : ∀ y' : Vec (d' + 1), Reach q (p ++ [b0]) (x0 + L' y') := by
          intro y'
          have hq0 : q p (x0 + L' y') = b0 := by
            change q p (x0 + L (splitLin g hg y')) = b0
            rw [hq]
            dsimp only
            rw [hdot, ← ofSplit_zero, dot_ofSplit, add_zero]
          exact reach_snoc (hreach (splitLin g hg y')) hq0
        have hx1_eq : ∀ y' : Vec (d' + 1), x1 + L' y' = x0 + L (ofSplit g hg (1, y')) := by
          intro y'
          change (x0 + L (splitShift g hg)) + L (splitLin g hg y') = x0 + L (ofSplit g hg (1, y'))
          rw [add_assoc, ← map_add, ← ofSplit_one]
        have hreach1 : ∀ y' : Vec (d' + 1), Reach q (p ++ [b1]) (x1 + L' y') := by
          intro y'
          rw [hx1_eq y']
          have hq1 : q p (x0 + L (ofSplit g hg (1, y'))) = b1 := by
            rw [hq]
            dsimp only
            rw [hdot, dot_ofSplit]
          exact reach_snoc (hreach (ofSplit g hg (1, y'))) hq1
        have hpN0 : p ++ [b0] ∈ N := by
          cases b0
          · exact (hcert.1.2.2.2 p hpJ).1
          · exact (hcert.1.2.2.2 p hpJ).2
        have hpN1 : p ++ [b1] ∈ N := by
          cases b1
          · exact (hcert.1.2.2.2 p hpJ).1
          · exact (hcert.1.2.2.2 p hpJ).2
        rcases ihd (d' + 1) (by omega) (by omega) (sub N (p ++ [b0])).card x0 L' hL'
            (p ++ [b0]) hpN0 rfl hreach0 with ⟨u0, hu0, s0, hleaf0, hfilt0⟩
        rcases ihd (d' + 1) (by omega) (by omega) (sub N (p ++ [b1])).card x1 L' hL'
            (p ++ [b1]) hpN1 rfl hreach1 with ⟨u1, hu1, s1, hleaf1, hfilt1⟩
        refine ⟨glue g hg u0 u1, mem_recog_glue hg hu0 hu1, s0 + s1, ?_, ?_⟩
        · have hsum : leafCount N J (p ++ [b0]) + leafCount N J (p ++ [b1]) = leafCount N J p := by
            rw [hb1, leafCount_internal hpJ]
            cases b0 <;> simp [add_comm]
          have hpow : 2 ^ (d' + 2) = 2 ^ (d' + 1) + 2 ^ (d' + 1) := by
            rw [pow_succ]
            omega
          omega
        · let F0 := Finset.univ.filter (fun y' : Vec (d' + 1) => v (x0 + L' y') = x0 + L' (u0 y'))
          let F1 := Finset.univ.filter (fun y' : Vec (d' + 1) => v (x1 + L' y') = x1 + L' (u1 y'))
          let F := Finset.univ.filter
            (fun y : Vec (d' + 2) => v (x0 + L y) = x0 + L (glue g hg u0 u1 y))
          let I0 := F0.image (fun y' => ofSplit g hg (0, y'))
          let I1 := F1.image (fun y' => ofSplit g hg (1, y'))
          have hsub0 : I0 ⊆ F := by
            intro y hy
            rcases Finset.mem_image.mp hy with ⟨y', hy', rfl⟩
            have heq0 : v (x0 + L' y') = x0 + L' (u0 y') := (Finset.mem_filter.mp hy').2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rw [glue_ofSplit_zero, ofSplit_zero, ofSplit_zero]
            exact heq0
          have hsub1 : I1 ⊆ F := by
            intro y hy
            rcases Finset.mem_image.mp hy with ⟨y', hy', rfl⟩
            have heq1 : v (x1 + L' y') = x1 + L' (u1 y') := (Finset.mem_filter.mp hy').2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rw [glue_ofSplit_one, ← hx1_eq y', ← hx1_eq (u1 y')]
            exact heq1
          have hdisj : Disjoint I0 I1 := by
            rw [Finset.disjoint_left]
            intro y hy0 hy1
            rcases Finset.mem_image.mp hy0 with ⟨y0, _, rfl⟩
            rcases Finset.mem_image.mp hy1 with ⟨y1, _, heq⟩
            have hdotEq := congrArg (fun z => dot z g) heq
            simp only [dot_ofSplit] at hdotEq
            exact (by decide : (1 : ZMod 2) ≠ 0) hdotEq
          have hinj0 : Function.Injective (fun y' : Vec (d' + 1) => ofSplit g hg (0, y')) := by
            intro a1 a2 h
            have h2 := congrArg (fun z => (toSplit g hg z).2) h
            simpa [toSplit_ofSplit] using h2
          have hinj1 : Function.Injective (fun y' : Vec (d' + 1) => ofSplit g hg (1, y')) := by
            intro a1 a2 h
            have h2 := congrArg (fun z => (toSplit g hg z).2) h
            simpa [toSplit_ofSplit] using h2
          have hcard_le : F0.card + F1.card ≤ F.card := by
            rw [← Finset.card_image_of_injective F0 hinj0,
              ← Finset.card_image_of_injective F1 hinj1,
              ← Finset.card_union_of_disjoint hdisj]
            exact Finset.card_le_card (Finset.union_subset hsub0 hsub1)
          change 2 * s0 ≤ F0.card at hfilt0
          change 2 * s1 ≤ F1.card at hfilt1
          change 2 * (s0 + s1) ≤ F.card
          omega
  · clear ihd ihc
    have hpLeaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hpN, hpJ⟩
    have hout : ∀ y : Vec d, out p = {x0 + L y, v (x0 + L y)} :=
      fun y => hcert.2.2 p hpLeaf (x0 + L y) (hreach y)
    have hout0 : out p = {x0, v x0} := by
      simpa using hout 0
    have himg_sub : Finset.univ.image (fun y : Vec d => x0 + L y) ⊆ out p := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨y, _, rfl⟩
      rw [hout y]
      simp
    have hinjAff : Function.Injective (fun y : Vec d => x0 + L y) :=
      (add_right_injective x0).comp hL
    have hpow_le : 2 ^ d ≤ 2 := by
      calc 2 ^ d = (Finset.univ : Finset (Vec d)).card := by rw [Finset.card_univ, card_vec]
        _ = (Finset.univ.image (fun y : Vec d => x0 + L y)).card :=
            (Finset.card_image_of_injective _ hinjAff).symm
        _ ≤ (out p).card := Finset.card_le_card himg_sub
        _ = ({x0, v x0} : Finset (Vec n)).card := by rw [hout0]
        _ ≤ 2 := Finset.card_le_two
    have hd1 : d = 1 := by
      by_contra hne
      have hge2 : 2 ≤ d := by omega
      have h4 : 2 ^ 2 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hge2
      omega
    subst hd1
    refine ⟨fun (y : Vec 1) => y + (fun (_ : Fin 1) => (1 : ZMod 2)), Finset.mem_singleton_self _, 1, ?_, ?_⟩
    · rw [leafCount_of_leaf hcert.1 hpN hpJ]
      omega
    · let y1 : Vec 1 := fun _ => 1
      have hy1_ne : y1 ≠ 0 := by
        intro h
        have h0 := congrFun h 0
        exact (by decide : (1 : ZMod 2) ≠ 0) h0
      have hne0 : x0 + L y1 ≠ x0 := by
        intro h
        have hLy1 : L y1 = 0 := by
          have h' : x0 + L y1 = x0 + 0 := by simpa using h
          exact add_left_cancel h'
        exact hy1_ne (hL (by rw [hLy1, map_zero]))
      have hmem1 : x0 + L y1 ∈ ({x0, v x0} : Finset (Vec n)) := by
        rw [← hout0]
        exact himg_sub (Finset.mem_image.mpr ⟨y1, Finset.mem_univ y1, rfl⟩)
      have hvx0 : x0 + L y1 = v x0 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1
        rcases hmem1 with h | h
        · exact (hne0 h).elim
        · exact h
      have hfilt_eq : Finset.univ.filter
          (fun y : Vec 1 => v (x0 + L y) = x0 + L (y + (fun _ => 1))) = Finset.univ := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        rcases zmod2_eq_zero_or_one (y 0) with hy0 | hy0
        · have hy : y = 0 := by
            ext i
            rw [Subsingleton.elim i 0]
            exact hy0
          rw [hy, map_zero, add_zero, zero_add]
          exact hvx0.symm
        · have hy : y = y1 := by
            ext i
            rw [Subsingleton.elim i 0]
            exact hy0
          have hyadd : y + (fun _ => 1) = 0 := by
            rw [hy]
            ext i
            simp [y1, zmod2_add_self]
          rw [hy, hvx0, (hv x0).1, ← hy, hyadd, map_zero, add_zero]
      rw [hfilt_eq, Finset.card_univ, card_vec]
      norm_num

def M : ℕ → ℕ
  | 0 => 1
  | r + 1 => (2 * r + 1) * M r

lemma fact_choose_M_le (r : ℕ) : ∀ k : ℕ, k.factorial * Nat.choose (r + k) k * M r ≤ M (r + k)
  | 0 => by simp
  | k + 1 => by
    have ih := fact_choose_M_le r k
    have hch := Nat.add_one_mul_choose_eq (r + k) k
    calc (k + 1).factorial * Nat.choose (r + (k + 1)) (k + 1) * M r
        = k.factorial * (Nat.choose (r + k + 1) (k + 1) * (k + 1)) * M r := by
          rw [Nat.factorial_succ, show r + (k + 1) = r + k + 1 by omega]
          ring
      _ = k.factorial * ((r + k + 1) * Nat.choose (r + k) k) * M r := by rw [← hch]
      _ = (r + k + 1) * (k.factorial * Nat.choose (r + k) k * M r) := by ring
      _ ≤ (2 * (r + k) + 1) * M (r + k) := Nat.mul_le_mul (by omega) ih
      _ = M (r + (k + 1)) := by
          rw [show r + (k + 1) = (r + k) + 1 by omega]
          rfl

noncomputable def MatchOn {n : ℕ} (A : Finset (Vec n)) : Finset (Vec n → Vec n) :=
  Finset.univ.filter (fun v : Vec n → Vec n =>
    (∀ x ∈ A, v x ∈ A ∧ v (v x) = x ∧ v x ≠ x) ∧ ∀ x ∉ A, v x = x)

lemma card_matchOn {n : ℕ} : ∀ r : ℕ, ∀ A : Finset (Vec n), A.card = 2 * r →
    (MatchOn A).card = M r
  | 0, A, hcard => by
    have hA : A = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hA
    have heq : MatchOn (∅ : Finset (Vec n)) = {id} := by
      ext v
      simp [MatchOn, funext_iff]
    rw [heq, Finset.card_singleton]
    rfl
  | r + 1, A, hcard => by
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    rcases hne with ⟨a, ha⟩
    let A' := A.erase a
    have hA'card : A'.card = 2 * r + 1 := by
      rw [Finset.card_erase_of_mem ha]
      omega
    have hpart : MatchOn A = A'.biUnion (fun b => (MatchOn A).filter (fun v => v a = b)) := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hv
        have hva := (Finset.mem_filter.mp hv).2.1 a ha
        exact ⟨v a, Finset.mem_erase.mpr ⟨hva.2.2, hva.1⟩, hv, rfl⟩
      · rintro ⟨_, _, hv, _⟩
        exact hv
    have hdisj : Set.PairwiseDisjoint (A' : Set (Vec n))
        (fun b => (MatchOn A).filter (fun v => v a = b)) := by
      intro b1 _ b2 _ hne12
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      exact hne12 ((Finset.mem_filter.mp hv1).2.symm.trans (Finset.mem_filter.mp hv2).2)
    rw [hpart, Finset.card_biUnion hdisj]
    have hterm : ∀ b ∈ A', ((MatchOn A).filter (fun v => v a = b)).card = M r := by
      intro b hb
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      have hbA : b ∈ A := (Finset.mem_erase.mp hb).2
      have hcard' : (A'.erase b).card = 2 * r := by
        rw [Finset.card_erase_of_mem hb]
        omega
      rw [← card_matchOn r (A'.erase b) hcard']
      refine Finset.card_bij
        (fun v _ => fun x => if x = a ∨ x = b then x else v x) ?_ ?_ ?_
      · intro v hv
        rcases Finset.mem_filter.mp hv with ⟨hvM, hva⟩
        rcases (Finset.mem_filter.mp hvM).2 with ⟨hIn, hOut⟩
        have hvb : v b = a := by
          rw [← hva]
          exact (hIn a ha).2.1
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro x hx
          have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
          have hxA' : x ∈ A' := (Finset.mem_erase.mp hx).2
          have hxa : x ≠ a := (Finset.mem_erase.mp hxA').1
          have hxA : x ∈ A := (Finset.mem_erase.mp hxA').2
          have hnot : ¬ (x = a ∨ x = b) := by tauto
          have hvx := hIn x hxA
          have hvxa : v x ≠ a := by
            intro h
            have h1 : x = b := by rw [← hvx.2.1, h, hva]
            exact hxb h1
          have hvxb : v x ≠ b := by
            intro h
            have h1 : x = a := by rw [← hvx.2.1, h, hvb]
            exact hxa h1
          have hnot' : ¬ (v x = a ∨ v x = b) := by tauto
          simp only [hnot, ↓reduceIte, hnot']
          exact ⟨Finset.mem_erase.mpr ⟨hvxb, Finset.mem_erase.mpr ⟨hvxa, hvx.1⟩⟩,
            hvx.2.1, hvx.2.2⟩
        · intro x hx
          by_cases hab : x = a ∨ x = b
          · simp [hab]
          · have hxA : x ∉ A := by
              intro hxA
              apply hx
              exact Finset.mem_erase.mpr ⟨by tauto, Finset.mem_erase.mpr ⟨by tauto, hxA⟩⟩
            simp [hab, hOut x hxA]
      · intro v1 hv1 v2 hv2 heq
        rcases Finset.mem_filter.mp hv1 with ⟨hv1M, hv1a⟩
        rcases Finset.mem_filter.mp hv2 with ⟨hv2M, hv2a⟩
        have hv1b : v1 b = a := by
          rw [← hv1a]
          exact ((Finset.mem_filter.mp hv1M).2.1 a ha).2.1
        have hv2b : v2 b = a := by
          rw [← hv2a]
          exact ((Finset.mem_filter.mp hv2M).2.1 a ha).2.1
        funext x
        by_cases hxa : x = a
        · rw [hxa, hv1a, hv2a]
        · by_cases hxb : x = b
          · rw [hxb, hv1b, hv2b]
          · have hnot : ¬ (x = a ∨ x = b) := by tauto
            have hx := congrFun heq x
            simpa [hnot] using hx
      · intro u hu
        rcases (Finset.mem_filter.mp hu).2 with ⟨huIn, huOut⟩
        let v : Vec n → Vec n := fun x => if x = a then b else if x = b then a else u x
        refine ⟨v, ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
          · intro x hxA
            by_cases hxa : x = a
            · subst hxa
              simp [v, hbA, hba, hba.symm]
            · by_cases hxb : x = b
              · rw [hxb]
                simp [v, ha, hba, hba.symm]
              · have hx' : x ∈ A'.erase b :=
                  Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hxA⟩⟩
                have hux := huIn x hx'
                have huxb : u x ≠ b := (Finset.mem_erase.mp hux.1).1
                have huxa : u x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hux.1).2).1
                have huxA : u x ∈ A := (Finset.mem_erase.mp (Finset.mem_erase.mp hux.1).2).2
                simp [v, hxa, hxb, huxa, huxb, huxA, hux.2.1, hux.2.2]
          · intro x hxA
            have hxa : x ≠ a := fun h => hxA (h ▸ ha)
            have hxb : x ≠ b := fun h => hxA (h ▸ hbA)
            have hx' : x ∉ A'.erase b := fun h =>
              hxA (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2
            simp [v, hxa, hxb, huOut x hx']
          · simp [v]
        · funext x
          by_cases hxa : x = a
          · rw [hxa]
            have hna : a ∉ A'.erase b := fun h =>
              (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl
            simp [huOut a hna]
          · by_cases hxb : x = b
            · rw [hxb]
              have hnb : b ∉ A'.erase b := Finset.notMem_erase b A'
              simp [huOut b hnb]
            · simp [v, hxa, hxb]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hA'card]
    rfl

noncomputable def Ew {n : ℕ} (w : Vec n → Vec n) : Finset (Vec n) :=
  Finset.univ.filter (fun x : Vec n => Fintype.equivFin (Vec n) x < Fintype.equivFin (Vec n) (w x))

lemma isMatching_injective {α : Type*} {w : α → α} (hw : IsMatching w) :
    Function.Injective w := by
  intro x y h
  calc x = w (w x) := (hw x).1.symm
    _ = w (w y) := by rw [h]
    _ = y := (hw y).1

lemma mem_ew_iff_not_mem_ew {n : ℕ} {w : Vec n → Vec n} (hw : IsMatching w) (x : Vec n) :
    x ∈ Ew w ↔ w x ∉ Ew w := by
  simp only [Ew, Finset.mem_filter, Finset.mem_univ, true_and, (hw x).1]
  have hne : Fintype.equivFin (Vec n) x ≠ Fintype.equivFin (Vec n) (w x) :=
    fun h => (hw x).2 ((Fintype.equivFin (Vec n)).injective h).symm
  constructor
  · intro hlt
    exact not_lt.mpr (le_of_lt hlt)
  · intro hnlt
    exact lt_of_le_of_ne (not_lt.mp hnlt) hne

lemma card_ew {n : ℕ} (hn : 1 ≤ n) {w : Vec n → Vec n} (hw : IsMatching w) :
    (Ew w).card = 2 ^ (n - 1) := by
  have hcompl : Finset.univ \ Ew w = (Ew w).image w := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      refine ⟨w y, ?_, (hw y).1⟩
      rw [mem_ew_iff_not_mem_ew hw, (hw y).1]
      exact hy
    · rintro ⟨x, hx, rfl⟩
      exact (mem_ew_iff_not_mem_ew hw x).mp hx
  have hsum : (Finset.univ \ Ew w).card + (Ew w).card = 2 ^ n := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, card_vec]
  rw [hcompl, Finset.card_image_of_injective _ (isMatching_injective hw)] at hsum
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  omega

lemma exists_subset_ew {n k : ℕ} {w v : Vec n → Vec n}
    (hw : IsMatching w) (hv : IsMatching v)
    (hagree : 2 * k ≤ (Finset.univ.filter (fun x : Vec n => v x = w x)).card) :
    ∃ S ∈ (Ew w).powersetCard k, ∀ x ∈ S, v x = w x := by
  let Agree := Finset.univ.filter (fun x : Vec n => v x = w x)
  let A1 := Agree ∩ Ew w
  let A2 := Agree \ Ew w
  have hsum : A1.card + A2.card = Agree.card := by
    rw [Finset.card_inter_add_card_sdiff]
  have hA2 : A2 = A1.image w := by
    ext y
    simp only [A1, A2, Agree, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hyv, hyn⟩
      refine ⟨w y, ⟨?_, ?_⟩, (hw y).1⟩
      · rw [(hw y).1, ← hyv, (hv y).1]
      · rw [mem_ew_iff_not_mem_ew hw, (hw y).1]
        exact hyn
    · rintro ⟨x, ⟨hxv, hxe⟩, rfl⟩
      refine ⟨?_, (mem_ew_iff_not_mem_ew hw x).mp hxe⟩
      rw [(hw x).1, ← hxv, (hv x).1]
  rw [hA2, Finset.card_image_of_injective _ (isMatching_injective hw)] at hsum
  change 2 * k ≤ Agree.card at hagree
  have hkA1 : k ≤ A1.card := by omega
  rcases Finset.exists_subset_card_eq hkA1 with ⟨S, hSA1, hScard⟩
  refine ⟨S, Finset.mem_powersetCard.mpr ⟨?_, hScard⟩, ?_⟩
  · intro x hx
    exact (Finset.mem_inter.mp (hSA1 hx)).2
  · intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp (hSA1 hx)).1).2

lemma card_filter_agree_subset {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ 2 ^ (n - 1))
    {w : Vec n → Vec n} (hw : IsMatching w) {S : Finset (Vec n)}
    (hS : S ∈ (Ew w).powersetCard k) :
    ((MatchOn (Finset.univ : Finset (Vec n))).filter (fun v => ∀ x ∈ S, v x = w x)).card ≤
      M (2 ^ (n - 1) - k) := by
  rcases Finset.mem_powersetCard.mp hS with ⟨hSEw, hScard⟩
  let U := S ∪ S.image w
  let R := Finset.univ \ U
  have hdisj : Disjoint S (S.image w) := by
    rw [Finset.disjoint_left]
    intro x hxS hxIm
    rcases Finset.mem_image.mp hxIm with ⟨y, hyS, rfl⟩
    exact (mem_ew_iff_not_mem_ew hw y).mp (hSEw hyS) (hSEw hxS)
  have hUcard : U.card = 2 * k := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (isMatching_injective hw), hScard]
    omega
  have hRcard : R.card = 2 * (2 ^ (n - 1) - k) := by
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ, mul_comm]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ, card_vec, hUcard]
    omega
  rw [← card_matchOn (2 ^ (n - 1) - k) R hRcard]
  let pad : (Vec n → Vec n) → (Vec n → Vec n) := fun v x => if x ∈ R then v x else x
  have hagreeU : ∀ v ∈ (MatchOn (Finset.univ : Finset (Vec n))).filter
      (fun v => ∀ x ∈ S, v x = w x), ∀ y ∈ U, v y = w y ∧ w y ∈ U := by
    intro v hv y hy
    rcases Finset.mem_filter.mp hv with ⟨hvM, hSagree⟩
    have hvInv : ∀ z, v (v z) = z := fun z => ((Finset.mem_filter.mp hvM).2.1 z (Finset.mem_univ z)).2.1
    rcases Finset.mem_union.mp hy with hyS | hyIm
    · exact ⟨hSagree y hyS, Finset.mem_union_right S (Finset.mem_image.mpr ⟨y, hyS, rfl⟩)⟩
    · rcases Finset.mem_image.mp hyIm with ⟨z, hzS, rfl⟩
      have hvz : v z = w z := hSagree z hzS
      refine ⟨?_, ?_⟩
      · rw [(hw z).1, ← hvz, hvInv z]
      · rw [(hw z).1]
        exact Finset.mem_union_left _ hzS
  refine Finset.card_le_card_of_injOn pad ?_ ?_
  · intro v hv
    have hv' := Finset.mem_coe.mp hv
    rcases Finset.mem_filter.mp hv' with ⟨hvM, _⟩
    have hvAll := (Finset.mem_filter.mp hvM).2.1
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩)
    · intro x hxR
      have hxU : x ∉ U := (Finset.mem_sdiff.mp hxR).2
      have hvx := hvAll x (Finset.mem_univ x)
      have hvxR : v x ∈ R := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        intro hvxU
        have h1 := hagreeU v hv' (v x) hvxU
        have hxInU : x ∈ U := by
          have h2 : x = w (v x) := by rw [← h1.1, hvx.2.1]
          rw [h2]
          exact h1.2
        exact hxU hxInU
      simp [pad, hxR, hvxR, hvx.2.1, hvx.2.2]
    · intro x hxR
      simp [pad, hxR]
  · intro v1 hv1 v2 hv2 heq
    funext x
    by_cases hxR : x ∈ R
    · have hx := congrFun heq x
      simpa [pad, hxR] using hx
    · have hxU : x ∈ U := by
        by_contra hnot
        exact hxR (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hnot⟩)
      rw [(hagreeU v1 (Finset.mem_coe.mp hv1) x hxU).1,
        (hagreeU v2 (Finset.mem_coe.mp hv2) x hxU).1]

lemma main_bound (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k ≤ 2 ^ (n - 1)) :
    let X := Vec n
    let matching := fun v : X → X => ∀ x, v (v x) = x ∧ v x ≠ x
    let m := 2 ^ (n - 1)
    let total := Nat.card {v : X → X // matching v}
    let easy := Nat.card {v : X → X // matching v ∧
      ∃ (N J : Finset (List Bool)) (q : List Bool → X → Bool) (out : List Bool → Finset X),
        Cert (Queries X) (fun x a => a = {x, v x}) N J q out ∧
        (N \ J).card + k ≤ 2 ^ n}
    k.factorial * easy ≤ 2 ^ (3 * m - n - 2) * total := by
  intro X matching m total easy
  have hn1 : 1 ≤ n := hn
  have htotal : total = M m := by
    change Nat.card {v : Vec n → Vec n // IsMatching v} = M m
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hfilt : Finset.univ.filter (fun v : Vec n → Vec n => IsMatching v) =
        MatchOn (Finset.univ : Finset (Vec n)) := by
      ext v
      rw [MatchOn, Finset.mem_filter, Finset.mem_filter]
      simp only [IsMatching, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨fun x _ => h x, fun _ ht => (ht trivial).elim⟩,
        fun h x => h.1 x trivial⟩
    rw [hfilt]
    refine card_matchOn m (Finset.univ : Finset (Vec n)) ?_
    rw [Finset.card_univ, card_vec]
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  let EasyPred : (Vec n → Vec n) → Prop := fun v =>
    IsMatching v ∧
      ∃ (N J : Finset (List Bool)) (q : List Bool → Vec n → Bool) (out : List Bool → Finset (Vec n)),
        Cert (Queries (Vec n)) (fun x a => a = {x, v x}) N J q out ∧
        (N \ J).card + k ≤ 2 ^ n
  have heasy_eq : easy = (Finset.univ.filter EasyPred).card := by
    change Nat.card {v : Vec n → Vec n // EasyPred v} = (Finset.univ.filter EasyPred).card
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : Finset.univ.filter EasyPred ⊆
      (recog n).biUnion (fun w => ((Ew w).powersetCard k).biUnion (fun S =>
        (MatchOn (Finset.univ : Finset (Vec n))).filter (fun v => ∀ x ∈ S, v x = w x))) := by
    intro v hv
    rcases (Finset.mem_filter.mp hv).2 with ⟨hvM, N, J, q, out, hcert, hcard⟩
    rcases exists_recog_of_cert hvM hcert n hn1 (sub N []).card 0 LinearMap.id
        Function.injective_id [] hcert.1.1 rfl (fun _ => reach_nil q _) with
      ⟨w, hwRec, s, hleaf, hfilt⟩
    rw [leafCount_nil] at hleaf
    have hks : k ≤ s := by omega
    have hagree : 2 * k ≤ (Finset.univ.filter (fun x : Vec n => v x = w x)).card := by
      have heqFilt : Finset.univ.filter
          (fun y : Vec n => v (0 + (LinearMap.id : Vec n →ₗ[ZMod 2] Vec n) y) =
            0 + (LinearMap.id : Vec n →ₗ[ZMod 2] Vec n) (w y)) =
          Finset.univ.filter (fun x : Vec n => v x = w x) := by
        ext x
        simp
      rw [heqFilt] at hfilt
      omega
    rcases exists_subset_ew (isMatching_of_mem_recog hn1 w hwRec) hvM hagree with
      ⟨S, hSpow, hSagree⟩
    refine Finset.mem_biUnion.mpr ⟨w, hwRec, Finset.mem_biUnion.mpr ⟨S, hSpow, ?_⟩⟩
    refine Finset.mem_filter.mpr ⟨?_, hSagree⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro x _
      exact ⟨Finset.mem_univ _, (hvM x).1, (hvM x).2⟩
    · intro x hx
      exact (hx (Finset.mem_univ x)).elim
  have heasy_le : easy ≤ (recog n).card * (Nat.choose m k * M (m - k)) := by
    rw [heasy_eq]
    calc (Finset.univ.filter EasyPred).card
        ≤ ((recog n).biUnion (fun w => ((Ew w).powersetCard k).biUnion (fun S =>
            (MatchOn (Finset.univ : Finset (Vec n))).filter (fun v => ∀ x ∈ S, v x = w x)))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ w ∈ recog n, (((Ew w).powersetCard k).biUnion (fun S =>
            (MatchOn (Finset.univ : Finset (Vec n))).filter (fun v => ∀ x ∈ S, v x = w x))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ w ∈ recog n, ∑ S ∈ (Ew w).powersetCard k,
            ((MatchOn (Finset.univ : Finset (Vec n))).filter (fun v => ∀ x ∈ S, v x = w x)).card :=
          Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
      _ ≤ ∑ w ∈ recog n, ∑ _S ∈ (Ew w).powersetCard k, M (m - k) := by
          refine Finset.sum_le_sum (fun w hw => Finset.sum_le_sum (fun S hS => ?_))
          exact card_filter_agree_subset hn1 hk (isMatching_of_mem_recog hn1 w hw) hS
      _ = ∑ w ∈ recog n, Nat.choose m k * M (m - k) := by
          refine Finset.sum_congr rfl (fun w hw => ?_)
          rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard,
            card_ew hn1 (isMatching_of_mem_recog hn1 w hw)]
      _ = (recog n).card * (Nat.choose m k * M (m - k)) := by
          rw [Finset.sum_const, smul_eq_mul]
  calc k.factorial * easy
      ≤ k.factorial * ((recog n).card * (Nat.choose m k * M (m - k))) :=
        Nat.mul_le_mul_left _ heasy_le
    _ = (recog n).card * (k.factorial * Nat.choose ((m - k) + k) k * M (m - k)) := by
        rw [Nat.sub_add_cancel hk]
        ring
    _ ≤ 2 ^ (3 * m - n - 2) * M ((m - k) + k) :=
        Nat.mul_le_mul (recog_card_le n hn1) (fact_choose_M_le (m - k) k)
    _ = 2 ^ (3 * m - n - 2) * total := by
        rw [Nat.sub_add_cancel hk, htotal]

end

end PEqualNP.Outside.L_pcx_362_aux

theorem PEqualNP.Outside.L_pcx_362 : (let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  ∀ n : ℕ, 0 < n →
    let X := Fin n → ZMod 2
    let matching := fun v : X → X => ∀ x, v (v x) = x ∧ v x ≠ x
    let m := 2^(n-1)
    let total := Nat.card {v : X → X // matching v}
    ∀ k : ℕ, k ≤ m →
      let easy := Nat.card {v : X → X // matching v ∧
        ∃ (N J : Finset (List Bool)) (q : List Bool → X → Bool) (out : List Bool → Finset X),
          cert (queries X) (fun x a => a = {x, v x}) N J q out ∧
          (N \ J).card + k ≤ 2^n}
      k.factorial * easy ≤ 2^(3*m-n-2) * total) := by
  dsimp only
  intro n hn k hk
  exact PEqualNP.Outside.L_pcx_362_aux.main_bound n hn k hk
