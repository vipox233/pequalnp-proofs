import Mathlib
import PEqualNP.Defs

-- The normalized gate basis and affine wire machinery follow L_meta_30642.lean
-- at accepted revision 1394d5d0d05067cc059aa91efad768024d32ee62.


namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.PivotFinish

open scoped BigOperators
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

theorem bit_gate_pair :
    ∀ a b : F,
    let ba := decide (a = 1)
    let bb := decide (b = 1)
    PEqualNP.CircuitLowerBounds.GateOp.and.eval [ba,bb] = decide (a*b = 1) ∧
    PEqualNP.CircuitLowerBounds.GateOp.or.eval [ba,bb] = decide (a+b+a*b = 1) ∧
    PEqualNP.CircuitLowerBounds.GateOp.not.eval
      [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [ba,bb]] =
      decide (a+b = 1) := by
  decide +kernel

theorem no_free_after_elimination {p k t : ℕ} (A : Vec p →ₗ[F] Vec k)
    (hA : Function.Injective A) (b : Vec k → Vec t → Vec k)
    (g h : Vec k → Vec t → F) (l : Vec p → F)
    (heval : ∀ q y z, dotProduct (A q + b y z) y + g y z = l q + h y z) :
    p = 0 := by
  have hconst : ∀ q, l q = l 0 := by
    intro q
    have hq := heval q 0 0
    have h0 := heval 0 0 0
    simp only [dotProduct_zero] at hq h0
    exact add_right_cancel (hq.symm.trans h0)
  have hvanish : ∀ q, A q = 0 := by
    intro q
    ext i
    let y : Vec k := fun j => if i = j then 1 else 0
    have hq := heval q y 0
    have h0 := heval 0 y 0
    rw [hconst q] at hq
    have hd : dotProduct (A q + b y 0) y = dotProduct (b y 0) y := by
      apply add_right_cancel (b := g y 0)
      simpa only [map_zero, zero_add] using hq.trans h0.symm
    have hdot : ∀ v : Vec k, dotProduct v y = v i := by
      intro v
      simp [dotProduct,y,Finset.sum_ite_eq]
    rw [hdot, hdot] at hd
    have hz : A q i + b y 0 i = 0 + b y 0 i := hd.trans (zero_add _).symm
    exact add_right_cancel hz
  by_contra hp
  let i : Fin p := ⟨0, Nat.pos_of_ne_zero hp⟩
  let q : Vec p := fun _ => 1
  have he : q = 0 := hA ((hvanish q).trans (map_zero A).symm)
  have hm : (1 : F) = 0 := congrFun he i
  exact one_ne_zero hm

end PEqualNP.Outside.L_meta_32579_aux.RowPort.PivotFinish

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.PivotStep
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

theorem solve_one {p : ℕ} (a : Vec (p+1) →ₗ[F] F) (ha : a ≠ 0) :
    ∃ (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1)),
      Function.Injective R ∧ a v = 1 ∧
      (∀ q, a (R q) = 0) ∧ (∀ q c, a (R q + c • v) + c = 0) := by
  classical
  have hsurj : Function.Surjective a := LinearMap.surjective_of_ne_zero ha
  obtain ⟨v,hv⟩ := hsurj 1
  have hkdim : Module.finrank F a.ker = p := by
    have h := LinearMap.finrank_range_add_finrank_ker a
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_fin_fun] at h
    omega
  let E : Vec p ≃ₗ[F] a.ker := LinearEquiv.ofFinrankEq _ _ (by rw [hkdim, Module.finrank_fin_fun])
  let R : Vec p →ₗ[F] Vec (p+1) := a.ker.subtype.comp E.toLinearMap
  have hR : ∀ q, a (R q) = 0 := fun q => LinearMap.mem_ker.mp (E q).property
  refine ⟨R, v, a.ker.subtype_injective.comp E.injective, hv, hR, ?_⟩
  intro q c
  simp [hR, hv, CharTwo.add_self_eq_zero]

end PEqualNP.Outside.L_meta_32579_aux.RowPort.PivotStep

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.CubeParity

open scoped BigOperators
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

def toggle {d : ℕ} (i : Fin d) (w : Vec d) : Vec d :=
  Function.update w i (w i + 1)

theorem toggle_involutive {d : ℕ} (i : Fin d) : Function.Involutive (toggle i) := by
  intro w
  ext j
  by_cases h : j = i
  · subst j
    simp [toggle, add_assoc, CharTwo.add_self_eq_zero]
  · simp [toggle, Function.update_of_ne h]

theorem sum_zero_of_toggle {d : ℕ} (i : Fin d) (f : Vec d → F)
    (hf : ∀ w, f (toggle i w) = f w) : (∑ w, f w) = 0 := by
  let E : Vec d ≃ Vec d := ⟨toggle i, toggle i, toggle_involutive i, toggle_involutive i⟩
  have h : (∑ w : Vec d, f w * w i) = ∑ w : Vec d, f w * (w i + 1) := by
    apply Fintype.sum_equiv E
    intro w
    change f w * w i = f (toggle i w) * (toggle i w i + 1)
    rw [hf]
    simp [toggle, add_assoc, CharTwo.add_self_eq_zero]
  calc
    (∑ w, f w) = ∑ w : Vec d, (f w * w i + f w * (w i + 1)) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [← mul_add]
      simp [add_assoc, ← add_assoc (w i), CharTwo.add_self_eq_zero]
    _ = (∑ w : Vec d, f w * w i) + (∑ w : Vec d, f w * (w i + 1)) :=
      Finset.sum_add_distrib
    _ = 0 := h ▸ CharTwo.add_self_eq_zero _

theorem sum_monomial_eq_zero {d : ℕ} (S : Finset (Fin d)) (hS : S.card < d) (c : F) :
    (∑ w : Vec d, c * ∏ i ∈ S, w i) = 0 := by
  classical
  have hmiss : ∃ i : Fin d, i ∉ S := by
    by_contra h
    push Not at h
    have hu : S = Finset.univ := Finset.eq_univ_of_forall h
    simp [hu] at hS
  obtain ⟨i, hi⟩ := hmiss
  apply sum_zero_of_toggle i
  intro w
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun he => hi (he ▸ hj)
  simp [toggle, Function.update_of_ne hji]

end PEqualNP.Outside.L_meta_32579_aux.RowPort.CubeParity

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan
open scoped BigOperators
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F
abbrev Fn (n : ℕ) := Vec n → F

def mono {n : ℕ} (S : Finset (Fin n)) : Fn n := fun x => ∏ i ∈ S, x i

def degree (n q : ℕ) : Submodule F (Fn n) :=
  Submodule.span F { f | ∃ S : Finset (Fin n), S.card ≤ q ∧ mono S = f }

theorem mono_mem {n q} (S : Finset (Fin n)) (hS : S.card ≤ q) : mono S ∈ degree n q :=
  Submodule.subset_span ⟨S,hS,rfl⟩

theorem degree_mono {n a b : ℕ} (hab : a ≤ b) : degree n a ≤ degree n b := by
  apply Submodule.span_mono
  rintro x ⟨S,hS,rfl⟩
  exact ⟨S,hS.trans hab,rfl⟩

theorem constant {n q : ℕ} (c : F) : (fun _ : Vec n => c) ∈ degree n q := by
  have h := (degree n q).smul_mem c (mono_mem ∅ (Nat.zero_le q) : mono (∅ : Finset (Fin n)) ∈ degree n q)
  have he : c • mono (∅ : Finset (Fin n)) = (fun _ : Vec n => c) := by
    funext w
    simp [mono]
  rwa [he] at h

theorem coordinate {n : ℕ} (i : Fin n) : (fun w : Vec n => w i) ∈ degree n 1 := by
  have he : mono ({i} : Finset (Fin n)) = (fun w : Vec n => w i) := by
    funext w
    simp [mono]
  rw [← he]
  exact mono_mem {i} (by simp)

private theorem char_idem (q : F) : q*q=q := (by decide : ∀ q : F, q*q=q) q

theorem mono_mul {n : ℕ} (S T : Finset (Fin n)) : mono S * mono T = mono (S ∪ T) := by
  classical
  funext x
  induction T using Finset.induction_on with
  | empty => simp [mono]
  | insert a T ha ih =>
    by_cases hs : a ∈ S
    · have hu : a ∈ S ∪ T := Finset.mem_union_left T hs
      have hdup : x a * (∏ i ∈ S ∪ T, x i) = ∏ i ∈ S ∪ T, x i := by
        rw [← Finset.insert_erase hu, Finset.prod_insert (Finset.notMem_erase _ _), ← mul_assoc,
          char_idem]
      change (∏ i ∈ S, x i) * (∏ i ∈ insert a T, x i) = ∏ i ∈ S ∪ insert a T, x i
      change (∏ i ∈ S, x i) * (∏ i ∈ T, x i) = ∏ i ∈ S ∪ T, x i at ih
      rw [Finset.prod_insert ha, ← mul_left_comm, ih]
      rw [show S ∪ insert a T = S ∪ T by
        ext j
        simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inl (h.symm ▸ hs)
          · exact Or.inr h
        · tauto]
      exact hdup
    · have hn : a ∉ S ∪ T := by simp [hs,ha]
      change (∏ i ∈ S, x i) * (∏ i ∈ insert a T, x i) = ∏ i ∈ S ∪ insert a T, x i
      change (∏ i ∈ S, x i) * (∏ i ∈ T, x i) = ∏ i ∈ S ∪ T, x i at ih
      rw [Finset.prod_insert ha, ← mul_left_comm, ih, Finset.union_insert, Finset.prod_insert hn]


theorem degree_mul {n a b : ℕ} {f g : Fn n}
    (hf : f ∈ degree n a) (hg : g ∈ degree n b) :
    f * g ∈ degree n (a+b) := by
  let W := degree n (a+b)
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ => f * g ∈ W) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    change g ∈ Submodule.span F _ at hg
    refine Submodule.span_induction (p := fun g _ => mono S * g ∈ W) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨T,hT,rfl⟩
      rw [mono_mul]
      exact mono_mem _ ((Finset.card_union_le S T).trans (Nat.add_le_add hS hT))
    · simpa using W.zero_mem
    · intro f g _ _ hf hg
      rw [mul_add]
      exact W.add_mem hf hg
    · intro c x _ hx
      have he : mono S * (c • x) = c • (mono S * x) := by
        funext y
        change (mono S y) * (c * x y) = c * (mono S y * x y)
        exact mul_left_comm _ _ _
      rw [he]
      exact W.smul_mem c hx
  · simpa using W.zero_mem
  · intro f g _ _ hf hg
    rw [add_mul]
    exact W.add_mem hf hg
  · intro c x _ hx
    have he : (c • x) * g = c • (x*g) := by
      funext y
      change (c * x y) * g y = c * (x y * g y)
      exact mul_assoc _ _ _
    rw [he]
    exact W.smul_mem c hx

theorem parity {n q : ℕ} {f : Fn n} (hf : f ∈ degree n q) (hqn : q < n) :
    (∑ w, f w) = 0 := by
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ => (∑ w, f w) = 0) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    simpa [mono] using PEqualNP.Outside.L_meta_32579_aux.RowPort.CubeParity.sum_monomial_eq_zero S (hS.trans_lt hqn) 1
  · simp
  · intro a b _ _ ha hb
    simp [Pi.add_apply, Finset.sum_add_distrib, ha, hb]
  · intro c a _ ha
    simp [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ha]

end PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.ParityBudget
open scoped BigOperators
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan

private theorem linear_mem {d : ℕ} (L : Vec d →ₗ[F] F) : (fun w => L w) ∈ degree d 1 := by
  classical
  have he (w : Vec d) : w = ∑ j : Fin d, w j • (Pi.single j 1 : Vec d) := by
    funext i
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_ite_eq']
  have hL (w : Vec d) : L w = ∑ j : Fin d, L (Pi.single j 1) * w j := by
    conv_lhs => rw [he w]
    simp [map_sum, smul_eq_mul, mul_comm]
  let g : Fin d → Fn d := fun j => L (Pi.single j 1) • (fun w => w j)
  have hL' : (fun w => L w) = ∑ j : Fin d, g j := by
    funext w
    simpa [g, Finset.sum_apply] using hL w
  rw [hL']
  apply Submodule.sum_mem
  intro j _
  exact (degree d 1).smul_mem _ (coordinate j)

theorem affine_mem {d : ℕ} (c : F) (L : Vec d →ₗ[F] F) :
    (fun w => c + L w) ∈ degree d 1 :=
  (degree d 1).add_mem (constant c) (linear_mem L)

theorem affine_cube_budget {d k r : ℕ} (A : Vec d →ₗ[F] Vec k)
    (y₀ : Vec k) (b : Fin k → Fn d) (h : Fn d)
    (hb : ∀ i, b i ∈ degree d (r+1))
    (hh : h ∈ degree d (r+1))
    (hsum : (∑ w : Vec d, (h w + ∑ i : Fin k, (y₀ i + A w i) * b i w)) = 1) :
    d ≤ r + (if A = 0 then 1 else 2) := by
  classical
  let q : ℕ := if A = 0 then 0 else 1
  have hy : ∀ i : Fin k, (fun w : Vec d => y₀ i + A w i) ∈ degree d q := by
    intro i
    by_cases ha : A = 0
    · simpa [q,ha] using (constant (n := d) (q := 0) (y₀ i))
    · have hp := affine_mem (y₀ i) ((LinearMap.proj i).comp A)
      simpa [q,ha] using hp
  let u : Fin k → Fn d := fun i => (fun w => y₀ i + A w i) * b i
  have hprod : ∀ i, u i ∈ degree d (r+1+q) := by
    intro i
    have hi := degree_mul (hb i) (hy i)
    simpa [u, mul_comm] using hi
  have hu : (∑ i : Fin k, u i) ∈ degree d (r+1+q) := by
    apply Submodule.sum_mem
    intro i _
    exact hprod i
  have hde := (degree d (r+1+q)).add_mem (degree_mono (Nat.le_add_right _ _) hh) hu
  have he : h + (∑ i : Fin k, u i) = (fun w : Vec d =>
      h w + ∑ i : Fin k, (y₀ i + A w i) * b i w) := by
    funext w
    simp [u,Finset.sum_apply]
  rw [he] at hde
  have hn : d ≤ r+1+q := by
    by_contra ht
    push Not at ht
    have hz := parity hde ht
    rw [hsum] at hz
    contradiction
  by_cases e : A = 0
  · simpa [q,e] using hn
  · simpa [q,e, Nat.add_assoc] using hn

end PEqualNP.Outside.L_meta_32579_aux.RowPort.ParityBudget

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.Substitute
open scoped BigOperators
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan

def front {n : ℕ} (H : Fn n) (w : Vec n) : Vec (n+1) :=
  Fin.cases (H w) w

theorem substitute {n q : ℕ} (H : Fn n) (hH : H ∈ degree n 2)
    {f : Fn (n+1)} (hf : f ∈ degree (n+1) q) :
    (fun w => f (front H w)) ∈ degree n (q+1) := by
  classical
  let W := degree n (q+1)
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ => (fun w => f (front H w)) ∈ W)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    let U : Finset (Fin n) := (S.erase 0).preimage Fin.succ (Fin.succ_injective n).injOn
    have huI : U.image Fin.succ = S.erase 0 := by
      ext i
      cases i using Fin.cases with
      | zero => simp [U]
      | succ i => simp [U]
    have huC : U.card = (S.erase 0).card := by
      rw [← huI, Finset.card_image_of_injective U (Fin.succ_injective n)]
    have huP (w : Vec n) : (∏ i ∈ S.erase 0, front H w i) = mono U w := by
      rw [← huI, Finset.prod_image (Fin.succ_injective n).injOn]
      rfl
    by_cases hz : 0 ∈ S
    · have hU : U.card + 1 ≤ q := by
        rw [huC, Finset.card_erase_of_mem hz]
        have hp : 0 < S.card := Finset.card_pos.mpr ⟨0,hz⟩
        omega
      have hform : (fun w => mono S (front H w)) = mono U * H := by
        funext w
        change (∏ i ∈ S, front H w i) = mono U w * H w
        rw [← Finset.prod_erase_mul S (fun i => front H w i) hz, huP]
        rfl
      rw [hform]
      exact degree_mono (by omega) (degree_mul (mono_mem U (le_refl _)) hH)
    · have hU : U.card ≤ q := by
        rwa [huC, Finset.erase_eq_of_notMem hz]
      have hform : (fun w => mono S (front H w)) = mono U := by
        funext w
        simpa only [mono, Finset.erase_eq_of_notMem hz] using huP w
      rw [hform]
      exact mono_mem U (by omega)
  · exact W.zero_mem
  · intro a b _ _ ha hb
    exact W.add_mem ha hb
  · intro c a _ ha
    exact W.smul_mem c ha

end PEqualNP.Outside.L_meta_32579_aux.RowPort.Substitute

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.ProgramDegree
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan PEqualNP.Outside.L_meta_32579_aux.RowPort.Substitute PEqualNP.Outside.L_meta_32579_aux.RowPort.ParityBudget

inductive Run (n : ℕ) : ∀ r : ℕ, (Vec n → Vec (n+r)) → Prop
  | nil : Run n 0 id
  | cons {r : ℕ} {f : Vec n → Vec (n+r)} (hf : Run n r f)
      (a b : Fn (n+r)) (ha : a ∈ degree (n+r) 1) (hb : b ∈ degree (n+r) 1) :
      Run n (r+1) (fun w => front (a*b) (f w))

theorem degree_run {n r : ℕ} {g : Vec n → Vec (n+r)} (hg : Run n r g) :
    ∀ q, ∀ f : Fn (n+r), f ∈ degree (n+r) q → (fun w => f (g w)) ∈ degree n (q+r) := by
  induction hg with
  | nil =>
    intro q f hf
    simpa using hf
  | @cons r f h a b ha hb ih =>
    intro q fi hi
    have hp := degree_mul ha hb
    have h₀ := substitute (a*b) hp hi
    have h₁ := ih (q+1) (fun w => fi (front (a*b) w)) h₀
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h₁

end PEqualNP.Outside.L_meta_32579_aux.RowPort.ProgramDegree

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.SpanExact
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan

theorem as_affine {n : ℕ} {f : Fn n} (hf : f ∈ degree n 1) :
    ∃ (c : F) (L : Vec n →ₗ[F] F), ∀ w, f w = c + L w := by
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ =>
    ∃ (c : F) (L : Vec n →ₗ[F] F), ∀ w, f w = c + L w) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    by_cases he : S = ∅
    · refine ⟨1,0,?_⟩
      intro w
      simp [mono,he]
    · have hcard : S.card = 1 := by
        have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        omega
      obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp hcard
      exact ⟨0, LinearMap.proj j, by intro w; simp [mono]⟩
  · exact ⟨0,0,by simp⟩
  · rintro f g _ _ ⟨c,L,h⟩ ⟨d,K,hk⟩
    refine ⟨c+d,L+K,?_⟩
    intro w
    simp only [Pi.add_apply, LinearMap.add_apply, h, hk]
    abel
  · rintro c f _ ⟨d,L,h⟩
    refine ⟨c*d,c • L,?_⟩
    intro w
    simp [h, mul_add]

theorem iff_affine {n : ℕ} {f : Fn n} :
    f ∈ degree n 1 ↔ ∃ (c : F) (L : Vec n →ₗ[F] F), ∀ w, f w = c + L w := by
  refine ⟨as_affine, ?_⟩
  rintro ⟨c,L,h⟩
  rw [show f = (fun w => c + L w) from funext h]
  exact PEqualNP.Outside.L_meta_32579_aux.RowPort.ParityBudget.affine_mem c L

end PEqualNP.Outside.L_meta_32579_aux.RowPort.SpanExact

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.Wire
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan PEqualNP.Outside.L_meta_32579_aux.RowPort.SpanExact PEqualNP.Outside.L_meta_32579_aux.RowPort.Substitute

structure Wire (p n : ℕ) where
  x : Vec p →ₗ[F] F
  tail : Fn n
  tail_aff : tail ∈ degree n 1

def eval {p n : ℕ} (a : Wire p n) (q : Vec p) (w : Vec n) : F :=
  a.x q + a.tail w

def shift {p n : ℕ} (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1))
    (pivot : Fn n) (hp : pivot ∈ degree n 1) (a : Wire (p+1) n) : Wire p n :=
  ⟨a.x.comp R, a.tail + (a.x v) • pivot,
    (degree n 1).add_mem a.tail_aff ((degree n 1).smul_mem _ hp)⟩

theorem shift_eval {p n : ℕ} (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1))
    (pivot : Fn n) (hp : pivot ∈ degree n 1) (a : Wire (p+1) n)
    (q : Vec p) (w : Vec n) :
    eval (shift R v pivot hp a) q w = eval a (R q + pivot w • v) w := by
  simp [eval, shift, smul_eq_mul, mul_comm]
  abel

theorem kill_factor {p n : ℕ} (a : Wire (p+1) n) (ha : a.x ≠ 0) :
    ∃ (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1)),
      Function.Injective R ∧ ∀ q w,
        eval (shift R v a.tail a.tail_aff a) q w = 0 := by
  obtain ⟨R,v,hR,_,_,hp⟩ := PEqualNP.Outside.L_meta_32579_aux.RowPort.PivotStep.solve_one a.x ha
  refine ⟨R,v,hR,?_⟩
  intro q w
  rw [shift_eval]
  exact hp q (a.tail w)

private def tailLinear (n : ℕ) : Vec (n+1) →ₗ[F] Vec n :=
  LinearMap.pi (fun i => LinearMap.proj i.succ)

def extend {p n : ℕ} (a : Wire p n) : Wire p (n+1) where
  x := a.x
  tail := fun w => a.tail (tailLinear n w)
  tail_aff := by
    obtain ⟨c,L,h⟩ := as_affine a.tail_aff
    apply iff_affine.mpr
    exact ⟨c, L.comp (tailLinear n), fun w => h _⟩

theorem extend_eval {p n : ℕ} (a : Wire p n) (H : Fn n) (q : Vec p) (w : Vec n) :
    eval (extend a) q (front H w) = eval a q w := by
  rfl

def retained {p n : ℕ} : Wire p (n+1) :=
  ⟨0, (fun w => w 0), coordinate 0⟩

theorem retained_eval {p n : ℕ} (H : Fn n) (q : Vec p) (w : Vec n) :
    eval retained q (front H w) = H w := by
  simp [eval, retained, front]

end PEqualNP.Outside.L_meta_32579_aux.RowPort.Wire

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.GateDecode
open PEqualNP.CircuitLowerBounds
abbrev F := ZMod 2

def bit (x : F) : Bool := decide (x = 1)

def costly (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

def legal (g : Gate) : Prop := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

-- At most two affine input terms and a product term, whose presence is exactly the budget.
def ops (g : Gate) (a b : F) : F :=
  match g.op, g.inputs with
  | .and, [] => 1
  | .and, [_] => a
  | .and, _ :: _ :: _ => a*b
  | .or, [] => 0
  | .or, [_] => a
  | .or, _ :: _ :: _ => a+b+a*b
  | .mod _, [] => 1
  | .mod _, [_] => 1+a
  | .mod _, _ :: _ :: _ => 1+a+b
  | .not, _ => 1+a
  | .maj, _ => 0

private theorem and1 : ∀ a : F, GateOp.and.eval [bit a] = bit a := by decide +kernel
private theorem or1 : ∀ a : F, GateOp.or.eval [bit a] = bit a := by decide +kernel
private theorem and2 : ∀ a b : F, GateOp.and.eval [bit a,bit b] = bit (a*b) := by decide +kernel
private theorem or2 : ∀ a b : F, GateOp.or.eval [bit a,bit b] = bit (a+b+a*b) := by decide +kernel
private theorem mod1 : ∀ a : F, (GateOp.mod 2).eval [bit a] = bit (1+a) := by decide +kernel
private theorem mod2 : ∀ a b : F, (GateOp.mod 2).eval [bit a,bit b] = bit (1+a+b) := by decide +kernel
private theorem not1 : ∀ a : F, GateOp.not.eval [bit a] = bit (1+a) := by decide +kernel

theorem decode (g : Gate) (u : ℕ → F) (h : legal g) :
    g.op.eval (g.inputs.map fun i => bit (u i)) =
      bit (ops g (u (g.inputs.getD 0 0)) (u (g.inputs.getD 1 0))) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hs,ho⟩ := h
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ ins.length = 1) at ho
  change ins.length ≤ 2 at hs
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k,is⟩⟩⟩
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> first | rfl | simp at h
  · rcases ho with rfl | rfl | rfl | ⟨rfl,_⟩
    · exact and1 (u i)
    · exact or1 (u i)
    · exact mod1 (u i)
    · exact not1 (u i)
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩
    · exact and2 (u i) (u j)
    · exact or2 (u i) (u j)
    · exact mod2 (u i) (u j)
    · simp at h
  · simp at hs

end PEqualNP.Outside.L_meta_32579_aux.RowPort.GateDecode

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.WireOps
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan PEqualNP.Outside.L_meta_32579_aux.RowPort.Wire

def zeroCostConst {p n : ℕ} (c : F) : Wire p n :=
  ⟨0, fun _ => c, constant c⟩

def plus {p n : ℕ} (a b : Wire p n) : Wire p n :=
  ⟨a.x+b.x, a.tail+b.tail, (degree n 1).add_mem a.tail_aff b.tail_aff⟩

theorem const_eval {p n} (c : F) (q : Vec p) (w : Vec n) :
    eval (zeroCostConst c) q w = c := by simp [eval,zeroCostConst]

theorem plus_eval {p n} (a b : Wire p n) (q : Vec p) (w : Vec n) :
    eval (plus a b) q w = eval a q w + eval b q w := by
  simp [plus, eval]
  abel

theorem factor_value_of_zero {p n} (a : Wire p n) (h : a.x = 0) (q : Vec p) (w : Vec n) :
    eval a q w = a.tail w := by simp [eval,h]

theorem retain_product {p n} (a b : Wire p n) (ha : a.x = 0) (hb : b.x = 0)
    (q : Vec p) (w : Vec n) :
    eval retained q (PEqualNP.Outside.L_meta_32579_aux.RowPort.Substitute.front (a.tail*b.tail) w) = eval a q w * eval b q w := by
  rw [retained_eval, factor_value_of_zero a ha, factor_value_of_zero b hb]
  rfl

end PEqualNP.Outside.L_meta_32579_aux.RowPort.WireOps

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.Normalized
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan PEqualNP.Outside.L_meta_32579_aux.RowPort.Wire PEqualNP.Outside.L_meta_32579_aux.RowPort.WireOps PEqualNP.Outside.L_meta_32579_aux.RowPort.Substitute
open PEqualNP.Outside.L_meta_32579_aux.RowPort.ProgramDegree

inductive Expr where
  | cn : F → Expr
  | rd : ℕ → Expr
  | add : Expr → Expr → Expr

def Expr.val (w : List F) : Expr → F
  | .cn c => c
  | .rd i => w.getD i 0
  | .add a b => a.val w + b.val w

def Expr.compile {p n : ℕ} (w : List (Wire p n)) : Expr → Wire p n
  | .cn c => zeroCostConst c
  | .rd i => w.getD i (zeroCostConst 0)
  | .add a b => plus (a.compile w) (b.compile w)

theorem list_getD_eval {p n : ℕ} (w : List (Wire p n)) (q : Vec p) (u : Vec n) (i : ℕ) :
    eval (w.getD i (zeroCostConst 0)) q u =
      (w.map fun z => eval z q u).getD i 0 := by
  induction w generalizing i with
  | nil => simp [const_eval]
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem Expr.compile_val {p n : ℕ} (w : List (Wire p n)) (q : Vec p) (u : Vec n) (e : Expr) :
    eval (e.compile w) q u = e.val (w.map fun z => eval z q u) := by
  induction e with
  | cn c => exact const_eval c q u
  | rd i => exact list_getD_eval w q u i
  | add a b ha hb => simp [Expr.compile, Expr.val, plus_eval, ha, hb]

inductive Ins where
  | free : Expr → Ins
  | paid : Expr → Expr → Expr → Ins

def Ins.cost : Ins → ℕ
  | .free _ => 0
  | .paid _ _ _ => 1

def Ins.val (w : List F) : Ins → F
  | .free e => e.val w
  | .paid e a b => e.val w + a.val w * b.val w

def Ins.step (w : List F) (g : Ins) : List F := w ++ [g.val w]

def embed {k p n : ℕ} (x : Fin k → Wire p n) : Vec p →ₗ[F] Vec k :=
  LinearMap.pi fun i => (x i).x

structure State (b k p r : ℕ) where
  env : Vec b → Vec (b+r)
  hEnv : Run b r env
  orig : Fin k → Wire p (b+r)
  hOrig : Function.Injective (embed orig)
  regs : List (Wire p (b+r))

def State.args {b k p r} (S : State b k p r) (q : Vec p) (u : Vec b) : Vec k :=
  fun i => eval (S.orig i) q (S.env u)

def State.values {b k p r} (S : State b k p r) (q : Vec p) (u : Vec b) : List F :=
  S.regs.map fun z => eval z q (S.env u)

def State.free {b k p r} (S : State b k p r) (e : Expr) : State b k p r :=
  { S with regs := S.regs ++ [e.compile S.regs] }

theorem State.free_ok {b k p r} (S : State b k p r) (e : Expr) (q : Vec p) (u : Vec b) :
    (S.free e).args q u = S.args q u ∧
    (S.free e).values q u = Ins.step (S.values q u) (.free e) := by
  refine ⟨rfl, ?_⟩
  simp [State.free, State.values, Ins.step, Ins.val, Expr.compile_val]

def State.retain {b k p r} (S : State b k p r) (e a c : Expr) : State b k p (r+1) :=
  let a' := a.compile S.regs
  let c' := c.compile S.regs
  ⟨fun u => front (a'.tail*c'.tail) (S.env u),
    .cons S.hEnv a'.tail c'.tail a'.tail_aff c'.tail_aff,
    fun i => extend (S.orig i), S.hOrig,
    (S.regs.map extend) ++ [plus (extend (e.compile S.regs)) retained]⟩

theorem State.retain_ok {b k p r} (S : State b k p r) (e a c : Expr)
    (ha : (a.compile S.regs).x = 0) (hc : (c.compile S.regs).x = 0)
    (q : Vec p) (u : Vec b) :
    (S.retain e a c).args q u = S.args q u ∧
    (S.retain e a c).values q u = Ins.step (S.values q u) (.paid e a c) := by
  constructor
  · funext i
    exact extend_eval (S.orig i) _ q (S.env u)
  · unfold State.retain State.values Ins.step Ins.val
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
      plus_eval, extend_eval]
    rw [retain_product _ _ ha hc]
    simp [Expr.compile_val, extend_eval]

def State.discard {b k p r} (S : State b k (p+1) r) (e : Expr)
  (R : Vec p →ₗ[F] Vec (p+1)) (hR : Function.Injective R) (v : Vec (p+1))
  (pivot : Wire (p+1) (b+r)) : State b k p r :=
  let f := shift R v pivot.tail pivot.tail_aff
  ⟨S.env, S.hEnv, fun i => f (S.orig i), S.hOrig.comp hR,
    (S.regs.map f) ++ [f (e.compile S.regs)]⟩


theorem State.discard_ok {b k p r} (S : State b k (p+1) r) (e a c : Expr)
    (R : Vec p →ₗ[F] Vec (p+1)) (hR : Function.Injective R) (v : Vec (p+1))
    (pivot : Wire (p+1) (b+r)) (q : Vec p) (u : Vec b)
    (hz : eval (shift R v pivot.tail pivot.tail_aff (a.compile S.regs)) q (S.env u) *
          eval (shift R v pivot.tail pivot.tail_aff (c.compile S.regs)) q (S.env u) = 0) :
    let q₀ := R q + pivot.tail (S.env u) • v
    (S.discard e R hR v pivot).args q u = S.args q₀ u ∧
    (S.discard e R hR v pivot).values q u = Ins.step (S.values q₀ u) (.paid e a c) := by
  dsimp only
  constructor
  · funext i
    exact shift_eval R v pivot.tail pivot.tail_aff (S.orig i) q (S.env u)
  · unfold State.discard State.values Ins.step Ins.val
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
      shift_eval]
    simp only [shift_eval] at hz
    simp [← Expr.compile_val, hz, shift_eval]

theorem zero_direction {n} (a : Wire 0 n) : a.x = 0 := by
  apply LinearMap.ext
  intro q
  have hq : q = 0 := Subsingleton.elim _ _
  rw [hq]
  exact map_zero a.x

theorem advance {b k p r} (S : State b k p r) (g : Ins) :
    ∃ (p' r' : ℕ) (S' : State b k p' r'),
      p+r' = p'+r+g.cost ∧
      ∀ q u, ∃ q₀, S'.args q u = S.args q₀ u ∧ S'.values q u = g.step (S.values q₀ u) := by
  cases g with
  | free e =>
    exact ⟨p,r,S.free e,by simp [Ins.cost],fun q u => ⟨q,S.free_ok e q u⟩⟩
  | paid e a c =>
    let aa := a.compile S.regs
    let cc := c.compile S.regs
    by_cases both : aa.x = 0 ∧ cc.x = 0
    · refine ⟨p,r+1,S.retain e a c,by simp [Ins.cost, Nat.add_assoc],?_⟩
      intro q u
      exact ⟨q,S.retain_ok e a c both.1 both.2 q u⟩
    · cases p with
      | zero => exact False.elim (both ⟨zero_direction aa,zero_direction cc⟩)
      | succ p =>
        have usePivot (z : Wire (p+1) (b+r)) (hz : z.x ≠ 0) (hz' : z = aa ∨ z = cc) :
            ∃ (p' r' : ℕ) (S' : State b k p' r'),
              (p+1)+r' = p'+r+(.paid e a c : Ins).cost ∧
              ∀ q u, ∃ q₀, S'.args q u = S.args q₀ u ∧
                S'.values q u = (.paid e a c : Ins).step (S.values q₀ u) := by
          obtain ⟨R,v,hR,hkill⟩ := kill_factor z hz
          refine ⟨p,r,S.discard e R hR v z,by simp only [Ins.cost]; omega,?_⟩
          intro q u
          have hh := hkill q (S.env u)
          refine ⟨_,S.discard_ok e a c R hR v z q u ?_⟩
          rcases hz' with h | h
          · subst z
            change _ at hh
            change eval (shift R v aa.tail aa.tail_aff aa) q (S.env u) *
              eval (shift R v aa.tail aa.tail_aff cc) q (S.env u) = 0
            rw [hh,zero_mul]
          · subst z
            change eval (shift R v cc.tail cc.tail_aff aa) q (S.env u) *
              eval (shift R v cc.tail cc.tail_aff cc) q (S.env u) = 0
            rw [hh,mul_zero]
        by_cases h : aa.x = 0
        · exact usePivot cc (fun z => both ⟨h,z⟩) (Or.inr rfl)
        · exact usePivot aa h (Or.inl rfl)

def paidCount (gs : List Ins) : ℕ := (gs.map Ins.cost).sum

theorem advance_all {b k : ℕ} (gs : List Ins) :
    ∀ p r (S : State b k p r),
      ∃ (p' r' : ℕ) (S' : State b k p' r'),
        p+r' = p'+r+paidCount gs ∧
        ∀ q u, ∃ q₀, S'.args q u = S.args q₀ u ∧
          S'.values q u = gs.foldl Ins.step (S.values q₀ u) := by
  induction gs with
  | nil =>
    intro p r S
    exact ⟨p,r,S,by simp [paidCount],fun q _ => ⟨q,rfl,rfl⟩⟩
  | cons g t ih =>
    intro p r S
    obtain ⟨p₁,r₁,S₁,h₁,e₁⟩ := advance S g
    obtain ⟨p₂,r₂,S₂,h₂,e₂⟩ := ih p₁ r₁ S₁
    refine ⟨p₂,r₂,S₂,?_ ,?_⟩
    · simp only [paidCount,List.map_cons,List.sum_cons] at *
      omega
    · intro q u
      obtain ⟨q₁,ha,hw⟩ := e₂ q u
      obtain ⟨q₀,ha₀,hw₀⟩ := e₁ q₁ u
      exact ⟨q₀,ha.trans ha₀,by rw [List.foldl_cons,hw,hw₀]⟩

end PEqualNP.Outside.L_meta_32579_aux.RowPort.Normalized

namespace PEqualNP.Outside.L_meta_32579_aux.RowPort.CircuitBridge
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32579_aux.RowPort.Normalized PEqualNP.Outside.L_meta_32579_aux.RowPort.GateDecode

private def free0 (x : F) : Ins := .free (.cn x)
private def read (i : ℕ) : Ins := .free (.rd i)
private def neg (i : ℕ) : Ins := .free (.add (.cn 1) (.rd i))

def lower (g : Gate) : Ins :=
  match g.op, g.inputs with
  | .and, [] => free0 1
  | .or, [] => free0 0
  | .and, [i] | .or, [i] => read i
  | .and, i :: j :: _ => .paid (.cn 0) (.rd i) (.rd j)
  | .or, i :: j :: _ => .paid (.add (.rd i) (.rd j)) (.rd i) (.rd j)
  | .mod _, [] => free0 1
  | .mod _, [i] => neg i
  | .mod _, i :: j :: _ => .free (.add (.add (.cn 1) (.rd i)) (.rd j))
  | .not, i :: _ => neg i
  | _, _ => free0 0

theorem lower_ops (g : Gate) (w : List F) (hg : legal g) :
    (lower g).val w =
      ops g (w.getD (g.inputs.getD 0 0) 0) (w.getD (g.inputs.getD 1 0) 0) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hs,ho⟩ := hg
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ ins.length = 1) at ho
  change ins.length ≤ 2 at hs
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k,is⟩⟩⟩
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> first | rfl | simp at h
  · rcases ho with rfl | rfl | rfl | ⟨rfl,_⟩ <;> rfl
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩
    · simp [lower, ops, Ins.val, Expr.val]
    · rfl
    · rfl
    · simp at h
  · simp at hs

private theorem bit_zero : bit 0 = false := by decide

private theorem getD_map_bit (w : List F) (i : ℕ) :
    (w.map bit).getD i false = bit (w.getD i 0) := by
  induction w generalizing i with
  | nil => simp [bit_zero]
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_bridge (g : Gate) (w : List F) (h : legal g) :
    stepBool (w.map bit) g = ((lower g).step w).map bit := by
  unfold stepBool Ins.step
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_cancel_left_eq]
  simp only [getD_map_bit]
  rw [decode g _ h, lower_ops g w h]

theorem fold_bridge (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List F) :
    gs.foldl stepBool (w.map bit) = ((gs.map lower).foldl Ins.step w).map bit := by
  induction gs generalizing w with
  | nil => rfl
  | cons g t ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [step_bridge g w (hg g (by simp))]
    exact ih (fun a ha => hg a (List.mem_cons_of_mem _ ha)) _

theorem eval_bridge (C : Circuit) (hg : ∀ g ∈ C.gates, legal g) (w : List F) :
    C.eval (w.map bit) = bit (((C.gates.map lower).foldl Ins.step w).getD C.output 0) := by
  change (C.gates.foldl stepBool (w.map bit)).getD C.output false = _
  rw [fold_bridge C.gates hg, getD_map_bit]

noncomputable def paid (g : Gate) : Bool := @decide (costly g) (Classical.propDecidable _)

theorem cost_one (g : Gate) (hg : legal g) :
    (lower g).cost = @ite ℕ (costly g) (Classical.propDecidable _) 1 0 := by
  classical
  obtain ⟨op,ins⟩ := g
  obtain ⟨hs,ho⟩ := hg
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ ins.length = 1) at ho
  change ins.length ≤ 2 at hs
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k,is⟩⟩⟩
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> simp [lower,costly,Ins.cost,free0] at *
  · rcases ho with rfl | rfl | rfl | ⟨rfl,_⟩ <;> simp [lower,costly,Ins.cost,read,neg]
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> simp [lower,costly,Ins.cost] at *
  · simp at hs

theorem cost_bridge (gs : List Gate) (hg : ∀ g ∈ gs, legal g) :
    paidCount (gs.map lower) = gs.countP paid := by
  classical
  induction gs with
  | nil => rfl
  | cons g t ih =>
    have ht := ih (fun a ha => hg a (List.mem_cons_of_mem _ ha))
    simp only [paidCount,List.map_cons,List.sum_cons,List.countP_cons]
    change (lower g).cost + paidCount (t.map lower) = _
    rw [cost_one g (hg g (by simp)), ht]
    by_cases h : costly g <;> simp [paid,h,Nat.add_comm]

end PEqualNP.Outside.L_meta_32579_aux.RowPort.CircuitBridge


namespace PEqualNP.Outside.L_meta_32579_aux.Row

open scoped BigOperators
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan
open PEqualNP.Outside.L_meta_32579_aux.RowPort.Wire
open PEqualNP.Outside.L_meta_32579_aux.RowPort.WireOps
open PEqualNP.Outside.L_meta_32579_aux.RowPort.Normalized
open PEqualNP.Outside.L_meta_32579_aux.RowPort.ProgramDegree
open PEqualNP.Outside.L_meta_32579_aux.RowPort.CircuitBridge
open PEqualNP.Outside.L_meta_32579_aux.RowPort.GateDecode (bit legal)

noncomputable def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

theorem vec_card (d : ℕ) : Fintype.card (Vec d) = 2^d := by
  simp [Fintype.card_fun]

theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (f : β → ℝ) : mean (fun x => f (e x)) = mean f := by
  unfold mean
  rw [Fintype.card_congr e, Equiv.sum_comp]

theorem mean_F_prod {α : Type*} [Fintype α] (f : F × α → ℝ) :
    mean f = (mean (fun a => f (0,a)) + mean (fun a => f (1,a))) / 2 := by
  unfold mean
  have h : (∑ a : F, ∑ x : α, f (a,x)) = (∑ x : α, f (0,x)) + (∑ x : α, f (1,x)) := by
    rw [show (Finset.univ : Finset F) = {0,1} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [Fintype.sum_prod_type, h, Fintype.card_prod, ZMod.card, Nat.cast_mul]
  push_cast
  ring

noncomputable def phase (a : F) : ℝ := if a = 1 then -1 else 1

theorem phase_add (a b : F) : phase (a+b) = phase a * phase b := by
  have hs : ∀ x : F, x = 0 ∨ x = 1 := by decide
  rcases hs a with rfl | rfl <;> rcases hs b with rfl | rfl <;>
    (try rw [CharTwo.add_self_eq_zero]) <;> norm_num [phase]

theorem phase_zero : phase 0 = 1 := by norm_num [phase]

theorem phase_one : phase 1 = -1 := by norm_num [phase]

theorem phase_agree (a b : F) :
    (if bit a = bit b then (1 : ℝ) else -1) = phase (a+b) := by
  have hs : ∀ x : F, x = 0 ∨ x = 1 := by decide
  rcases hs a with rfl | rfl <;> rcases hs b with rfl | rfl <;>
    (try rw [CharTwo.add_self_eq_zero]) <;> norm_num [phase, bit]

private theorem pivot_bijective {p : ℕ} (R : Vec p →ₗ[F] Vec (p+1)) (hR : Function.Injective R)
    (L : Vec (p+1) →ₗ[F] F) (v : Vec (p+1)) (hv : L v = 1)
    (hL : ∀ q, L (R q) = 0) (c : F) :
    Function.Bijective (fun t : F × Vec p => R t.2 + (c+t.1) • v) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨a,q⟩ ⟨b,r⟩ h
    have hab : a = b := by
      have hh := congrArg L h
      simpa [hL, hv] using hh
    subst b
    congr 1
    apply hR
    exact add_right_cancel h
  · rw [Fintype.card_prod, ZMod.card, vec_card, vec_card, pow_succ, Nat.mul_comm]

private def adj (β : F) (a : Expr) : Expr := .add a (.cn β)

private def correction (β : F) (e b : Expr) : Expr :=
  .add e (if β = 0 then .cn 0 else b)

private theorem correction_eq (β : F) (e a b : Expr) (ws : List F) :
    (Ins.paid (correction β e b) (adj β a) b).step ws =
      (Ins.paid e a b).step ws := by
  have hs : ∀ x : F, x = 0 ∨ x = 1 := by decide
  rcases hs β with rfl | rfl
  · simp [Ins.step, Ins.val, correction, adj, Expr.val]
  · simp only [Ins.step, Ins.val, correction, adj, Expr.val, one_ne_zero, if_false]
    rw [add_mul, one_mul, add_comm (a.val ws * b.val ws), ← add_assoc, add_assoc (e.val ws),
      CharTwo.add_self_eq_zero, add_zero]

private theorem split_state {b k p r : ℕ} (S : State b k (p+1) r) (e a c : Expr)
    (ha : (a.compile S.regs).x ≠ 0) :
    ∃ T : F → State b k p r,
      ∀ (u : Vec b) (f : Vec k → List F → ℝ),
        mean (fun q => f (S.args q u) ((Ins.paid e a c).step (S.values q u))) =
          (mean (fun q => f ((T 0).args q u) ((T 0).values q u)) +
           mean (fun q => f ((T 1).args q u) ((T 1).values q u))) / 2 := by
  classical
  let A := a.compile S.regs
  obtain ⟨R,v,hR,hv,hker,hkill⟩ :=
    RowPort.PivotStep.solve_one A.x ha
  let pivot (β : F) := (adj β a).compile S.regs
  have hpx (β : F) : (pivot β).x = A.x := by
    simp [pivot, adj, Expr.compile, plus, zeroCostConst, A]
  have hpt (β : F) (w : Vec (b+r)) : (pivot β).tail w = A.tail w + β := rfl
  let T (β : F) := S.discard (correction β e c) R hR v (pivot β)
  have hT (β : F) (q : Vec p) (u : Vec b) :
      let q₀ := R q + (A.tail (S.env u)+β) • v
      (T β).args q u = S.args q₀ u ∧
        (T β).values q u = (Ins.paid e a c).step (S.values q₀ u) := by
    have hp := hkill q ((pivot β).tail (S.env u))
    have hz : eval (shift R v (pivot β).tail (pivot β).tail_aff (pivot β)) q (S.env u) = 0 := by
      rw [shift_eval]
      exact show (pivot β).x _ + (pivot β).tail (S.env u) = 0 by rw [hpx]; exact hp
    have h := S.discard_ok (correction β e c) (adj β a) c R hR v (pivot β) q u
      (by change eval (shift R v (pivot β).tail (pivot β).tail_aff (pivot β)) q (S.env u) * _ = 0
          rw [hz, zero_mul])
    simpa only [correction_eq, hpt] using h
  refine ⟨T, fun u f => ?_⟩
  let E := Equiv.ofBijective _ (pivot_bijective R hR A.x v hv hker (A.tail (S.env u)))
  rw [← mean_equiv E]
  let g : F × Vec p → ℝ := fun t => f ((T t.1).args t.2 u) ((T t.1).values t.2 u)
  have hg : (fun x => f (S.args (E x) u) ((Ins.paid e a c).step (S.values (E x) u))) = g := by
    funext t
    obtain ⟨h₁,h₂⟩ := hT t.1 t.2 u
    change _ = f ((T t.1).args t.2 u) ((T t.1).values t.2 u)
    rw [h₁,h₂]
    rfl
  rw [hg, mean_F_prod]

abbrev Leaf (b k : ℕ) := Σ p r : ℕ, State b k p r

noncomputable def mixture {α : Type*} (L : List (ℝ × α)) (f : α → ℝ) : ℝ :=
  (L.map fun t => t.1 * f t.2).sum

theorem mixture_append {α : Type*} (L M : List (ℝ × α)) (f : α → ℝ) :
    mixture (L ++ M) f = mixture L f + mixture M f := by
  simp [mixture]

theorem mixture_scale {α : Type*} (c : ℝ) (L : List (ℝ × α)) (f : α → ℝ) :
    mixture (L.map fun t => (c * t.1,t.2)) f = c * mixture L f := by
  induction L with
  | nil => simp [mixture]
  | cons a l ih => simp [mixture, List.map_map, Function.comp_def] at *; rw [ih]; ring

theorem mixture_advance {b k : ℕ} (gs : List Ins) :
    ∀ p r (S : State b k p r), ∃ L : List (ℝ × Leaf b k),
      (∀ t ∈ L, 0 ≤ t.1 ∧ p + t.2.2.1 = t.2.1 + r + paidCount gs) ∧
      mixture L (fun _ => 1) = 1 ∧
      ∀ (u : Vec b) (f : Vec k → List F → ℝ),
        mean (fun q => f (S.args q u) (gs.foldl Ins.step (S.values q u))) =
          mixture L (fun t => mean (fun q => f (t.2.2.args q u) (t.2.2.values q u))) := by
  classical
  induction gs with
  | nil =>
    intro p r S
    exact ⟨[(1,⟨p,r,S⟩)], by simp [paidCount], by simp [mixture], by simp [mixture]⟩
  | cons g gs ih =>
    intro p r S
    have keep {r' : ℕ} (T : State b k p r') (hc : r' = r + g.cost)
        (hr : ∀ q u, T.args q u = S.args q u ∧ T.values q u = g.step (S.values q u)) :
        ∃ L : List (ℝ × Leaf b k),
          (∀ t ∈ L, 0 ≤ t.1 ∧ p + t.2.2.1 = t.2.1 + r + paidCount (g::gs)) ∧
          mixture L (fun _ => 1) = 1 ∧
          ∀ (u : Vec b) (f : Vec k → List F → ℝ),
            mean (fun q => f (S.args q u) ((g::gs).foldl Ins.step (S.values q u))) =
              mixture L (fun t => mean (fun q => f (t.2.2.args q u) (t.2.2.values q u))) := by
      obtain ⟨L,hl,hw,hm⟩ := ih p r' T
      refine ⟨L,fun t ht => ⟨(hl t ht).1,?_⟩,hw,?_⟩
      · have := (hl t ht).2
        simp only [paidCount,List.map_cons,List.sum_cons] at *
        omega
      · intro u f
        simpa only [(hr _ _).1, (hr _ _).2, List.foldl_cons] using hm u f
    cases g with
    | free e => exact keep (S.free e) (by simp [Ins.cost]) (S.free_ok e)
    | paid e a c =>
      by_cases hb : (a.compile S.regs).x = 0 ∧ (c.compile S.regs).x = 0
      · exact keep (S.retain e a c) rfl (S.retain_ok e a c hb.1 hb.2)
      cases p with
      | zero => exact (hb ⟨zero_direction _, zero_direction _⟩).elim
      | succ p =>
        have hs : ∃ T : F → State b k p r, ∀ (u : Vec b) (f : Vec k → List F → ℝ),
            mean (fun q => f (S.args q u) ((Ins.paid e a c).step (S.values q u))) =
              (mean (fun q => f ((T 0).args q u) ((T 0).values q u)) +
               mean (fun q => f ((T 1).args q u) ((T 1).values q u))) / 2 := by
          by_cases ha : (a.compile S.regs).x = 0
          · obtain ⟨T,hT⟩ := split_state S e c a (fun hc => hb ⟨ha,hc⟩)
            refine ⟨T,fun u f => ?_⟩
            simpa only [Ins.step, Ins.val, mul_comm (c.val _) (a.val _)] using hT u f
          · exact split_state S e a c ha
        obtain ⟨T,hT⟩ := hs
        obtain ⟨L,hL,hWL,hML⟩ := ih p r (T 0)
        obtain ⟨M,hM,hWM,hMM⟩ := ih p r (T 1)
        let sc : ℝ × Leaf b k → ℝ × Leaf b k := fun t => ((1/2) * t.1,t.2)
        refine ⟨L.map sc ++ M.map sc,?_ ,?_,?_⟩
        · intro t ht
          rw [List.mem_append] at ht
          rcases ht with ht | ht <;> obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
          · refine ⟨mul_nonneg (by norm_num) (hL u hu).1,?_⟩
            have := (hL u hu).2
            simp only [sc, paidCount, List.map_cons, List.sum_cons, Ins.cost] at *
            omega
          · refine ⟨mul_nonneg (by norm_num) (hM u hu).1,?_⟩
            have := (hM u hu).2
            simp only [sc, paidCount, List.map_cons, List.sum_cons, Ins.cost] at *
            omega
        · rw [mixture_append, mixture_scale, mixture_scale, hWL, hWM]
          norm_num
        · intro u f
          change mean (fun q => f (S.args q u) (gs.foldl Ins.step
            ((Ins.paid e a c).step (S.values q u)))) = _
          rw [hT u (fun x w => f x (gs.foldl Ins.step w))]
          rw [mixture_append, mixture_scale, mixture_scale, ← hML u f, ← hMM u f]
          ring

theorem mean_phase_linear {d : ℕ} (L : Vec d →ₗ[F] F) (b : F) :
    mean (fun q => phase (L q + b)) = if L = 0 then phase b else 0 := by
  classical
  by_cases h : L = 0
  · have hc : (Fintype.card (Vec d) : ℝ) ≠ 0 := by
      rw [vec_card]; positivity
    simp [h, mean, hc]
  · obtain ⟨u,hu⟩ := LinearMap.surjective_of_ne_zero h 1
    let g : Vec d → ℝ := fun q => phase (L q + b)
    have ht : (∑ q, g (q+u)) = ∑ q, g q := Equiv.sum_comp (Equiv.addRight u) g
    have hz (q : Vec d) : g (q+u) = -g q := by
      change phase (L (q+u)+b) = -phase (L q+b)
      rw [map_add, add_right_comm, hu, phase_add, phase_one, mul_neg, mul_one]
    simp_rw [hz, Finset.sum_neg_distrib] at ht
    have hzero : (∑ q, g q) = 0 := by linarith
    rw [if_neg h]
    change (∑ q, g q) / _ = 0
    rw [hzero, zero_div]

def addressMap {d n : ℕ} (A : Vec d →ₗ[F] Vec n) :
    Vec n →ₗ[F] Module.Dual F (Vec d) :=
  A.dualMap.comp (dotProductBilin F F)

theorem address_surjective {d n : ℕ} (A : Vec d →ₗ[F] Vec n)
    (hA : Function.Injective A) : Function.Surjective (addressMap A) := by
  have hinj : Function.Injective (dotProductBilin F F :
      Vec n →ₗ[F] Module.Dual F (Vec n)) := by
    intro a b hab
    have hh : ∀ y, dotProduct (a-b) y = 0 := by
      intro y
      rw [sub_dotProduct, sub_eq_zero]
      exact LinearMap.congr_fun hab y
    exact sub_eq_zero.mp (dotProduct_eq_zero _ hh)
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := F) (V := Vec n)).symm).mp hinj
  exact (LinearMap.dualMap_surjective_of_injective hA).comp hsurj

theorem address_finrank {d n : ℕ} (A : Vec d →ₗ[F] Vec n)
    (hA : Function.Injective A) : Module.finrank F (addressMap A).ker + d = n := by
  have h := (addressMap A).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (address_surjective A hA), finrank_top,
    Subspace.dual_finrank_eq, Module.finrank_fin_fun, Module.finrank_fin_fun, add_comm] at h
  exact h

noncomputable def readWire {b k d r : ℕ} (S : State b k d r) (j : ℕ) :
    Wire d (b+r) := S.regs.getD j (zeroCostConst 0)

theorem readWire_eq {b k d r : ℕ} (S : State b k d r) (j : ℕ) (q : Vec d) (u : Vec b) :
    eval (readWire S j) q (S.env u) = (S.values q u).getD j 0 :=
  list_getD_eval S.regs q (S.env u) j

theorem row_address {n d r : ℕ} (S : State n n d r) (j : ℕ) :
    ∃ H : Submodule F (Vec n), ∃ y₀ : Vec n, Module.finrank F H + d = n ∧
      ∀ (y : Vec n) (g : F),
        mean (fun q => phase ((S.values q y).getD j 0 + dotProduct (S.args q y) y + g)) =
          @ite ℝ (y-y₀ ∈ H) (Classical.propDecidable _)
            (phase ((readWire S j).tail (S.env y) +
              dotProduct (fun i => (S.orig i).tail (S.env y)) y + g)) 0 := by
  classical
  let A := embed S.orig
  let O := readWire S j
  obtain ⟨y₀,hy₀⟩ := address_surjective A S.hOrig O.x
  refine ⟨(addressMap A).ker,y₀,address_finrank A S.hOrig,?_⟩
  intro y g
  let b : Vec n := fun i => (S.orig i).tail (S.env y)
  let L := O.x + addressMap A y
  have ha (q : Vec d) : S.args q y = A q + b := rfl
  have hl (q : Vec d) : dotProduct (A q) y = addressMap A y q := by
    exact dotProduct_comm _ _
  have hh (q : Vec d) :
      (S.values q y).getD j 0 + dotProduct (S.args q y) y + g =
      L q + (O.tail (S.env y) + dotProduct b y + g) := by
    rw [← readWire_eq, ha, add_dotProduct, hl]
    change O.x q + O.tail (S.env y) + (addressMap A y q + dotProduct b y) + g =
      (O.x q + addressMap A y q) + (O.tail (S.env y) + dotProduct b y + g)
    abel
  simp_rw [hh, mean_phase_linear]
  have hm : y-y₀ ∈ (addressMap A).ker ↔ L = 0 := by
    rw [LinearMap.mem_ker, map_sub, hy₀]
    change addressMap A y - O.x = 0 ↔ O.x + addressMap A y = 0
    have hn : -(addressMap A y) = addressMap A y := by
      ext q
      exact CharTwo.neg_eq _
    rw [sub_eq_zero, add_eq_zero_iff_eq_neg, hn]
    exact eq_comm
  simp only [hm, O, b]

private def initialX {n : ℕ} (i : Fin n) : Wire n n :=
  ⟨LinearMap.proj i, fun _ => 0, constant 0⟩

private def initialY {n : ℕ} (i : Fin n) : Wire n n :=
  ⟨0, fun w => w i, coordinate i⟩

private def start (n : ℕ) : State n n n 0 :=
  ⟨id, .nil, initialX, by
    intro q s h
    funext i
    exact congrFun h i,
    List.ofFn initialX ++ List.ofFn initialY⟩

def bits {n : ℕ} (x : Vec n) : List Bool := List.ofFn (fun i => bit (x i))

private theorem args_start {n : ℕ} (q u : Vec n) :
    (start n).args q u = q := by
  funext i
  simp [start,State.args,eval,initialX]

private theorem values_start {n : ℕ} (q u : Vec n) :
    (start n).values q u = List.ofFn q ++ List.ofFn u := by
  simp [start,State.values,eval,initialX,initialY,List.map_ofFn,Function.comp_def]

theorem circuit_rows {n : ℕ} (C : Circuit) (hLegal : ∀ a ∈ C.gates, legal a) :
    ∃ L : List (ℝ × Leaf n n),
      (∀ t ∈ L, 0 ≤ t.1 ∧ n + t.2.2.1 = t.2.1 + C.gates.countP paid) ∧
      mixture L (fun _ => 1) = 1 ∧
      ∀ (y : Vec n) (g : F),
        mean (fun x => if C.eval (bits x ++ bits y) = bit (dotProduct x y + g)
          then (1 : ℝ) else -1) =
        mixture L (fun t => mean (fun q =>
          phase ((t.2.2.values q y).getD C.output 0 + dotProduct (t.2.2.args q y) y + g))) := by
  obtain ⟨L,hL,hW,hM⟩ := mixture_advance (C.gates.map lower) n 0 (start n)
  refine ⟨L,?_,hW,?_⟩
  · intro t ht
    have h := hL t ht
    simpa only [Nat.add_zero, cost_bridge _ hLegal] using h
  · intro y g
    have h := hM y (fun x w => phase (w.getD C.output 0 + dotProduct x y + g))
    simp only [args_start, values_start] at h
    rw [← h]
    congr 1
    funext x
    rw [show bits x ++ bits y = (List.ofFn x ++ List.ofFn y).map bit by
      simp [bits,List.map_ofFn,Function.comp_def], eval_bridge _ hLegal, phase_agree, add_assoc]

end PEqualNP.Outside.L_meta_32579_aux.Row


namespace PEqualNP.Outside.L_meta_32579_aux.Geometry

abbrev F := ZMod 2
abbrev Dat (v : ℕ) := Fin v → F
abbrev Prs (m : ℕ) := (Fin m × Bool) → F

def Good {v m : ℕ} (P : Dat v →ₗ[F] Prs m) (U : Submodule F (Dat v)) : Prop :=
  ∃ (J : Finset (Fin m)) (side : Fin m → Bool) (L : Prs m →ₗ[F] Dat v),
    J.card + Module.finrank F U ≤ v ∧ (∀ x, L x ∈ U) ∧
    (∀ (x : Prs m) (i : Fin m) (b : Bool), i ∉ J → P (L x) (i, b) = x (i, b)) ∧
    (∀ (x : Prs m) (i : Fin m), i ∈ J → P (L x) (i, side i) = 0)

private def zeroPair {m : ℕ} (t : Fin m) : Prs m →ₗ[F] Prs m where
  toFun x p := if p.1 = t then 0 else x p
  map_add' x y := by funext p; by_cases hp : p.1 = t <;> simp [hp]
  map_smul' c x := by funext p; by_cases hp : p.1 = t <;> simp [hp]

/-- A linear cut preserves the old broken pairs and breaks at most one further pair. -/
theorem good_cut {v m : ℕ} (P : Dat v →ₗ[F] Prs m)
    (U : Submodule F (Dat v)) (g : Dat v →ₗ[F] F)
    (J : Finset (Fin m)) (side : Fin m → Bool) (L : Prs m →ₗ[F] Dat v)
    (hLU : ∀ x, L x ∈ U)
    (hfree : ∀ (x : Prs m) (i : Fin m) (b : Bool), i ∉ J → P (L x) (i, b) = x (i, b))
    (hzero : ∀ (x : Prs m) (i : Fin m), i ∈ J → P (L x) (i, side i) = 0) :
    ∃ (J' : Finset (Fin m)) (side' : Fin m → Bool) (L' : Prs m →ₗ[F] Dat v),
      J ⊆ J' ∧ J'.card ≤ J.card + 1 ∧
      (∀ x, L' x ∈ U ⊓ LinearMap.ker g) ∧
      (∀ (x : Prs m) (i : Fin m) (b : Bool), i ∉ J' → P (L' x) (i, b) = x (i, b)) ∧
      (∀ (x : Prs m) (i : Fin m), i ∈ J' → P (L' x) (i, side' i) = 0) := by
  classical
  let f := g.comp L
  by_cases hf : f = 0
  · refine ⟨J, side, L, Finset.Subset.rfl, by omega,
      fun x => ⟨hLU x, LinearMap.mem_ker.2 ?_⟩, hfree, hzero⟩
    change f x = 0
    rw [hf]; rfl
  have hpiv : ∃ p : Fin m × Bool, f (Pi.single p 1) ≠ 0 := by
    by_contra! h
    apply hf
    apply LinearMap.pi_ext
    intro p c
    have e : (Pi.single p c : Prs m) = c • Pi.single p (1 : F) := by
      rw [← Pi.single_smul]; simp
    rw [e, map_smul, h]; simp
  obtain ⟨⟨t, b⟩, hp⟩ := hpiv
  let e : Prs m := Pi.single (t, b) 1
  let E : Prs m →ₗ[F] Prs m := zeroPair t - ((f.comp (zeroPair t)).smulRight ((f e)⁻¹ • e))
  have hEa (x : Prs m) (p : Fin m × Bool) :
      E x p = (if p.1 = t then 0 else x p) - f (zeroPair t x) * ((f e)⁻¹ * e p) := rfl
  have hE1 (x : Prs m) (p : Fin m × Bool) (hp' : p.1 ≠ t) : E x p = x p := by
    have hn : p ≠ (t, b) := fun h => hp' (congrArg Prod.fst h)
    rw [hEa, show e p = 0 from Pi.single_eq_of_ne hn 1]; simp [hp']
  have hE2 (x : Prs m) : E x (t, !b) = 0 := by
    have hn : (t, !b) ≠ (t, b) := by
      intro h
      have hb := congrArg Prod.snd h
      cases b <;> simp at hb
    rw [hEa, show e (t, !b) = 0 from Pi.single_eq_of_ne hn 1]; simp
  have hE3 (x : Prs m) : f (E x) = 0 := by
    change f (zeroPair t x - f (zeroPair t x) • ((f e)⁻¹ • e)) = 0
    simp only [map_sub, map_smul, smul_eq_mul, inv_mul_cancel₀ (show f e ≠ 0 from hp)]
    simp
  have hmem (x : Prs m) : L.comp E x ∈ U ⊓ LinearMap.ker g :=
    ⟨hLU _, LinearMap.mem_ker.2 (hE3 x)⟩
  have hcardJ : (insert t J).card ≤ J.card + 1 := Finset.card_insert_le t J
  by_cases ht : t ∈ J
  · refine ⟨J, side, L.comp E, Finset.Subset.rfl, by omega, hmem, ?_,
      fun x i hi => hzero (E x) i hi⟩
    intro x i a hi
    exact (hfree (E x) i a hi).trans (hE1 x (i, a) (show i ≠ t from fun h => hi (h ▸ ht)))
  · refine ⟨insert t J, Function.update side t (!b), L.comp E,
      Finset.subset_insert t J, hcardJ, hmem, ?_, ?_⟩
    · intro x i a hi
      have hn : i ≠ t := fun h => hi (h ▸ Finset.mem_insert_self t J)
      exact (hfree (E x) i a (fun h => hi (Finset.mem_insert_of_mem h))).trans (hE1 x (i, a) hn)
    · intro x i hi
      change P (L (E x)) (i, Function.update side t (!b) i) = 0
      by_cases hc : i = t
      · rw [hc, Function.update_self, hfree (E x) t (!b) ht, hE2]
      · rw [Function.update_of_ne hc]
        exact hzero (E x) i ((Finset.mem_insert.1 hi).resolve_left hc)

/-- Every data direction can lose at most one free pair per lost dimension. -/
theorem good_of_surjective {v m : ℕ} (P : Dat v →ₗ[F] Prs m)
    (hP : Function.Surjective P) (U : Submodule F (Dat v)) : Good P U := by
  classical
  have hv : Module.finrank F (Dat v) = v := by simp [Dat]
  generalize hn : v - Module.finrank F U = n
  induction n using Nat.strong_induction_on generalizing U with
  | ind n ih =>
    by_cases ht : U = ⊤
    · subst U
      obtain ⟨L, hL⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)
      refine ⟨∅, fun _ => false, L, by simp [hv], fun _ => Submodule.mem_top, ?_, by simp⟩
      intro x i b _
      exact congrFun (LinearMap.congr_fun hL x) (i, b)
    · obtain ⟨u, hu⟩ : ∃ u : Dat v, u ∉ U := by
        by_contra! h
        exact ht (eq_top_iff.mpr fun x _ => h x)
      let T := U ⊔ Submodule.span F {u}
      have hr : Module.finrank F T = Module.finrank F U + 1 :=
        Submodule.finrank_sup_span_singleton hu
      have hTle : Module.finrank F T ≤ v := by simpa only [hv] using Submodule.finrank_le T
      have hG : Good P T := ih (v - Module.finrank F T) (by omega) T rfl
      let q := U.mkQ
      have hq : q u ≠ 0 := by
        intro h
        apply hu
        rw [← U.ker_mkQ]
        exact LinearMap.mem_ker.2 h
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one F hq
      let g := l.comp q
      have hug : g u ≠ 0 := by change l (q u) ≠ 0; rw [hl]; exact one_ne_zero
      have huT : u ∈ T :=
        (show Submodule.span F {u} ≤ T from le_sup_right)
          (Submodule.subset_span (Set.mem_singleton u))
      have hle : U ≤ T ⊓ LinearMap.ker g := by
        intro x hx
        refine ⟨(show U ≤ T from le_sup_left) hx, LinearMap.mem_ker.2 ?_⟩
        change l (q x) = 0
        have hqx : q x = 0 := LinearMap.mem_ker.1 (show x ∈ LinearMap.ker q by
          change x ∈ LinearMap.ker U.mkQ
          rwa [U.ker_mkQ])
        rw [hqx, map_zero]
      have heq : U = T ⊓ LinearMap.ker g := by
        by_contra hne
        have h₁ := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
        have h₂ := Submodule.finrank_lt_finrank_of_lt
          (show T ⊓ LinearMap.ker g < T from lt_of_le_of_ne inf_le_left (fun he =>
            hug (LinearMap.mem_ker.1 (show u ∈ T ⊓ LinearMap.ker g from he.symm ▸ huT).2)))
        omega
      obtain ⟨J, side, L, hcard, hLU, hfree, hzero⟩ := hG
      obtain ⟨J', side', L', _, hcard', hLU', hfree', hzero'⟩ :=
        good_cut P T g J side L hLU hfree hzero
      refine ⟨J', side', L', by omega, ?_, hfree', hzero'⟩
      intro x
      rw [heq]
      exact hLU' x

private theorem exists_subspace_of_finrank_le {M : Type*} [AddCommGroup M] [Module F M]
    (K : Submodule F M) {n : ℕ} (hn : n ≤ Module.finrank F K) :
    ∃ W : Submodule F M, W ≤ K ∧ Module.finrank F W = n := by
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank hn
  let V := Submodule.span F (Set.range b)
  have hV : Module.finrank F V = n := (finrank_span_eq_card hb).trans (Fintype.card_fin n)
  refine ⟨V.map K.subtype, ?_, (Submodule.finrank_map_subtype_eq K V).trans hV⟩
  intro x hx
  obtain ⟨y, _, rfl⟩ := Submodule.mem_map.1 hx
  exact y.property

/-- A coordinate constraint costs at most one dimension per constrained index. -/
theorem exists_selector_subspace {k m d' : ℕ} (H : Submodule F (Dat k))
    (word : Dat k →ₗ[F] Dat m) (J : Finset (Fin m))
    (hd : d' + J.card ≤ Module.finrank F H) :
    ∃ W : Submodule F (Dat k), W ≤ H ∧ Module.finrank F W = d' ∧
      ∀ s ∈ W, ∀ i ∈ J, word s i = 0 := by
  classical
  let f : H →ₗ[F] (J → F) := LinearMap.pi fun i =>
    ((LinearMap.proj (R := F) (φ := fun _ : Fin m => F) i.val).comp word).comp H.subtype
  have hr : Module.finrank F (LinearMap.range f) ≤ J.card := by
    simpa [Module.finrank_pi] using Submodule.finrank_le (LinearMap.range f)
  have hk := f.finrank_range_add_finrank_ker
  let K : Submodule F (Dat k) := (LinearMap.ker f).map H.subtype
  have hKrank : Module.finrank F K = Module.finrank F (LinearMap.ker f) :=
    Submodule.finrank_map_subtype_eq H (LinearMap.ker f)
  obtain ⟨W, hWK, hdim⟩ := exists_subspace_of_finrank_le K (n := d') (by omega)
  have hK (x : Dat k) (hx : x ∈ K) : ∃ y : H, f y = 0 ∧ y.val = x := by
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
    exact ⟨y, LinearMap.mem_ker.1 hy, hyx⟩
  refine ⟨W, ?_, hdim, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := hK x (hWK hx)
    exact y.property
  · intro x hx i hi
    obtain ⟨y, hy, rfl⟩ := hK x (hWK hx)
    exact congrFun hy (⟨i, hi⟩ : J)

/-- Simultaneously pick the lost data pairs and a selector direction killing their words. -/
theorem good_with_selector {v m k d' : ℕ} (P : Dat v →ₗ[F] Prs m)
    (hP : Function.Surjective P) (U : Submodule F (Dat v))
    (H : Submodule F (Dat k)) (word : Dat k →ₗ[F] Dat m)
    (hd : d' + (v - Module.finrank F U) ≤ Module.finrank F H) :
    ∃ (J : Finset (Fin m)) (side : Fin m → Bool) (L : Prs m →ₗ[F] Dat v)
      (W : Submodule F (Dat k)),
      J.card + Module.finrank F U ≤ v ∧ (∀ x, L x ∈ U) ∧
      (∀ (x : Prs m) (i : Fin m) (b : Bool), i ∉ J → P (L x) (i, b) = x (i, b)) ∧
      (∀ (x : Prs m) (i : Fin m), i ∈ J → P (L x) (i, side i) = 0) ∧
      W ≤ H ∧ Module.finrank F W = d' ∧ ∀ s ∈ W, ∀ i ∈ J, word s i = 0 := by
  obtain ⟨J, side, L, hJ, hL, hfree, hzero⟩ := good_of_surjective P hP U
  obtain ⟨W, hW, hdim, hword⟩ := exists_selector_subspace (d' := d') H word J (by omega)
  exact ⟨J, side, L, W, hJ, hL, hfree, hzero, hW, hdim, hword⟩

end PEqualNP.Outside.L_meta_32579_aux.Geometry

namespace PEqualNP.Outside.L_meta_32579_aux.Residual

open scoped BigOperators
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan
open PEqualNP.Outside.L_meta_32579_aux.RowPort.ProgramDegree
open PEqualNP.Outside.L_meta_32579_aux.RowPort.Substitute (front)
open PEqualNP.Outside.L_meta_32579_aux.RowPort.SpanExact (as_affine)

abbrev Pairs (m : ℕ) := (Fin m × Bool) → F

structure Part (k v m : ℕ) where
  center : Vec k → Vec v
  dir : Submodule F (Vec v)
  bad : Finset (Fin m)
  side : Fin m → Bool
  sectionMap : Pairs m →ₗ[F] Vec v

def On {k v m : ℕ} (T : Part k v m) (s : Vec k) (x : Vec v) : Prop :=
  x - T.center s ∈ T.dir

def FreePairs {k v m : ℕ} (P : Vec v →ₗ[F] Pairs m) (T : Part k v m) : Prop :=
  (∀ x, T.sectionMap x ∈ T.dir) ∧
  (∀ x i b, i ∉ T.bad → P (T.sectionMap x) (i,b) = x (i,b)) ∧
  (∀ x i, i ∈ T.bad → P (T.sectionMap x) (i,T.side i) = 0)

def IsAffine {k v m d : ℕ} (T : Part k v m) (f : Vec k → Vec v → Vec d) : Prop :=
  ∃ (A : Vec v →ₗ[F] Vec d) (a : Vec k → Vec d),
    ∀ s x, On T s x → f s x = A x + a s

def Below {k v m : ℕ} (T U : Part k v m) : Prop :=
  T.bad ⊆ U.bad ∧ ∀ s x, On U s x → On T s x

private theorem prepend_affine {k v m d : ℕ} (T : Part k v m)
    (f : Vec k → Vec v → Vec d) (g : Vec k → Vec v → F)
    (A : Vec v →ₗ[F] Vec d) (a : Vec k → Vec d)
    (hf : ∀ s x, On T s x → f s x = A x + a s)
    (L : Vec v →ₗ[F] F) (c : Vec k → F)
    (hg : ∀ s x, On T s x → g s x = L x + c s) :
    IsAffine T (fun s x => Fin.cases (g s x) (f s x)) := by
  refine ⟨LinearMap.pi (Fin.cases L (fun i => (LinearMap.proj i).comp A)),
    fun s => Fin.cases (c s) (a s), ?_⟩
  intro s x hx
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hg s x hx
  · exact congrFun (hf s x hx) j

private theorem cut {k v m : ℕ} (P : Vec v →ₗ[F] Pairs m)
    (T : Part k v m) (hT : FreePairs P T)
    (L : Vec v →ₗ[F] F) (c : Vec k → F) (u : Vec v) (hu : u ∈ T.dir) (hLu : L u = 1) :
    ∃ U : F → Part k v m,
      (∀ β, FreePairs P (U β) ∧ T.bad ⊆ (U β).bad ∧ (U β).bad.card ≤ T.bad.card+1) ∧
      (∀ β s x, On (U β) s x ↔ On T s x ∧ L x + c s = β) := by
  obtain ⟨J,side,M,hsub,hcard,hM,hfree,hzero⟩ :=
    Geometry.good_cut P T.dir L T.bad T.side T.sectionMap hT.1 hT.2.1 hT.2.2
  let U (β : F) : Part k v m :=
    ⟨fun s => T.center s + (L (T.center s) + c s + β) • u,
      T.dir ⊓ L.ker, J, side, M⟩
  refine ⟨U,fun _ => ⟨⟨hM,hfree,hzero⟩,hsub,hcard⟩,?_⟩
  intro β s x
  have hg :
      x - (T.center s + (L (T.center s) + c s + β) • u) =
        (x-T.center s) - (L (T.center s) + c s + β) • u := by abel
  have h₁ : x - (U β).center s ∈ T.dir ↔ On T s x := by
    change x - (T.center s + (L (T.center s) + c s + β) • u) ∈ T.dir ↔ _
    rw [hg]
    exact Submodule.sub_mem_iff_left _ (T.dir.smul_mem _ hu)
  have h₂ : x - (U β).center s ∈ L.ker ↔ L x + c s = β := by
    change x - (T.center s + (L (T.center s) + c s + β) • u) ∈ L.ker ↔ _
    rw [LinearMap.mem_ker, map_sub, map_add, map_smul, hLu, smul_eq_mul, mul_one]
    have h : ∀ X C D β : F, X-(C+(C+D+β)) = 0 ↔ X+D = β := by decide
    exact h _ _ _ _
  exact and_congr h₁ h₂

private theorem affine_over {k v m n d : ℕ} (T : Part k v m) (y : Vec k → Vec v → Vec n)
    (E : Vec n → Vec d) (hE : IsAffine T (fun s x => E (y s x)))
    (f : Fn d) (hf : f ∈ degree d 1) :
    ∃ (L : Vec v →ₗ[F] F) (c : Vec k → F),
      ∀ s x, On T s x → f (E (y s x)) = L x + c s := by
  obtain ⟨A,a,ha⟩ := hE
  obtain ⟨c,M,hM⟩ := as_affine hf
  refine ⟨M.comp A, fun s => c + M (a s), ?_⟩
  intro s x hx
  rw [hM, show E (y s x) = A x + a s from ha s x hx, map_add, LinearMap.comp_apply]
  exact add_left_comm _ _ _

private theorem no_variation {k v m : ℕ} (T : Part k v m)
    (L : Vec v →ₗ[F] F) (h : ¬∃ u ∈ T.dir, L u = 1) :
    ∀ s x, On T s x → L x = L (T.center s) := by
  have hs : ∀ x : F, x = 0 ∨ x = 1 := by decide
  intro s x hx
  have hz : L (x-T.center s) = 0 := (hs _).resolve_right (fun h' => h ⟨_,hx,h'⟩)
  rwa [map_sub, sub_eq_zero] at hz

private theorem branch {k v m n d : ℕ} (P : Vec v →ₗ[F] Pairs m)
    (T : Part k v m) (hT : FreePairs P T) (y : Vec k → Vec v → Vec n)
    (E : Vec n → Vec d) (hE : IsAffine T (fun s x => E (y s x)))
    (a b : Fn d) (ha : a ∈ degree d 1) (hb : b ∈ degree d 1) :
    ∃ S : Finset (Part k v m),
      (∀ U ∈ S, FreePairs P U ∧ Below T U ∧ U.bad.card ≤ T.bad.card+1 ∧
        IsAffine U (fun s x => front (a*b) (E (y s x)))) ∧
      (∀ s x, On T s x → ∃! U, U ∈ S ∧ On U s x) := by
  classical
  obtain ⟨A,z,hE⟩ := hE
  obtain ⟨L,c,hL⟩ := affine_over T y E ⟨A,z,hE⟩ a ha
  obtain ⟨M,g,hM⟩ := affine_over T y E ⟨A,z,hE⟩ b hb
  have splitOn (f₁ f₂ : Fn d) (N₁ N₂ : Vec v →ₗ[F] F) (c₁ c₂ : Vec k → F)
      (h₁ : ∀ s x, On T s x → f₁ (E (y s x)) = N₁ x + c₁ s)
      (h₂ : ∀ s x, On T s x → f₂ (E (y s x)) = N₂ x + c₂ s)
      (e : f₁ * f₂ = a * b) (u : Vec v) (hu : u ∈ T.dir) (hu₁ : N₁ u = 1) :
      ∃ S : Finset (Part k v m),
        (∀ U ∈ S, FreePairs P U ∧ Below T U ∧ U.bad.card ≤ T.bad.card+1 ∧
          IsAffine U (fun s x => front (a*b) (E (y s x)))) ∧
        (∀ s x, On T s x → ∃! U, U ∈ S ∧ On U s x) := by
    obtain ⟨U,hU,hu⟩ := cut P T hT N₁ c₁ u hu hu₁
    let Q := Finset.univ.image U
    have hAff (β : F) : IsAffine (U β) (fun s x => front (a*b) (E (y s x))) := by
      rw [← e]
      refine prepend_affine (U β) _ _ A z (fun s x hx => hE s x ((hu β s x).mp hx).1)
        (β • N₂) (fun s => β * c₂ s) ?_
      intro s x hx
      obtain ⟨ht,hval⟩ := (hu β s x).mp hx
      simp only [Pi.mul_apply, h₁ s x ht, h₂ s x ht, hval, LinearMap.smul_apply, smul_eq_mul, mul_add]
    refine ⟨Q,?_,?_⟩
    · intro U' hU'
      obtain ⟨β,_,rfl⟩ := Finset.mem_image.mp hU'
      exact ⟨(hU β).1,⟨(hU β).2.1,fun s x hx => ((hu β s x).mp hx).1⟩,(hU β).2.2,hAff β⟩
    · intro s x ht
      let β := N₁ x + c₁ s
      refine ⟨U β,⟨Finset.mem_image.mpr ⟨β,Finset.mem_univ _,rfl⟩,(hu β s x).mpr ⟨ht,rfl⟩⟩,?_⟩
      rintro V ⟨hV,hon⟩
      obtain ⟨β',_,rfl⟩ := Finset.mem_image.mp hV
      exact congrArg U ((hu β' s x).mp hon).2.symm
  by_cases hl : ∃ u ∈ T.dir, L u = 1
  · obtain ⟨u,hu,hu₁⟩ := hl
    exact splitOn a b L M c g hL hM rfl u hu hu₁
  by_cases hm : ∃ u ∈ T.dir, M u = 1
  · obtain ⟨u,hu,hu₁⟩ := hm
    exact splitOn b a M L g c hM hL (mul_comm _ _) u hu hu₁
  refine ⟨{T},?_,?_⟩
  · intro Q hQ
    have he : Q = T := Finset.mem_singleton.mp hQ
    subst Q
    refine ⟨hT,⟨Finset.Subset.rfl,fun _ _ h => h⟩,by omega,?_⟩
    refine prepend_affine T _ _ A z hE 0 (fun s => (L (T.center s) + c s)*(M (T.center s) + g s)) ?_
    intro s x hx
    simp [hL s x hx, hM s x hx, no_variation T L hl s x hx, no_variation T M hm s x hx]
  · intro s x hx
    exact ⟨T,⟨Finset.mem_singleton_self _,hx⟩,fun U h => Finset.mem_singleton.mp h.1⟩

theorem partition {k v m n r : ℕ} (P : Vec v →ₗ[F] Pairs m)
    (T : Part k v m) (hT : FreePairs P T) (y : Vec k → Vec v → Vec n)
    (hy : IsAffine T y) {E : Vec n → Vec (n+r)} (hE : Run n r E) :
    ∃ S : Finset (Part k v m),
      (∀ U ∈ S, FreePairs P U ∧ Below T U ∧ U.bad.card ≤ T.bad.card+r ∧
        IsAffine U (fun s x => E (y s x))) ∧
      (∀ s x, On T s x → ∃! U, U ∈ S ∧ On U s x) := by
  classical
  induction hE with
  | nil =>
    refine ⟨{T},?_,?_⟩
    · intro U hU
      obtain rfl := Finset.mem_singleton.mp hU
      exact ⟨hT,⟨Finset.Subset.rfl,fun _ _ h => h⟩,Nat.le_refl _,hy⟩
    · intro s x hx
      exact ⟨T,⟨Finset.mem_singleton_self _,hx⟩,fun U h => Finset.mem_singleton.mp h.1⟩
  | @cons r E hE a b ha hb ih =>
    obtain ⟨S,hS,hcov⟩ := ih
    have hchild : ∀ U : S, ∃ Q : Finset (Part k v m),
        (∀ V ∈ Q, FreePairs P V ∧ Below U.1 V ∧ V.bad.card ≤ U.1.bad.card+1 ∧
          IsAffine V (fun s x => front (a*b) (E (y s x)))) ∧
        (∀ s x, On U.1 s x → ∃! V, V ∈ Q ∧ On V s x) :=
      fun U => branch P U.1 (hS U.1 U.2).1 y E (hS U.1 U.2).2.2.2 a b ha hb
    choose Q hQ hcovQ using hchild
    let M := S.attach.biUnion Q
    refine ⟨M,?_,?_⟩
    · intro V hV
      obtain ⟨U,_,hVU⟩ := Finset.mem_biUnion.mp hV
      obtain ⟨hf,⟨hj,hs⟩,hc,ha⟩ := hQ U V hVU
      obtain ⟨_,⟨hju,hsu⟩,hcu,_⟩ := hS U.1 U.2
      exact ⟨hf,⟨hju.trans hj,fun s x hx => hsu s x (hs s x hx)⟩,by omega,ha⟩
    · intro s x hx
      obtain ⟨U,⟨hUS,hOn⟩,hUU⟩ := hcov s x hx
      obtain ⟨V,⟨hV,hVOn⟩,hVV⟩ := hcovQ ⟨U,hUS⟩ s x hOn
      refine ⟨V,⟨Finset.mem_biUnion.mpr ⟨⟨U,hUS⟩,Finset.mem_attach _ _,hV⟩,hVOn⟩,?_⟩
      rintro W ⟨hWM,hWOn⟩
      obtain ⟨U',_,hWU⟩ := Finset.mem_biUnion.mp hWM
      have he : U' = ⟨U,hUS⟩ := Subtype.ext <|
        hUU U'.1 ⟨U'.2,(hQ U' W hWU).2.1.2 s x hWOn⟩
      exact hVV W ⟨he ▸ hWU,hWOn⟩

end PEqualNP.Outside.L_meta_32579_aux.Residual

namespace PEqualNP.Outside.L_meta_32579_aux.Mixtures

open scoped BigOperators
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan
open PEqualNP.Outside.L_meta_32579_aux.Row (mean mixture vec_card)

abbrev Profile (S : Type*) := S → ℝ

def Majorized {S : Type*} (atom : Profile S → Prop) (f : Profile S) : Prop :=
  ∃ (N : ℕ) (v : Fin N → Profile S) (w : Fin N → ℝ),
    (∀ i, atom (v i) ∧ 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
    ∀ s, |f s| ≤ ∑ i, w i * v i s

theorem pack {S ι : Type*} [Fintype ι] {atom : Profile S → Prop} {f : Profile S}
    (v : ι → Profile S) (w : ι → ℝ)
    (hv : ∀ i, atom (v i) ∧ 0 ≤ w i) (hw : (∑ i, w i) = 1)
    (hf : ∀ s, |f s| ≤ ∑ i, w i * v i s) : Majorized atom f := by
  let e := (Fintype.equivFin ι).symm
  exact ⟨Fintype.card ι,v ∘ e,w ∘ e,fun i => hv (e i),
    (Equiv.sum_comp e w).trans hw,fun s => (Equiv.sum_comp e (fun i => w i * v i s)).symm ▸ hf s⟩

theorem majorized_of_atom {S : Type*} {atom : Profile S → Prop} {f v : Profile S}
    (hv : atom v) (hf : ∀ s, |f s| ≤ v s) : Majorized atom f := by
  exact pack (ι := Unit) (fun _ => v) (fun _ => 1) (fun _ => ⟨hv,zero_le_one⟩) (by simp)
    (fun s => by simpa using hf s)

theorem mix {S ι : Type*} [Fintype ι] {atom : Profile S → Prop}
    (g : ι → Profile S) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw₁ : (∑ i, w i) = 1)
    (hg : ∀ i, Majorized atom (g i)) :
    Majorized atom (fun s => ∑ i, w i * g i s) := by
  classical
  choose n v u hv hu hm using hg
  let V : (Σ i, Fin (n i)) → Profile S := fun z => v z.1 z.2
  let W : (Σ i, Fin (n i)) → ℝ := fun z => w z.1 * u z.1 z.2
  refine pack V W (fun z => ⟨(hv z.1 z.2).1,mul_nonneg (hw _) (hv _ _).2⟩) ?_ ?_
  · rw [Fintype.sum_sigma]
    simp only [W, ← Finset.mul_sum, hu, mul_one, hw₁]
  · intro s
    rw [Fintype.sum_sigma]
    calc
      |∑ i, w i * g i s| ≤ ∑ i, w i * |g i s| := by
        simpa only [abs_mul, abs_of_nonneg (hw _)] using
          (Finset.abs_sum_le_sum_abs (fun i => w i * g i s) Finset.univ)
      _ ≤ ∑ i, w i * (∑ j, u i j * v i j s) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hm i s) (hw i)
      _ = _ := by simp only [W,V,mul_assoc,Finset.mul_sum]

theorem list_mixture_eq_sum {α : Type*} (L : List (ℝ × α)) (f : α → ℝ) :
    mixture L f = ∑ i : Fin L.length, (L.get i).1 * f (L.get i).2 := by
  conv_lhs =>
    unfold mixture
    rw [← List.ofFn_get L, List.map_ofFn, List.sum_ofFn]
  rfl

theorem mix_list {S α : Type*} {atom : Profile S → Prop}
    (L : List (ℝ × α)) (g : α → Profile S)
    (hw : ∀ t ∈ L, 0 ≤ t.1) (hw₁ : mixture L (fun _ => 1) = 1)
    (hg : ∀ t ∈ L, Majorized atom (g t.2)) :
    Majorized atom (fun s => mixture L (fun t => g t s)) := by
  simp_rw [list_mixture_eq_sum] at hw₁ ⊢
  simp only [mul_one] at hw₁
  exact mix (fun i : Fin L.length => g (L.get i).2) (fun i => (L.get i).1)
    (fun i => hw _ (List.get_mem _ _)) hw₁ (fun i => hg _ (List.get_mem _ _))

noncomputable def mass {v : ℕ} (U : Submodule F (Vec v)) : ℝ :=
  2^Module.finrank F U

noncomputable def averageOn {v : ℕ} (U : Submodule F (Vec v)) (a : Vec v)
    (f : Vec v → ℝ) : ℝ := by
  classical
  exact mean (fun z : U => f (a+z.1))

noncomputable def cutSum {v : ℕ} (U : Submodule F (Vec v)) (a : Vec v)
    (f : Vec v → ℝ) : ℝ := by
  classical
  exact ∑ x, if x-a ∈ U then f x else 0

theorem card_submodule {v : ℕ} (U : Submodule F (Vec v)) [Fintype U] :
    Fintype.card U = 2^Module.finrank F U := by
  rw [Module.card_eq_pow_finrank (K := F), ZMod.card]

theorem mass_pos {v : ℕ} (U : Submodule F (Vec v)) : 0 < mass U := by
  unfold mass
  positivity

theorem cutSum_eq {v : ℕ} (U : Submodule F (Vec v)) (a : Vec v) (f : Vec v → ℝ) :
    cutSum U a f = mass U * averageOn U a f := by
  classical
  unfold cutSum averageOn mean
  rw [card_submodule, Nat.cast_pow, mass]
  norm_cast
  rw [mul_div_cancel₀ _ (by positivity)]
  rw [← Finset.sum_filter, ← Finset.sum_coe_sort]
  let Q := (Finset.univ : Finset (Vec v)).filter (fun x => x-a ∈ U)
  let E : U ≃ Q :=
    { toFun := fun z => ⟨a+z.1,by simpa [Q,add_sub_cancel_left] using z.2⟩
      invFun := fun x => ⟨x.1-a,(Finset.mem_filter.mp x.2).2⟩
      left_inv := fun z => Subtype.ext (add_sub_cancel_left _ _)
      right_inv := fun x => Subtype.ext (by simp) }
  exact (Fintype.sum_equiv E (fun z => f (a+z.1)) (fun x => f x.1) (fun _ => rfl)).symm

theorem averageOn_one {v : ℕ} (U : Submodule F (Vec v)) (a : Vec v) :
    averageOn U a (fun _ => 1) = 1 := by
  classical
  simp [averageOn,mean,card_submodule,show (2:ℕ) ≠ 0 by decide]

theorem averageOn_abs_le_one {v : ℕ} (U : Submodule F (Vec v)) (a : Vec v)
    (f : Vec v → ℝ) (hf : ∀ x, |f x| ≤ 1) : |averageOn U a f| ≤ 1 := by
  classical
  unfold averageOn mean
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (Fintype.card U : ℝ))]
  have hc : 0 < (Fintype.card U : ℝ) := by rw [card_submodule]; positivity
  apply (div_le_iff₀ hc).mpr
  rw [one_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (f := fun z : U => |f (a+z.1)|) (g := fun _ => (1:ℝ)) (fun z _ => hf (a+z.1)))

theorem cutting_weights {k v m : ℕ} (T : Residual.Part k v m)
    (S : Finset (Residual.Part k v m))
    (hSub : ∀ U ∈ S, Residual.Below T U)
    (hCov : ∀ s x, Residual.On T s x → ∃! U, U ∈ S ∧ Residual.On U s x)
    (s : Vec k) :
    let w := fun i : S => mass i.1.dir / mass T.dir
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
    ∀ f : Vec v → ℝ, averageOn T.dir (T.center s) f =
      ∑ i, w i * averageOn i.1.dir (i.1.center s) f := by
  classical
  have hsum (f : Vec v → ℝ) : cutSum T.dir (T.center s) f =
      ∑ i : S, cutSum i.1.dir (i.1.center s) f := by
    unfold cutSum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    change (if Residual.On T s x then f x else 0) =
      ∑ i : S, if Residual.On i.1 s x then f x else 0
    by_cases hx : Residual.On T s x
    · obtain ⟨U,⟨hUS,hOn⟩,huniq⟩ := hCov s x hx
      rw [if_pos hx, Finset.sum_eq_single_of_mem ⟨U,hUS⟩ (Finset.mem_univ _)]
      · rw [if_pos hOn]
      · intro i _ hi
        apply if_neg
        intro hOn'
        exact hi (Subtype.ext (huniq i.1 ⟨i.2,hOn'⟩))
    · rw [if_neg hx]
      symm
      exact Finset.sum_eq_zero fun i _ => if_neg (fun hi => hx ((hSub i.1 i.2).2 s x hi))
  have hAvg (f : Vec v → ℝ) : averageOn T.dir (T.center s) f =
      ∑ i : S, (mass i.1.dir / mass T.dir) * averageOn i.1.dir (i.1.center s) f := by
    have h := hsum f
    simp_rw [cutSum_eq] at h
    calc
      averageOn T.dir (T.center s) f =
          (mass T.dir * averageOn T.dir (T.center s) f) / mass T.dir := by
        rw [mul_comm, mul_div_cancel_right₀ _ (mass_pos _).ne']
      _ = _ := by
        rw [h, Finset.sum_div]
        exact Finset.sum_congr rfl (fun i _ => by ring)
  refine ⟨fun _ => div_nonneg (mass_pos _).le (mass_pos _).le, ?_, hAvg⟩
  simpa only [averageOn_one,mul_one] using (hAvg (fun _ => 1)).symm

end PEqualNP.Outside.L_meta_32579_aux.Mixtures

namespace PEqualNP.Outside.L_meta_32579_aux.PhaseChart

open scoped BigOperators
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan
open PEqualNP.Outside.L_meta_32579_aux.RowPort.SpanExact (as_affine)
open PEqualNP.Outside.L_meta_32579_aux.RowPort.Normalized (State)
open PEqualNP.Outside.L_meta_32579_aux.Row (readWire)

abbrev Chart (v m r : ℕ) := Vec v ≃ₗ[F] Vec m × (Vec m × Vec r)

noncomputable def makeChart (m r : ℕ) : Chart (2*m+r) m r := by
  apply LinearEquiv.ofFinrankEq
  simp only [Chart, Module.finrank_fin_fun, Module.finrank_prod]
  omega

def pairMap {v m r : ℕ} (D : Chart v m r) : Vec v →ₗ[F] Residual.Pairs m where
  toFun x i := if i.2 then (D x).2.1 i.1 else (D x).1 i.1
  map_add' x y := by
    funext i
    rcases i with ⟨i,b⟩
    cases b <;> simp
  map_smul' c x := by
    funext i
    rcases i with ⟨i,b⟩
    cases b <;> simp

theorem pairMap_false {v m r : ℕ} (D : Chart v m r) (x : Vec v) (i : Fin m) :
    pairMap D x (i,false) = (D x).1 i := rfl

theorem pairMap_true {v m r : ℕ} (D : Chart v m r) (x : Vec v) (i : Fin m) :
    pairMap D x (i,true) = (D x).2.1 i := rfl

theorem pairMap_surj {v m r : ℕ} (D : Chart v m r) : Function.Surjective (pairMap D) := by
  intro z
  refine ⟨D.symm (fun i => z (i,false),(fun i => z (i,true),0)),?_⟩
  funext i
  rcases i with ⟨i,b⟩
  cases b <;> simp [pairMap_false,pairMap_true]

noncomputable def toProduct {n k v m r : ℕ}
    (E : Vec n ≃ₗ[F] Vec k × (Vec m × (Vec m × Vec r))) (D : Chart v m r) :
    Vec n ≃ₗ[F] Vec k × Vec v :=
  E.trans (LinearEquiv.prodCongr (LinearEquiv.refl F (Vec k)) D.symm)

theorem toProduct_symm {n k v m r : ℕ}
    (E : Vec n ≃ₗ[F] Vec k × (Vec m × (Vec m × Vec r))) (D : Chart v m r)
    (s : Vec k) (x : Vec v) : (toProduct E D).symm (s,x) = E.symm (s,D x) := rfl

theorem chart_y_affine {n k v m : ℕ} (E : Vec n ≃ₗ[F] Vec k × Vec v) (T : Residual.Part k v m) :
    Residual.IsAffine T (fun s x => E.symm (s,x)) := by
  refine ⟨E.symm.toLinearMap.comp (LinearMap.inr F (Vec k) (Vec v)),fun s => E.symm (s,0),?_⟩
  intro s x _
  change E.symm (s,x) = E.symm (0,x) + E.symm (s,0)
  rw [← map_add]
  simp

private theorem vector_affine {n t : ℕ} (f : Fin t → Fn n) (hf : ∀ i, f i ∈ degree n 1) :
    ∃ (A : Vec n →ₗ[F] Vec t) (a : Vec t), ∀ x, (fun i => f i x) = A x + a := by
  choose c L h using fun i => as_affine (hf i)
  refine ⟨LinearMap.pi L,c,?_⟩
  intro x
  funext i
  exact (h i x).trans (add_comm _ _)

theorem fixed_quadratic {k v m n d r : ℕ} (T : Residual.Part k v m)
    (y : Vec k → Vec v → Vec n) (hy : Residual.IsAffine T y)
    (S : State n n d r) (hE : Residual.IsAffine T (fun s x => S.env (y s x)))
    (j : ℕ) (h : Vec k → F) :
    ∃ (q : Vec v → F) (B : LinearMap.BilinForm F (Vec v))
      (A : Vec k → Vec v →ₗ[F] F) (c : Vec k → F),
      (∀ x, B x x = 0) ∧
      (∀ t x, q (t+x) = q t + q x + q 0 + B t x) ∧
      ∀ s x, Residual.On T s x →
        (readWire S j).tail (S.env (y s x)) +
            dotProduct (fun i => (S.orig i).tail (S.env (y s x))) (y s x) + h s =
          q x + A s x + c s := by
  obtain ⟨Y,b,hY⟩ := hy
  obtain ⟨D,z,hD⟩ := hE
  obtain ⟨c₀,S₀,h₀⟩ := as_affine (readWire S j).tail_aff
  obtain ⟨M,t,ht⟩ := vector_affine _ (fun i => (S.orig i).tail_aff)
  let K := M.comp D
  let pq : LinearMap.BilinForm F (Vec n) := dotProductBilin F F
  let b₀ := LinearMap.BilinForm.comp pq K Y
  let B : LinearMap.BilinForm F (Vec v) := b₀ + b₀.flip
  let q := fun x => dotProduct (K x) (Y x)
  let v₀ := fun s => M (z s) + t
  let A := fun s => (S₀.comp D) + ((pq.flip (b s)).comp K) + ((pq (v₀ s)).comp Y)
  let c := fun s => c₀ + S₀ (z s) + dotProduct (v₀ s) (b s) + h s
  refine ⟨q,B,A,c,?_ ,?_ ,?_⟩
  · intro x
    change b₀ x x + b₀ x x = 0
    exact CharTwo.add_self_eq_zero _
  · intro u x
    change b₀ (u+x) (u+x) = b₀ u u + b₀ x x + b₀ 0 0 + (b₀ u x + b₀ x u)
    simp only [map_add, map_zero, LinearMap.add_apply, LinearMap.zero_apply, add_zero]
    abel
  · intro s x hx
    have he : S.env (y s x) = D x + z s := hD s x hx
    rw [h₀, ht, he, hY s x hx]
    simp only [map_add, LinearMap.comp_apply, LinearMap.add_apply, K, q, v₀, A, c]
    change c₀ + (S₀ (D x) + S₀ (z s)) +
      dotProduct (M (D x) + M (z s) + t) (Y x + b s) + h s =
      dotProduct (M (D x)) (Y x) +
      (S₀ (D x) + dotProduct (M (D x)) (b s) +
        (dotProduct (M (z s)) (Y x) + dotProduct t (Y x))) +
      (c₀ + S₀ (z s) + dotProduct (M (z s) + t) (b s) + h s)
    simp only [dotProduct_add, add_dotProduct]
    abel

end PEqualNP.Outside.L_meta_32579_aux.PhaseChart


namespace PEqualNP.Outside.L_meta_32579_aux.Rank

open scoped BigOperators

abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F × F
abbrev Form (n : ℕ) := LinearMap.BilinForm F (V n)

noncomputable def tweak {n : ℕ} (w : Fin n → F) : Form n :=
  LinearMap.mk₂ F (fun x y => ∑ i, w i * ((x i).1 * (y i).2 + (x i).2 * (y i).1))
    (by intro x y z; rw [← Finset.sum_add_distrib]; congr 1; ext i;
        simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]; ring)
    (by intro a x y; simp only [smul_eq_mul, Finset.mul_sum]; congr 1; ext i;
        change w i * ((a * (x i).1) * (y i).2 + (a * (x i).2) * (y i).1) =
          a * (w i * ((x i).1 * (y i).2 + (x i).2 * (y i).1)); ring)
    (by intro x y z; rw [← Finset.sum_add_distrib]; congr 1; ext i;
        simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]; ring)
    (by intro a x y; simp only [smul_eq_mul, Finset.mul_sum]; congr 1; ext i;
        change w i * ((x i).1 * (a * (y i).2) + (x i).2 * (a * (y i).1)) =
          a * (w i * ((x i).1 * (y i).2 + (x i).2 * (y i).1)); ring)

theorem tweak_apply {n : ℕ} (w : Fin n → F) (x y : V n) :
    tweak w x y = ∑ i, w i * ((x i).1 * (y i).2 + (x i).2 * (y i).1) := rfl

private theorem binary_cancel (a : F) : a + a = 0 := by fin_cases a <;> decide

private theorem tweak_alt {n : ℕ} (w : Fin n → F) (x : V n) : tweak w x x = 0 := by
  rw [tweak_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [mul_comm (x i).2, binary_cancel, mul_zero]

private def tailIn (n : ℕ) : V n →ₗ[F] V (n+1) where
  toFun x := Fin.cons 0 x
  map_add' x y := by ext i : 1; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  map_smul' a x := by ext i : 1; refine Fin.cases ?_ (fun i => ?_) i <;> simp

@[simp] private theorem tailIn_zero_apply {n : ℕ} (x : V n) : tailIn n x 0 = 0 := by
  change Fin.cons (α := fun _ => F × F) 0 x 0 = 0
  exact Fin.cons_zero _ _

@[simp] private theorem tailIn_succ_apply {n : ℕ} (x : V n) (i : Fin n) :
    tailIn n x i.succ = x i := rfl

private theorem tweak_cons {n : ℕ} (k : F) (u : Fin n → F) (x y : V (n+1)) :
    tweak (Fin.cons k u) x y =
      k * ((x 0).1 * (y 0).2 + (x 0).2 * (y 0).1) +
      tweak u (Fin.tail x) (Fin.tail y) := by
  simp [tweak_apply, Fin.sum_univ_succ, Fin.tail]

private theorem alt_flip {n : ℕ} {A : Form n} (hA : ∀ x, A x x = 0) (x y : V n) :
    A y x = -A x y := by
  have hc := hA (x+y)
  simp only [map_add, LinearMap.add_apply, hA, zero_add, add_zero] at hc
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hc)

private theorem onto_dual {n : ℕ} (A : Form n) (hA : Function.Injective A) :
    Function.Surjective A :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := F) (V := V n)).symm).mp hA

/-- One choice of paired-diagonal coefficients makes an alternating form nonsingular. -/
theorem exists_injective_tweak (n : ℕ) (B : Form n) (hB : ∀ x, B x x = 0) :
    ∃ u : Fin n → F, Function.Injective (B + tweak u) := by
  induction n with
  | zero => exact ⟨0, fun _ _ _ => Subsingleton.elim _ _⟩
  | succ n ih =>
    let B' : Form n := LinearMap.BilinForm.comp B (tailIn n) (tailIn n)
    obtain ⟨u, hu⟩ := ih B' (fun x => hB (tailIn n x))
    let D := B' + tweak u
    let A₀ := B + tweak (Fin.cons 0 u)
    have hD (k : F) (x y : V n) :
        (B + tweak (Fin.cons k u)) (tailIn n x) (tailIn n y) = D x y := by
      have ht (z : V n) : Fin.tail (tailIn n z) = z := rfl
      simp [D, B', tweak_cons, ht]
    have lift (p : F × F) : ∃ x : V (n+1), x 0 = p ∧ ∀ y, A₀ x (tailIn n y) = 0 := by
      let z : V (n+1) := Fin.cons p 0
      obtain ⟨s, hs⟩ := onto_dual D hu (-(A₀ z).comp (tailIn n))
      refine ⟨z + tailIn n s, by simp [z], fun y => ?_⟩
      have he := LinearMap.congr_fun hs y
      change D s y = -(A₀ z (tailIn n y)) at he
      rw [map_add, LinearMap.add_apply, show A₀ (tailIn n s) (tailIn n y) = D s y from hD 0 s y,
        he, add_neg_cancel]
    obtain ⟨e, he, het⟩ := lift (1, 0)
    obtain ⟨f, hf, hft⟩ := lift (0, 1)
    let k := 1 - A₀ e f
    let A := B + tweak (Fin.cons k u)
    have hA (x : V (n+1)) : A x x = 0 := by simp [A, hB, tweak_alt]
    have hkt (x : V (n+1)) (y : V n) : A x (tailIn n y) = A₀ x (tailIn n y) := by
      simp [A, A₀, tweak_cons]
    have hef : A e f = 1 := by
      change B e f + tweak (Fin.cons k u) e f = 1
      have hk : k = 1 - (B e f + tweak u (Fin.tail e) (Fin.tail f)) := by
        simp [k, A₀, tweak_cons]
      simp [tweak_cons, he, hf, hk]
      ring
    refine ⟨Fin.cons k u, ?_⟩
    change Function.Injective A
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' (y : V (n+1)) : A x y = 0 := LinearMap.congr_fun hx y
    let a := (x 0).1
    let b := (x 0).2
    let r := x - a • e - b • f
    have hr : r 0 = 0 := by
      apply Prod.ext <;> simp [r, a, b, he, hf]
    have hrt : tailIn n (Fin.tail r) = r := by
      change Fin.cons 0 (Fin.tail r) = r
      rw [← hr, Fin.cons_self_tail]
    have hrD : D (Fin.tail r) = 0 := by
      apply LinearMap.ext
      intro y
      rw [LinearMap.zero_apply, ← hD k, hrt]
      change A r (tailIn n y) = 0
      simp [r, hx', hkt, het, hft]
    have hrz : r = 0 := by
      rw [← hrt, show Fin.tail r = 0 from hu (hrD.trans (map_zero D).symm), map_zero]
    have hp : x = a • e + b • f := by
      change x - a • e - b • f = 0 at hrz
      calc
        x = (x - a • e) + a • e := (sub_add_cancel _ _).symm
        _ = a • e + b • f := by
          rw [sub_eq_zero.mp hrz]
          exact add_comm _ _
    have haz := hx' f
    rw [hp] at haz
    have hbz := hx' e
    rw [hp] at hbz
    simp [hA, hef] at haz
    simp [hA, alt_flip hA e f, hef] at hbz
    simp [hp, haz, hbz]

def sign (a : F) : ℝ := if a = 0 then 1 else -1

private theorem eq_zero_or_one (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem complement_mismatch (a b : F) : (a ≠ b + 1) ↔ ¬(a ≠ b) := by
  rcases eq_zero_or_one a with rfl | rfl <;>
    rcases eq_zero_or_one b with rfl | rfl <;>
    simp [binary_cancel (1 : F)]

private theorem sign_add (a b : F) : sign (a+b) = sign a * sign b := by
  rcases eq_zero_or_one a with rfl | rfl <;>
    rcases eq_zero_or_one b with rfl | rfl <;>
    simp [sign, binary_cancel (1 : F)]

private theorem sign_le_one (a : F) : sign a ≤ 1 := by unfold sign; split <;> norm_num

private theorem linear_sign_sum {n : ℕ} (L : V n →ₗ[F] F) :
    (∑ x, sign (L x)) = if (∀ x, L x = 0) then (4 : ℝ)^n else 0 := by
  classical
  split_ifs with h
  · simp [h, sign]
  · push Not at h
    obtain ⟨a, ha⟩ := h
    have hL : L a = 1 := (eq_zero_or_one (L a)).resolve_left ha
    have hh := Fintype.sum_equiv (Equiv.addLeft a) (fun x => sign (L (a+x)))
      (fun x => sign (L x)) (fun _ => rfl)
    simp only [map_add, sign_add, hL, ← Finset.mul_sum] at hh
    have hsign : sign 1 = -1 := by norm_num [sign]
    rw [hsign, neg_one_mul] at hh
    linarith

private theorem square_sum {n : ℕ} (g : V n → F) (A : Form n)
    (hg : ∀ t x, g (t+x) = g t + g x + g 0 + A t x) :
    (∑ x, sign (g x))^2 = ∑ t, sign (g t + g 0) * ∑ x, sign (A t x) := by
  rw [pow_two, Finset.sum_mul]
  calc
    (∑ x, sign (g x) * ∑ y, sign (g y)) =
        ∑ x, ∑ t, sign (g x) * sign (g (t+x)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.addRight x) _ _ (fun _ => rfl)).symm
    _ = ∑ t, sign (g t + g 0) * ∑ x, sign (A t x) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← sign_add, ← sign_add, hg]
      congr 1
      calc
        g x + (g t + g x + g 0 + A t x) =
            (g x + g x) + ((g t + g 0) + A t x) := by abel
        _ = _ := by rw [binary_cancel, zero_add]

private theorem radical_card_le {n : ℕ} (B : Form n) (u w : Fin n → F)
    (hu : Function.Injective (B + tweak u)) :
    (Finset.univ.filter (fun t : V n => ∀ x, (B + tweak w) t x = 0)).card ≤
      4 ^ (Finset.univ.filter (fun i => w i ≠ u i)).card := by
  classical
  let R := Finset.univ.filter (fun t : V n => ∀ x, (B + tweak w) t x = 0)
  let I := Finset.univ.filter (fun i => w i ≠ u i)
  let restrict : R → (I → F × F) := fun t i => t.1 i.1
  have hinj : Function.Injective restrict := by
    intro t s h
    apply Subtype.ext
    apply hu
    apply LinearMap.ext
    intro x
    have hrad (z : R) : B z.1 x + tweak w z.1 x = 0 :=
      (Finset.mem_filter.mp z.2).2 x
    have htweak (z : V n) :
        tweak u z x - tweak w z x =
          ∑ i, (u i - w i) * ((z i).1 * (x i).2 + (z i).2 * (x i).1) := by
      simp only [tweak_apply, ← Finset.sum_sub_distrib, sub_mul]
    have hre : tweak u t.1 x - tweak w t.1 x = tweak u s.1 x - tweak w s.1 x := by
      rw [htweak, htweak]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : w i = u i
      · simp [hi]
      · rw [show t.1 i = s.1 i from congrFun h ⟨i, by simp [I, hi]⟩]
    change B t.1 x + tweak u t.1 x = B s.1 x + tweak u s.1 x
    linear_combination hrad t - hrad s + hre
  have hc := Fintype.card_le_of_injective restrict hinj
  rw [Fintype.card_coe R, Fintype.card_pi] at hc
  simpa only [Fintype.card_prod, ZMod.card, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe I, show (2 : ℕ) * 2 = 4 by decide] using hc

/-- The paired-diagonal rank center bounds every affine shift of the quadratic phase. -/
theorem exists_bias_center {n : ℕ} (q : V n → F) (B : Form n)
    (hB : ∀ x, B x x = 0)
    (hq : ∀ t x, q (t+x) = q t + q x + q 0 + B t x) :
    ∃ b : Fin n → F, ∀ (w : Fin n → F) (L : V n →ₗ[F] F) (c : F),
      |(∑ x, sign (q x + (∑ i, w i * (x i).1 * (x i).2) + L x + c)) /
        (2 : ℝ)^(2*n)| ≤ (1 : ℝ) / 2^(Finset.univ.filter (fun i => w i ≠ b i)).card := by
  classical
  obtain ⟨u, hu⟩ := exists_injective_tweak n B hB
  refine ⟨fun i => u i + 1, fun w L c => ?_⟩
  let Q : V n → F := fun x => ∑ i, w i * (x i).1 * (x i).2
  have hQ₀ : Q 0 = 0 := by simp [Q]
  have hQ (t x : V n) : Q (t+x) = Q t + Q x + tweak w t x := by
    simp only [Q, tweak_apply, ← Finset.sum_add_distrib, Pi.add_apply, Prod.fst_add, Prod.snd_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  let A := B + tweak w
  let g : V n → F := fun x => q x + Q x + L x + c
  have hg (t x : V n) : g (t+x) = g t + g x + g 0 + A t x := by
    have hc := binary_cancel c
    simp only [g, A, hq, hQ, hQ₀, map_add, map_zero, add_zero, LinearMap.add_apply]
    linear_combination -hc
  let R := Finset.univ.filter (fun t : V n => ∀ x, A t x = 0)
  let d := (Finset.univ.filter (fun i => w i ≠ u i + 1)).card
  let e := (Finset.univ.filter (fun i => w i ≠ u i)).card
  have hde : d + e = n := by
    simp only [d, e, complement_mismatch]
    rw [add_comm, Finset.card_filter_add_card_filter_not]
    simp
  have hCard : (R.card : ℝ) ≤ 4^e := by
    exact_mod_cast radical_card_le B u w hu
  have hSq : (∑ x, sign (g x))^2 ≤ ((2 : ℝ)^n * 2^e)^2 := by
    rw [square_sum g A hg]
    calc
      (∑ t, sign (g t + g 0) * ∑ x, sign (A t x)) ≤
          ∑ t : V n, if (∀ x, A t x = 0) then (4 : ℝ)^n else 0 := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [linear_sign_sum (A t)]
        split_ifs
        · exact mul_le_of_le_one_left (by positivity) (sign_le_one _)
        · simp
      _ = (R.card : ℝ) * 4^n := by simp [R, Finset.sum_ite]
      _ ≤ (4 : ℝ)^e * 4^n := mul_le_mul_of_nonneg_right hCard (by positivity)
      _ = ((2 : ℝ)^n * 2^e)^2 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2, mul_comm e 2, pow_mul, pow_mul]
        norm_num [mul_comm]
  have habs := abs_le_of_sq_le_sq hSq (by positivity)
  change |(∑ x, sign (g x)) / (2 : ℝ)^(2*n)| ≤ 1 / (2 : ℝ)^d
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)^(2*n))]
  calc
    |∑ x, sign (g x)| / (2 : ℝ)^(2*n) ≤ ((2 : ℝ)^n * 2^e) / (2 : ℝ)^(2*n) :=
      div_le_div_of_nonneg_right habs (by positivity)
    _ = 1 / (2 : ℝ)^d := by
      rw [div_eq_div_iff (by positivity) (by positivity), one_mul]
      rw [mul_assoc, ← pow_add, add_comm e d, hde, ← pow_add, two_mul]

end PEqualNP.Outside.L_meta_32579_aux.Rank

namespace PEqualNP.Outside.L_meta_32579_aux.LeafAvg

open scoped BigOperators

abbrev F := ZMod 2
abbrev Dat (v : ℕ) := Fin v → F
abbrev Prs (m : ℕ) := (Fin m × Bool) → F

set_option maxHeartbeats 1000000 in
/-- The paired-rank center for a leaf bounds the bias uniformly over its affine translates
and over all affine terms in the phase. -/
theorem exists_bias_center {v m : ℕ} (U : Submodule F (Dat v)) [Fintype U]
    (P : Dat v →ₗ[F] Prs m) (J : Finset (Fin m)) (side : Fin m → Bool)
    (L : Prs m →ₗ[F] Dat v) (hmem : ∀ x, L x ∈ U)
    (hgood : ∀ x i b, i ∉ J → P (L x) (i,b) = x (i,b))
    (hbad : ∀ x i, i ∈ J → P (L x) (i,side i) = 0)
    (q : Dat v → F) (B : LinearMap.BilinForm F (Dat v))
    (hB : ∀ x, B x x = 0)
    (hq : ∀ t x, q (t+x) = q t + q x + q 0 + B t x) :
    ∃ b : Fin m → F, ∀ (a : Dat v) (w : Fin m → F) (A : Dat v →ₗ[F] F) (c : F),
      |(∑ u : U, Rank.sign (q (a + u.1) +
        (∑ i, w i * P (a + u.1) (i,false) * P (a + u.1) (i,true)) + A (a+u.1) + c)) /
        (Fintype.card U : ℝ)| ≤
        (1 : ℝ) / 2^(Finset.univ.filter (fun i => i ∉ J ∧ w i ≠ b i)).card := by
  classical
  let G : Finset (Fin m) := Jᶜ
  let n := Fintype.card G
  let e : Fin n ≃ G := (Fintype.equivFin G).symm
  let ix (i : Fin m) (hi : i ∉ J) : Fin n := e.symm ⟨i, by simpa [G] using hi⟩
  have he (j : Fin n) : (e j).1 ∉ J := Finset.mem_compl.mp (e j).2
  have hix (j : Fin n) : ix (e j).1 (he j) = j := e.symm_apply_apply j
  let E : Rank.V n →ₗ[F] Prs m :=
    { toFun := fun x p => if hi : p.1 ∉ J then
          (if p.2 then (x (ix p.1 hi)).2 else (x (ix p.1 hi)).1) else 0
      map_add' := by intro x y; funext ⟨i,s⟩; by_cases hi : i ∈ J <;> cases s <;> simp [hi]
      map_smul' := by intro c x; funext ⟨i,s⟩; by_cases hi : i ∈ J <;> cases s <;> simp [hi] }
  let S := L.comp E
  let S' : Rank.V n →ₗ[F] U := S.codRestrict U (fun x => hmem (E x))
  let T : U →ₗ[F] Rank.V n :=
    { toFun := fun u j => (P u.1 ((e j).1,false), P u.1 ((e j).1,true))
      map_add' := by intro u z; funext j; simp
      map_smul' := by intro c u; funext j; simp }
  have hTS (x : Rank.V n) : T (S' x) = x := by
    funext j
    apply Prod.ext
    · change P (L (E x)) ((e j).1,false) = (x j).1
      rw [hgood _ _ _ (he j)]
      change (if hi : (e j).1 ∉ J then (if false then (x (ix (e j).1 hi)).2
        else (x (ix (e j).1 hi)).1) else 0) = _
      simp [he, hix]
    · change P (L (E x)) ((e j).1,true) = (x j).2
      rw [hgood _ _ _ (he j)]
      change (if hi : (e j).1 ∉ J then (if true then (x (ix (e j).1 hi)).2
        else (x (ix (e j).1 hi)).1) else 0) = _
      simp [he, hix]
  let K := LinearMap.ker T
  let _ : Fintype K := Fintype.ofFinite K
  let split : K × Rank.V n ≃ U :=
    { toFun := fun p => p.1.1 + S' p.2
      invFun := fun u => (⟨u - S' (T u), by simp [K, LinearMap.mem_ker, hTS]⟩, T u)
      left_inv := by
        rintro ⟨k,x⟩
        have hk : T k.1 = 0 := k.2
        have ht : T (k.1 + S' x) = x := by simp [hk, hTS]
        exact Prod.ext (Subtype.ext (by simp [ht])) ht
      right_inv := by intro u; exact sub_add_cancel _ _ }
  let q' : Rank.V n → F := q ∘ S
  let B' := B.comp S S
  obtain ⟨b', hb'⟩ := Rank.exists_bias_center q' B'
    (fun x => hB (S x)) (fun t x => by simpa [q', B'] using hq (S t) (S x))
  let b : Fin m → F := fun i => if hi : i ∉ J then b' (ix i hi) else 0
  have hb (j : Fin n) : b (e j).1 = b' j := by simp [b, he, hix]
  have reindex (f : Fin m → F) : (∑ i ∈ G, f i) = ∑ j, f (e j).1 := by
    rw [Finset.sum_subtype G (fun _ => Iff.rfl)]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  refine ⟨b, fun a w A c => ?_⟩
  let w' : Fin n → F := fun j => w (e j).1
  let d := (Finset.univ.filter (fun i => i ∉ J ∧ w i ≠ b i)).card
  have hd : (Finset.univ.filter (fun j => w' j ≠ b' j)).card = d := by
    simp only [d, w', ← hb]
    let f : Fin m → ℕ := fun i => if w i ≠ b i then 1 else 0
    calc
      _ = ∑ j, f (e j).1 := by simp [f, Finset.sum_ite]
      _ = ∑ i : G, f i.1 := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = ∑ i ∈ G, f i := (Finset.sum_subtype G (fun _ => Iff.rfl) f).symm
      _ = _ := by
        have hfilter : G.filter (fun i => w i ≠ b i) =
            Finset.univ.filter (fun i => i ∉ J ∧ w i ≠ b i) := by
          ext i
          simp [G]
        simp [f, Finset.sum_ite, hfilter]
  let M (i : Fin m) (s : Bool) : Rank.V n →ₗ[F] F :=
    (LinearMap.proj (i,s)).comp (P.comp S)
  let Q (t : Dat v) : F := ∑ i, w i * P t (i,false) * P t (i,true)
  have hquad (x : Rank.V n) : Q (S x) = ∑ j, w' j * (x j).1 * (x j).2 := by
    unfold Q
    calc
      _ = ∑ i ∈ G, w i * P (S x) (i,false) * P (S x) (i,true) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hz := hbad (E x) i (by simpa [G] using hi)
        change P (S x) (i, side i) = 0 at hz
        cases hs : side i <;> simp_all only [mul_zero, zero_mul]
      _ = _ := by
        rw [reindex]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hf := congrArg Prod.fst (congrFun (hTS x) j)
        have ht := congrArg Prod.snd (congrFun (hTS x) j)
        change P (S x) ((e j).1,false) = (x j).1 at hf
        change P (S x) ((e j).1,true) = (x j).2 at ht
        rw [hf, ht]
  let C (t : Dat v) : Rank.V n →ₗ[F] F :=
    (B t).comp S + A.comp S + ∑ i, ((w i * P t (i,false)) • M i true +
      (w i * P t (i,true)) • M i false)
  let k₀ (t : Dat v) := q t + q 0 + Q t + A t + c
  have hexp (t : Dat v) (x : Rank.V n) :
      q (t + S x) + Q (t + S x) + A (t + S x) + c =
      q' x + (∑ j, w' j * (x j).1 * (x j).2) + C t x + k₀ t := by
    rw [← hquad, hq, map_add]
    simp only [C, k₀, q', Function.comp_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have hQ : Q (t + S x) = Q t + Q (S x) + ∑ i,
        ((w i * P t (i,false)) * M i true x + (w i * P t (i,true)) * M i false x) := by
      simp only [Q, ← Finset.sum_add_distrib, map_add, Pi.add_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      change _ = w i * P t (i,false) * P t (i,true) +
        w i * P (S x) (i,false) * P (S x) (i,true) +
        (w i * P t (i,false) * P (S x) (i,true) + w i * P t (i,true) * P (S x) (i,false))
      ring
    rw [hQ]
    abel
  let g (u : U) := Rank.sign (q (a+u.1) + Q (a+u.1) + A (a+u.1) + c)
  let N : ℝ := (2 : ℝ)^(2*n)
  let R : ℝ := 1 / 2^d
  have hN : 0 < N := by dsimp [N]; positivity
  have hinner (k : K) : |∑ x : Rank.V n, g (split (k,x))| ≤ N * R := by
    have ht := hb' w' (C (a+k.1.1)) (k₀ (a+k.1.1))
    rw [hd] at ht
    have hg (x : Rank.V n) : g (split (k,x)) =
        Rank.sign (q' x + (∑ j, w' j * (x j).1 * (x j).2) + C (a+k.1.1) x + k₀ (a+k.1.1)) := by
      change Rank.sign (q (a+(k.1.1+S x)) + Q (a+(k.1.1+S x)) + A (a+(k.1.1+S x)) + c) = _
      rw [← add_assoc, hexp]
    simp only [hg]
    rw [mul_comm N R, ← div_le_iff₀ hN]
    rw [abs_div, abs_of_pos (show 0 < (2 : ℝ)^(2*n) from hN)] at ht
    exact ht
  have hcard : (Fintype.card U : ℝ) = (Fintype.card K : ℝ) * N := by
    rw [← Fintype.card_congr split, Fintype.card_prod, Nat.cast_mul]
    norm_num [N, Rank.V, Fintype.card_pi, two_mul, pow_add, ← mul_pow]
  have hsum : (∑ u, g u) = ∑ k : K, ∑ x : Rank.V n, g (split (k,x)) := by
    calc
      _ = ∑ p : K × Rank.V n, g (split p) :=
        (Fintype.sum_equiv split _ _ (fun _ => rfl)).symm
      _ = _ := Fintype.sum_prod_type (fun p : K × Rank.V n => g (split p))
  change |(∑ u, g u) / (Fintype.card U : ℝ)| ≤ R
  have hpos : 0 < (Fintype.card U : ℝ) := by positivity
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos, hsum, hcard]
  calc
    _ ≤ ∑ k : K, |∑ x : Rank.V n, g (split (k,x))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : K, N * R := Finset.sum_le_sum fun k _ => hinner k
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end PEqualNP.Outside.L_meta_32579_aux.LeafAvg


namespace PEqualNP.Outside.L_meta_32579_aux.Fibers

variable {F : Type*} [Field F] {k v : ℕ}


private def selectorProjection (H : Submodule F ((Fin k → F) × (Fin v → F))) : H →ₗ[F] (Fin k → F) :=
  (LinearMap.fst F (Fin k → F) (Fin v → F)).comp H.subtype

private def dataFiber (H : Submodule F ((Fin k → F) × (Fin v → F))) : Submodule F (Fin v → F) :=
  H.comap (LinearMap.inr F (Fin k → F) (Fin v → F))

private def kernelEquivFiber (H : Submodule F ((Fin k → F) × (Fin v → F))) :
    (selectorProjection H).ker ≃ₗ[F] dataFiber H where
  toFun y := ⟨y.val.val.2, by
    change (0, y.val.val.2) ∈ H
    have hy : y.val.val.1 = 0 := y.property
    rw [show (0, y.val.val.2) = y.val.val from Prod.ext hy.symm rfl]
    exact y.val.property⟩
  invFun x := ⟨⟨(0, x.val), x.property⟩, rfl⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (show 0 = y.val.val.1 from Eq.symm (show y.val.val.1 = 0 from y.property)) rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- An address chart whose data offset is affine on the whole selector space. -/
theorem affineAddressChartLinear (H : Submodule F ((Fin k → F) × (Fin v → F))) (a : (Fin k → F) × (Fin v → F)) :
    ∃ (G : Submodule F (Fin k → F)) (U : Submodule F (Fin v → F)) (L : (Fin k → F) →ₗ[F] (Fin v → F)),
      Module.finrank F G + Module.finrank F U = Module.finrank F H ∧
      ∀ (s : (Fin k → F)) (x : (Fin v → F)), ((s, x) - a ∈ H) ↔
        (s - a.1 ∈ G ∧ x - (a.2 + L (s - a.1)) ∈ U) := by
  let p := selectorProjection H
  let G := p.range
  let U := dataFiber H
  obtain ⟨sectionMap, hsection⟩ := p.rangeRestrict.exists_rightInverse_of_surjective
    p.range_rangeRestrict
  obtain ⟨C, hC⟩ := G.exists_isCompl
  let L : (Fin k → F) →ₗ[F] (Fin v → F) :=
    (LinearMap.snd F (Fin k → F) (Fin v → F)).comp (H.subtype.comp (sectionMap.comp (G.projectionOnto C hC)))
  refine ⟨G, U, L, ?_, ?_⟩
  · have he : Module.finrank F p.ker = Module.finrank F U := (kernelEquivFiber H).finrank_eq
    rw [← he]
    exact p.finrank_range_add_finrank_ker
  · intro s x
    have lift_mem (hs : s - a.1 ∈ G) : (s - a.1, L (s - a.1)) ∈ H := by
      have he : (sectionMap ⟨s - a.1, hs⟩).val.1 = s - a.1 :=
        congrArg (fun f : G →ₗ[F] G => (f ⟨s - a.1, hs⟩ : (Fin k → F))) hsection
      change (s - a.1, (sectionMap (G.projectionOnto C hC (s - a.1))).val.2) ∈ H
      rw [G.projectionOnto_apply_of_mem_left hC hs]
      rw [show (s - a.1, (sectionMap ⟨s - a.1, hs⟩).val.2) =
        (sectionMap ⟨s - a.1, hs⟩).val from Prod.ext he.symm rfl]
      exact (sectionMap ⟨s - a.1, hs⟩).property
    constructor
    · intro h
      have hs : s - a.1 ∈ G := ⟨⟨(s, x) - a, h⟩, rfl⟩
      refine ⟨hs, ?_⟩
      change (0, x - (a.2 + L (s - a.1))) ∈ H
      have h' := H.sub_mem h (lift_mem hs)
      change (s - a.1 - (s - a.1), x - a.2 - L (s - a.1)) ∈ H at h'
      simpa only [sub_self, sub_sub] using h'
    · rintro ⟨hs, hx⟩
      change (0, x - (a.2 + L (s - a.1))) ∈ H at hx
      have h' := H.add_mem (lift_mem hs) hx
      change (s - a.1 + 0, L (s - a.1) + (x - (a.2 + L (s - a.1)))) ∈ H at h'
      rw [add_zero, show L (s - a.1) + (x - (a.2 + L (s - a.1))) = x - a.2 by abel] at h'
      exact h'

/-- An affine translate of a submodule, expressed as a family of data cosets. -/
theorem affineAddressChart (H : Submodule F ((Fin k → F) × (Fin v → F))) (a : (Fin k → F) × (Fin v → F)) :
    ∃ (G : Submodule F (Fin k → F)) (U : Submodule F (Fin v → F)) (t : (Fin k → F) → (Fin v → F)),
      Module.finrank F G + Module.finrank F U = Module.finrank F H ∧
      ∀ (s : (Fin k → F)) (x : (Fin v → F)), ((s, x) - a ∈ H) ↔ (s - a.1 ∈ G ∧ x - t s ∈ U) := by
  obtain ⟨G, U, L, hd, hm⟩ := affineAddressChartLinear H a
  exact ⟨G, U, fun s => a.2 + L (s - a.1), hd, hm⟩

/-- Each coset of `W` in a translate of `G` has a unique representative in a fixed complement. -/
theorem addressCosetReps {W G : Submodule F (Fin k → F)} (hWG : W ≤ G) (a : (Fin k → F) × (Fin v → F)) :
    ∃ R : Submodule F (Fin k → F),
      Module.finrank F W + Module.finrank F R = Module.finrank F G ∧
      (∀ s : (Fin k → F), s - a.1 ∈ G → ∃! i : R, s - (a.1 + (i : (Fin k → F))) ∈ W) ∧
      (∀ (s : (Fin k → F)) (i : R), s - (a.1 + (i : (Fin k → F))) ∈ W → s - a.1 ∈ G) := by
  obtain ⟨C, hc⟩ := W.exists_isCompl
  let R := G ⊓ C
  have hdis : Disjoint W R := hc.disjoint.mono_right inf_le_right
  have decomp (y : (Fin k → F)) (hy : y ∈ G) : ∃ w ∈ W, ∃ r ∈ R, w + r = y := by
    have hy' : y ∈ W ⊔ C := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, r, hr, he⟩ := Submodule.mem_sup.mp hy'
    have hrG : r ∈ G := by
      have := G.sub_mem hy (hWG hw)
      simpa only [← he, add_sub_cancel_left] using this
    exact ⟨w, hw, r, ⟨hrG, hr⟩, he⟩
  have hsup : W ⊔ R = G := by
    refine le_antisymm (sup_le hWG inf_le_left) ?_
    intro y hy
    exact Submodule.mem_sup.mpr (decomp y hy)
  refine ⟨R, ?_, ?_, ?_⟩
  · rw [← Submodule.finrank_sup_add_finrank_inf_eq, hsup, hdis.eq_bot,
      finrank_bot, add_zero]
  · intro s hs
    obtain ⟨w, hw, r, hr, he⟩ := decomp (s - a.1) hs
    have hw' : s - (a.1 + r) = w := by
      rw [← sub_sub, ← he, add_sub_cancel_right]
    have hrep : s - (a.1 + r) ∈ W := by rwa [hw']
    refine ⟨⟨r, hr⟩, hrep, ?_⟩
    intro j hj
    change s - (a.1 + (j : (Fin k → F))) ∈ W at hj
    have hdW : (j : (Fin k → F)) - r ∈ W := by
      have h := W.sub_mem hrep hj
      rwa [show (s - (a.1 + r)) - (s - (a.1 + (j : (Fin k → F)))) = (j : (Fin k → F)) - r by abel] at h
    have hdR := R.sub_mem j.property hr
    have hz : (j : (Fin k → F)) - r = 0 := by
      have hm : (j : (Fin k → F)) - r ∈ W ⊓ R := ⟨hdW, hdR⟩
      simpa [hdis.eq_bot] using hm
    exact Subtype.ext (sub_eq_zero.mp hz)
  · intro s i hi
    have hm := G.add_mem (hWG hi) i.property.1
    rwa [show s - (a.1 + (i : (Fin k → F))) + (i : (Fin k → F)) = s - a.1 by abel] at hm

end PEqualNP.Outside.L_meta_32579_aux.Fibers



-- Circuit builder adapted from 1394d5d0d05067cc059aa91efad768024d32ee62,
-- lean/PEqualNP/Outside/L_meta_30642.lean, lines 4–22, 490–499, 845, 963, 1527–1921.
namespace PEqualNP.Outside.L_meta_32579_aux.Attain
noncomputable section Attainment
open scoped BigOperators
abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
namespace PivotFinish
theorem bit_gate_pair :
    ∀ a b : F,
    let ba := decide (a = 1)
    let bb := decide (b = 1)
    PEqualNP.CircuitLowerBounds.GateOp.and.eval [ba,bb] = decide (a*b = 1) ∧
    PEqualNP.CircuitLowerBounds.GateOp.or.eval [ba,bb] = decide (a+b+a*b = 1) ∧
    PEqualNP.CircuitLowerBounds.GateOp.not.eval
      [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [ba,bb]] =
      decide (a+b = 1) := by
  decide +kernel

end PivotFinish
namespace GateDecode
open PEqualNP.CircuitLowerBounds
abbrev F := ZMod 2

def bit (x : F) : Bool := decide (x = 1)

def costly (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

def legal (g : Gate) : Prop := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))
end GateDecode
namespace CircuitBridge
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32579_aux.Attain.GateDecode
noncomputable def paid (g : Gate) : Bool := @decide (costly g) (Classical.propDecidable _)
end CircuitBridge
namespace Lower
open PEqualNP.Outside.L_meta_32579_aux.Attain.GateDecode
abbrev Vec := V
def bits {n : ℕ} (x : Vec n) : List Bool := List.ofFn (fun i => bit (x i))
end Lower
namespace Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_32579_aux.Attain.GateDecode PEqualNP.Outside.L_meta_32579_aux.Attain.CircuitBridge

structure Build (n : ℕ) where
  gates : List Gate
  hlegal : ∀ g ∈ gates, legal g
  hback : ReadsBack n ⟨gates,0⟩

def Build.circ {n : ℕ} (B : Build n) (out : ℕ) : Circuit := ⟨B.gates,out⟩

def Build.next {n : ℕ} (B : Build n) : ℕ := n + B.gates.length

noncomputable def Build.cost {n : ℕ} (B : Build n) : ℕ := B.gates.countP paid

def empty (n : ℕ) : Build n :=
  ⟨[], by simp, by simp [ReadsBack]⟩

private theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt,List.getD_eq_getElem?_getD,hj]

def Build.snoc {n : ℕ} (B : Build n) (g : Gate) (h : legal g)
    (hb : ∀ i ∈ g.inputs, i < B.next) : Build n where
  gates := B.gates++[g]
  hlegal := by
    intro a ha
    simp only [List.mem_append,List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact B.hlegal a ha
    · exact h
  hback := by
    intro j hj i hi
    have hf : j < (B.gates++[g]).length := hj
    rw [gateAt_eq hj] at hi
    change i ∈ ((B.gates++[g])[j]'hf).inputs at hi
    by_cases hr : j < B.gates.length
    · rw [List.getElem_append_left hr] at hi
      have hh : j < (⟨B.gates,0⟩ : Circuit).gates.length := hr
      apply B.hback j hh i
      simpa only [gateAt_eq hh] using hi
    · have hj' : j = B.gates.length := by simp at hf; omega
      subst j
      have hg : (B.gates++[g])[B.gates.length] = g := by
        rw [List.getElem_append_right (by omega)]
        simp
      rw [hg] at hi
      exact hb i hi

theorem Build.next_snoc {n : ℕ} (B : Build n) (g : Gate) (h) (hb) :
    (B.snoc g h hb).next = B.next+1 := by
  simp [Build.next,Build.snoc,Nat.add_assoc]

theorem Build.cost_snoc {n : ℕ} (B : Build n) (g : Gate) (h) (hb) :
    (B.snoc g h hb).cost = B.cost + (if paid g then 1 else 0) := by
  simp [Build.cost, Build.snoc, List.countP_append]

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem Build.len_wires {n : ℕ} (B : Build n) (w : List Bool) (hw : w.length = n) :
    ((B.circ 0).wires w).length = B.next := by
  have aux (gs : List Gate) (l : List Bool) :
      (gs.foldl step l).length = l.length + gs.length := by
    induction gs generalizing l with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp [step]
      omega
  change (B.gates.foldl step w).length = _
  rw [aux,hw]
  rfl

def Build.get {n : ℕ} (B : Build n) (w : List Bool) (i : ℕ) : Bool :=
  (B.circ i).eval w

private theorem Build.step_wires {n : ℕ} (B : Build n) (g : Gate) (h) (hb) (w : List Bool) :
    ((B.snoc g h hb).circ 0).wires w = step ((B.circ 0).wires w) g := by
  change (B.gates++[g]).foldl step w = step (B.gates.foldl step w) g
  rw [List.foldl_append]
  rfl

theorem Build.get_snoc_old {n : ℕ} (B : Build n) (g : Gate) (h) (hb)
    (w : List Bool) (hw : w.length=n) (i : ℕ) (hi : i < B.next) :
    (B.snoc g h hb).get w i = B.get w i := by
  change (((B.snoc g h hb).circ 0).wires w).getD i false = ((B.circ 0).wires w).getD i false
  rw [Build.step_wires]
  unfold step
  exact List.getD_append _ _ _ _ (by rw [B.len_wires w hw]; exact hi)

theorem Build.get_snoc_new {n : ℕ} (B : Build n) (g : Gate) (h) (hb)
    (w : List Bool) (hw : w.length=n) :
    (B.snoc g h hb).get w B.next = g.op.eval (g.inputs.map fun i => B.get w i) := by
  change (((B.snoc g h hb).circ 0).wires w).getD B.next false =
    g.op.eval (g.inputs.map fun i => ((B.circ 0).wires w).getD i false)
  rw [Build.step_wires]
  rw [← B.len_wires w hw]
  unfold step
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
  rfl

end Builder

namespace BuildOps
open PEqualNP.Outside.L_meta_32579_aux.Attain.Builder
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32579_aux.Attain.GateDecode

structure Ext {n : ℕ} (A B : Build n) : Prop where
  next_le : A.next ≤ B.next
  keeps : ∀ w : List Bool, w.length = n → ∀ i < A.next, B.get w i = A.get w i

theorem Ext.refl {n} (A : Build n) : Ext A A := ⟨le_rfl,fun _ _ _ _ => rfl⟩
theorem Ext.trans {n} {A B C : Build n} (h : Ext A B) (k : Ext B C) : Ext A C :=
  ⟨h.next_le.trans k.next_le, fun w hw i hi => (k.keeps w hw i (hi.trans_le h.next_le)).trans (h.keeps w hw i hi)⟩

theorem grow {n} (A : Build n) (g : Gate) (hl) (hb) : Ext A (A.snoc g hl hb) :=
  ⟨by rw [A.next_snoc]; omega, fun w hw i hi => A.get_snoc_old g hl hb w hw i hi⟩

theorem genConst {n} (A : Build n) (b : Bool) :
    ∃ (B : Build n) (i : ℕ), Ext A B ∧ i < B.next ∧ B.cost = A.cost ∧
      ∀ w : List Bool, w.length = n → B.get w i = b := by
  let g : Gate := ⟨if b then .and else .or, []⟩
  have hl : legal g := by cases b <;> simp [legal,g]
  have hb : ∀ i ∈ g.inputs, i < A.next := by simp [g]
  refine ⟨A.snoc g hl hb,A.next,grow A g hl hb,by rw [A.next_snoc]; omega,?_ , ?_⟩
  · rw [A.cost_snoc]
    cases b <;> simp [CircuitBridge.paid, costly, g]
  · intro w hw
    rw [A.get_snoc_new g hl hb w hw]
    cases b <;> rfl

theorem genAnd {n} (A : Build n) (i j : ℕ) (hi : i < A.next) (hj : j < A.next) :
    ∃ (B : Build n) (k : ℕ), Ext A B ∧ k < B.next ∧ B.cost = A.cost+1 ∧
    ∀ w : List Bool, w.length=n → B.get w k = (A.get w i && A.get w j) := by
  let g : Gate := ⟨.and,[i,j]⟩
  have hl : legal g := by simp [legal,g]
  have hb : ∀ a ∈ g.inputs, a < A.next := by
    intro a ha
    simp only [g,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl <;> assumption
  refine ⟨A.snoc g hl hb,A.next,grow A g hl hb,by rw [A.next_snoc]; omega,?_ , ?_⟩
  · rw [A.cost_snoc]; simp [CircuitBridge.paid, costly, g]
  · intro w hw
    rw [A.get_snoc_new g hl hb w hw]
    simp [g,GateOp.eval]

theorem genXor {n} (A : Build n) (i j : ℕ) (hi : i < A.next) (hj : j < A.next) :
    ∃ (B : Build n) (k : ℕ), Ext A B ∧ k < B.next ∧ B.cost = A.cost ∧
    ∀ (w : List Bool), w.length=n → ∀ a b : F, A.get w i = bit a → A.get w j = bit b →
      B.get w k = bit (a+b) := by
  let g : Gate := ⟨.mod 2,[i,j]⟩
  have hg : legal g := by simp [legal,g]
  have gh : ∀ a ∈ g.inputs, a < A.next := by
    intro a ha
    simp only [g,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl <;> assumption
  let M := A.snoc g hg gh
  let v := A.next
  have hv : v < M.next := by dsimp [v,M]; rw [A.next_snoc]; omega
  let t : Gate := ⟨.not,[v]⟩
  have ht : legal t := by simp [legal,t]
  have th : ∀ a ∈ t.inputs, a < M.next := by simpa [t] using hv
  refine ⟨M.snoc t ht th,M.next,(grow A g hg gh).trans (grow M t ht th), by rw [M.next_snoc]; omega,?_,?_⟩
  · rw [M.cost_snoc,A.cost_snoc]; simp [CircuitBridge.paid, costly, g, t]
  · intro w hw a b ha hb
    rw [M.get_snoc_new t ht th w hw]
    change GateOp.not.eval [M.get w v] = bit (a+b)
    rw [show M.get w v = (GateOp.mod 2).eval [A.get w i,A.get w j] from A.get_snoc_new g hg gh w hw]
    rw [ha,hb]
    exact (PEqualNP.Outside.L_meta_32579_aux.Attain.PivotFinish.bit_gate_pair a b).2.2

theorem bitMul (a b : F) : (bit a && bit b) = bit (a*b) :=
  (by decide : ∀ a b : F, (bit a && bit b) = bit (a*b)) a b

end BuildOps
namespace UpperBase
open scoped BigOperators
abbrev Vec := V
open PEqualNP.Outside.L_meta_32579_aux.Attain.GateDecode (bit)
open PEqualNP.Outside.L_meta_32579_aux.Attain.Lower (bits)
open PEqualNP.Outside.L_meta_32579_aux.Attain.Builder

abbrev width (k t : ℕ) := 2*k+t

def inp {k t : ℕ} (x y : Vec k) (z : Vec t) : List Bool := bits x ++ bits y ++ bits z


def xwire {k : ℕ} (i : Fin k) : ℕ := i.val
def ywire {k : ℕ} (i : Fin k) : ℕ := k+i.val

theorem xbound {k t : ℕ} (i : Fin k) : xwire i < (empty (width k t)).next := by
  simp [xwire,empty,Build.next,width] <;> omega

theorem ybound {k t : ℕ} (i : Fin k) : ywire i < (empty (width k t)).next := by
  simp [ywire,empty,Build.next,width] <;> omega

private theorem bits_get {k : ℕ} (x : Vec k) (i : Fin k) : (bits x).getD i.val false = bit (x i) := by
  rw [List.getD_eq_getElem _ _ (by simp [bits])]
  simp [bits]

theorem xval {k t : ℕ} (x y : Vec k) (z : Vec t) (i : Fin k) :
    (empty (width k t)).get (inp x y z) (xwire i) = bit (x i) := by
  change ((bits x ++ bits y) ++ bits z).getD i.val false = _
  rw [List.getD_append _ _ _ _ (by simp [bits] <;> omega),
    List.getD_append _ _ _ _ (by simp [bits])]
  exact bits_get x i

theorem yval {k t : ℕ} (x y : Vec k) (z : Vec t) (i : Fin k) :
    (empty (width k t)).get (inp x y z) (ywire i) = bit (y i) := by
  change ((bits x ++ bits y) ++ bits z).getD (k+i.val) false = _
  rw [List.getD_append _ _ _ _ (by simp [bits] <;> omega),
      List.getD_append_right _ _ _ _ (by simp [bits])]
  simp only [bits,List.length_ofFn, Nat.add_sub_cancel_left]
  exact bits_get y i

end UpperBase

open Builder BuildOps PEqualNP.CircuitLowerBounds
open GateDecode (bit)
abbrev XY (n : Nat) := V n × V n
def Input {n} (x : XY n) := Lower.bits x.1 ++ Lower.bits x.2
theorem input_len {n} (x : XY n) : (Input x).length=2*n := by simp [Input,Lower.bits];omega

def Free {n} (B : Build (2*n)) (f : XY n → F) : Prop :=
  ∀ C, Ext B C → ∃ (E : Build (2*n)) (i : Nat), Ext C E ∧ i<E.next ∧ E.cost=C.cost ∧
    ∀ x, E.get (Input x) i=bit (f x)

theorem free_next {n} {B C : Build (2*n)} {f : XY n → F} (h : Ext B C) (hf : Free B f) : Free C f :=
  fun Z hz => hf Z (h.trans hz)

theorem free_wire {n} (B : Build (2*n)) (j : Nat) (lt : j<B.next) (f : XY n → F)
    (ev : ∀ x, B.get (Input x) j=bit (f x)) : Free B f := by
  intro C h
  exact ⟨C,j,Ext.refl _,lt.trans_le h.next_le,rfl,fun x => (h.keeps _ (input_len x) j lt).trans (ev x)⟩

theorem free_const {n} (B : Build (2*n)) (s : F) : Free B (fun _ => s) := by
  intro C _
  obtain ⟨E,i,he,hi,hc,ev⟩ := genConst C (bit s)
  exact ⟨E,i,he,hi,hc,fun x => ev _ (input_len x)⟩

theorem free_add {n} {B : Build (2*n)} {f g : XY n → F} (hf : Free B f) (hg : Free B g) :
    Free B (fun x => f x+g x) := by
  intro C h
  obtain ⟨E,i,hCE,hi,cE,vi⟩ := hf C h
  obtain ⟨K,j,hEK,hj,cK,vj⟩ := hg E (h.trans hCE)
  obtain ⟨Q,q,hKQ,hq,cQ,vq⟩ := genXor K i j (hi.trans_le hEK.next_le) hj
  refine ⟨Q,q,(hCE.trans hEK).trans hKQ,hq,cQ.trans (cK.trans cE),?_⟩
  intro x
  exact vq _ (input_len x) _ _ ((hEK.keeps _ (input_len x) _ hi).trans (vi x)) (vj x)

theorem free_scale {n} {B : Build (2*n)} {f : XY n → F} (s : F) (hf : Free B f) :
    Free B (fun x => s*f x) := by
  rcases (show s=0 ∨ s=1 from (by decide : ∀ s : F, s=0 ∨ s=1) s) with h|h
  · simpa only [h,zero_mul] using free_const B 0
  · simpa only [h,one_mul] using hf

theorem free_sum {n} {B : Build (2*n)} {ι : Type*} [DecidableEq ι] (S : Finset ι) {f : ι → XY n → F}
    (h : ∀ i∈S,Free B (f i)) : Free B (fun x => ∑ i∈S, f i x) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using free_const B 0
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact free_add (h i (by simp)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem paid_set {n} {B : Build (2*n)} {ι : Type*} [DecidableEq ι] (S : Finset ι) (f g : ι → XY n → F)
    (hf : ∀ i∈S,Free B (f i)) (hg : ∀ i∈S,Free B (g i)) :
    ∃ C, Ext B C ∧ C.cost=B.cost+S.card ∧ ∀ i∈S, Free C (fun x => f i x*g i x) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨B,Ext.refl _,by simp,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨C,hBC,cC,vC⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    obtain ⟨E,a,hCE,ha,cE,va⟩ := hf i (by simp) C hBC
    obtain ⟨K,b,hEK,hb,cK,vb⟩ := hg i (by simp) E (hBC.trans hCE)
    obtain ⟨Q,j,hKQ,hj,cQ,vj⟩ := genAnd K a b (ha.trans_le hEK.next_le) hb
    let hCQ := (hCE.trans hEK).trans hKQ
    refine ⟨Q,hBC.trans hCQ,by rw [cQ,cK,cE,cC,Finset.card_insert_of_notMem hi];omega,?_⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with eq|mem
    · subst t
      apply free_wire Q j hj
      intro x
      rw [vj _ (input_len x),hEK.keeps _ (input_len x) _ ha,va,vb,bitMul]
    · exact free_next hCQ (vC t mem)

theorem raw_x {n} (i : Fin n) : Free (empty (2*n)) (fun z : XY n => z.1 i) := by
  apply free_wire _ (UpperBase.xwire i) (UpperBase.xbound (t:=0) i)
  intro z
  simpa [Input,UpperBase.inp,Lower.bits] using UpperBase.xval z.1 z.2 (0 : V 0) i

theorem raw_y {n} (i : Fin n) : Free (empty (2*n)) (fun z : XY n => z.2 i) := by
  apply free_wire _ (UpperBase.ywire i) (UpperBase.ybound (t:=0) i)
  intro z
  simpa [Input,UpperBase.inp,Lower.bits] using UpperBase.yval z.1 z.2 (0 : V 0) i

theorem free_linear {n} (L : V n →ₗ[F] F) :
    Free (empty (2*n)) (fun z : XY n => L z.2) := by
  classical
  have h (y : V n) : L y = ∑ j, L (Pi.single j 1) * y j := by
    have hy : (∑ j, y j • (Pi.single j 1 : V n)) = y := by
      ext i
      simp [Pi.single_apply, Finset.sum_apply, smul_ite]
    conv_lhs => rw [← hy, map_sum]
    simp only [map_smul, smul_eq_mul, mul_comm]
  have hf := free_sum Finset.univ (fun j _ => free_scale (L (Pi.single j 1)) (raw_y j))
  exact (show (fun z : XY n => ∑ j, L (Pi.single j 1) * z.2 j) = _ from
    funext fun z => (h z.2).symm) ▸ hf

theorem raw_dot_x {n} (l : V n) : Free (empty (2*n)) (fun z : XY n => dotProduct z.1 l) :=
  free_sum Finset.univ (fun j _ => by
    simpa only [mul_comm] using free_scale (l j) (raw_x j))

def Fits {n : ℕ} (p : ℕ) (C : Circuit) : Prop :=
  (PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
    ∀ a ∈ C.gates, GateDecode.legal a) ∧ C.gates.countP CircuitBridge.paid ≤ p

/-- The address used in the bilinear part is `y₀ + Σ qⱼ uⱼ`. An extra product
can be routed to any one of the taps, so its outer multiplication is free of
additional paid cost. -/
theorem build_taps {n : ℕ} {ι η : Type*} [DecidableEq ι] [DecidableEq η]
    (I : Finset ι) (J : Finset η) (y₀ : V n) (u : ι → V n)
    (q l : ι → V n → F) (A B : η → V n → F) (atTap : η → ι) (g₀ : F)
    (fq : ∀ j ∈ I, Free (empty (2*n)) (fun z => q j z.2))
    (fl : ∀ j ∈ I, Free (empty (2*n)) (fun z => l j z.2))
    (fA : ∀ i ∈ J, Free (empty (2*n)) (fun z => A i z.2))
    (fB : ∀ i ∈ J, Free (empty (2*n)) (fun z => B i z.2)) :
    ∃ C : Circuit, Fits (n:=n) (I.card + J.card) C ∧ ∀ x y,
      C.eval (Lower.bits x ++ Lower.bits y) = bit
        (dotProduct x (y₀ + ∑ j ∈ I, q j y • u j) +
          (g₀ + ∑ j ∈ I, q j y * (l j y + ∑ i ∈ J.filter (fun i => atTap i = j), A i y * B i y))) := by
  let E := empty (2*n)
  obtain ⟨P,hEP,cP,vP⟩ := paid_set (B:=E) J (fun i z => A i z.2) (fun i z => B i z.2) fA fB
  let T (j : ι) (z : XY n) :=
    dotProduct z.1 (u j) + (l j z.2 + ∑ i ∈ J.filter (fun i => atTap i = j), A i z.2 * B i z.2)
  have fT (j) (hj : j ∈ I) : Free P (T j) :=
    free_add (free_next hEP (raw_dot_x _)) <| free_add (free_next hEP (fl j hj)) <|
      free_sum _ (fun i hi => vP i (Finset.mem_filter.mp hi).1)
  obtain ⟨K,hPK,cK,vK⟩ := paid_set I (fun j z => q j z.2) T
    (fun j hj => free_next hEP (fq j hj)) fT
  have hf := free_add (free_next (hEP.trans hPK) (raw_dot_x y₀))
    (free_add (free_const K g₀) (free_sum I vK))
  obtain ⟨Q,o,_,_,cQ,vQ⟩ := hf K (Ext.refl _)
  refine ⟨Q.circ o, ⟨⟨Q.hback, Q.hlegal⟩, ?_⟩, ?_⟩
  · change Q.cost ≤ I.card + J.card
    rw [cQ,cK,cP,show E.cost = 0 from rfl]
    omega
  · intro x y
    change Q.get (Input (x,y)) o = _
    rw [vQ (x,y)]
    congr 1
    change dotProduct x y₀ + (g₀ + ∑ j ∈ I, q j y * T j (x,y)) = _
    simp only [T, mul_add, Finset.sum_add_distrib, dotProduct_add, dotProduct_sum, dotProduct_smul]
    simp_rw [show ∀ j, q j y * dotProduct x (u j) = dotProduct x (u j) * q j y from
      fun j => mul_comm _ _]
    ring

def sign (a : F) : ℝ := if a = 0 then 1 else -1

theorem sign_add (a b : F) : sign (a+b) = sign a * sign b := by
  have casesF : ∀ a : F, a = 0 ∨ a = 1 := by decide
  rcases casesF a with rfl | rfl <;> rcases casesF b with rfl | rfl <;>
    simp [sign, CharTwo.add_self_eq_zero]

theorem sign_one : sign 1 = -1 := by norm_num [sign]

theorem sign_zero : sign 0 = 1 := by simp [sign]

theorem sign_eq (a b : F) :
    (if bit a = bit b then (1 : ℝ) else -1) = sign (a + b) := by
  have casesF : ∀ a : F, a = 0 ∨ a = 1 := by decide
  rcases casesF a with rfl | rfl <;> rcases casesF b with rfl | rfl <;>
    simp [bit, sign, CharTwo.add_self_eq_zero]

theorem sign_sum {ι : Type*} (I : Finset ι) (f : ι → F) :
    sign (∑ i ∈ I, f i) = ∏ i ∈ I, sign (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [sign]
  | @insert i I hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, sign_add, ih]

theorem sum_sign_dot {n} (y : V n) :
    (∑ x : V n, sign (dotProduct x y)) = if y = 0 then (2 : ℝ)^n else 0 := by
  classical
  by_cases hy : y = 0
  · simp [hy, sign, Fintype.card_fun, ZMod.card]
  rw [if_neg hy]
  obtain ⟨i, hi⟩ : ∃ i, y i = 1 := by
    by_contra! h
    apply hy
    ext i
    exact ((by decide : ∀ v : F, v = 0 ∨ v = 1) (y i)).resolve_right (h i)
  let d : V n := Pi.single i 1
  have hd : dotProduct d y = 1 := by simp [d, dotProduct, Pi.single_apply, hi]
  let e : V n ≃ V n := Equiv.addRight d
  have h := Fintype.sum_equiv e (fun x => sign (dotProduct x y))
    (fun x => -sign (dotProduct x y)) (fun x => by
      change sign (dotProduct x y) = -sign (dotProduct (x + d) y)
      rw [add_dotProduct,hd,sign_add,sign_one]; ring)
  rw [Finset.sum_neg_distrib] at h
  linarith

theorem x_orthogonality {n} (y Y : V n) (g v : F) :
    (∑ x : V n, if bit (dotProduct x Y + g) = bit (dotProduct x y + v)
      then (1 : ℝ) else -1) = if Y = y then 2^n * sign (g+v) else 0 := by
  classical
  simp_rw [sign_eq]
  have hh (x : V n) : dotProduct x Y + g + (dotProduct x y + v) =
      dotProduct x (Y+y) + (g+v) := by rw [dotProduct_add]; ring
  simp_rw [hh, sign_add]
  rw [← Finset.sum_mul, sum_sign_dot]
  have hz : Y + y = 0 ↔ Y = y := by
    have hn : -y = y := funext fun i => CharTwo.neg_eq (y i)
    calc
      Y + y = 0 ↔ Y + (-y) = 0 := by rw [hn]
      _ ↔ Y = y := by rw [← sub_eq_add_neg]; exact sub_eq_zero
  rw [if_congr hz rfl rfl]
  split <;> simp

theorem coord_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → F) :
    (∑ j, q j • Pi.single j (1 : F)) = q := by
  classical
  ext j
  simp [Finset.sum_apply, Pi.single_apply, smul_ite]

theorem linear_coords {ι E : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup E] [Module F E]
    (L : (ι → F) →ₗ[F] E) (q : ι → F) :
    L q = ∑ j, q j • L (Pi.single j 1) := by
  classical
  calc
    L q = L (∑ j, q j • Pi.single j (1 : F)) := congrArg L (coord_expansion q).symm
    _ = _ := by simp only [map_sum, map_smul]

theorem fit_mono {n p q : ℕ} {C : Circuit} (h : Fits (n:=n) p C) (hp : p ≤ q) :
    Fits (n:=n) q C := ⟨h.1, h.2.trans hp⟩

/-- Implement an affine parameterized address, a quadratic in its parameters, and
selected extra products, each multiplied by one of the tap coordinates. -/
theorem build_affine_address {n : ℕ} {ι η : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq η]
    (J : Finset η) (y₀ : V n) (T : (ι → F) →ₗ[F] V n) (hT : Function.Injective T)
    (g₀ : F) (L : ι → F) (M : ι → ι → F)
    (A B : η → V n →ₗ[F] F) (atTap : η → ι) :
    ∃ (C : Circuit) (q : V n → ι → F),
      Fits (n:=n) (Fintype.card ι + J.card) C ∧
      (∀ z, q (y₀ + T z) = z) ∧ ∀ x y,
      C.eval (Lower.bits x ++ Lower.bits y) = bit (dotProduct x (y₀ + T (q y)) +
        (g₀ + (∑ j, q y j * (L j + ∑ k, M j k * q y k)) +
          ∑ i ∈ J, q y (atTap i) * (A i y * B i y))) := by
  classical
  obtain ⟨R, hR⟩ := T.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hT)
  let q (y : V n) := R (y-y₀)
  let l (j : ι) (y : V n) := L j + ∑ k, M j k * q y k
  have fq (j : ι) : Free (empty (2*n)) (fun z => q z.2 j) := by
    have hf := free_linear ((LinearMap.proj j).comp R)
    simpa only [q, sub_eq_add_neg, map_add, map_neg, Pi.add_apply, Pi.neg_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
      using free_add hf (free_const _ (-R y₀ j))
  have fl (j : ι) : Free (empty (2*n)) (fun z => l j z.2) :=
    free_add (free_const _ _) (free_sum Finset.univ fun k _ => free_scale _ (fq k))
  obtain ⟨C, hc, hev⟩ := build_taps Finset.univ J y₀ (fun j => T (Pi.single j 1))
    (fun j y => q y j) l (fun i y => A i y) (fun i y => B i y) atTap g₀
    (fun j _ => fq j) (fun j _ => fl j) (fun i _ => free_linear _) (fun i _ => free_linear _)
  refine ⟨C, q, by simpa using hc, ?_, ?_⟩
  · intro z
    change R (y₀ + T z - y₀) = z
    rw [add_sub_cancel_left]
    exact LinearMap.congr_fun hR z
  · intro x y
    rw [hev, linear_coords T (q y)]
    congr 1
    have hExtra : (∑ j, q y j * ∑ i ∈ J.filter (fun i => atTap i = j), A i y * B i y) =
        ∑ i ∈ J, q y (atTap i) * (A i y * B i y) := by
      simp only [Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [show ∀ j, atTap i = j ↔ j = atTap i from fun _ => eq_comm]
      simp
    simp only [l, mul_add (q y _), Finset.sum_add_distrib, hExtra, add_assoc]

abbrev Data (m r : ℕ) := V m × (V m × V r)

def Score {k m r : ℕ} (e : V (k+2*m+r) ≃ₗ[F] V k × Data m r)
    (word : V k → Fin m → F) (h : V k → F) (C : Circuit) (s : V k) : ℝ :=
  (∑ x : V (k+2*m+r), ∑ b : V m, ∑ c : V m, ∑ z : V r,
    let y := e.symm (s,(b,(c,z)))
    let v := dotProduct x y + h s + ∑ i, word s i * b i * c i
    if C.eval (Lower.bits x ++ Lower.bits y) = bit v then (1 : ℝ) else -1) /
  2^(k+2*m+r+(2*m+r))

theorem score_address {k m r : ℕ} (e : V (k+2*m+r) ≃ₗ[F] V k × Data m r)
    (word : V k → Fin m → F) (h : V k → F)
    (C : Circuit) (Y : V (k+2*m+r) → V (k+2*m+r)) (g : V (k+2*m+r) → F)
    (hev : ∀ x y, C.eval (Lower.bits x ++ Lower.bits y) = bit (dotProduct x (Y y)+g y))
    (s : V k) :
    Score e word h C s =
      (∑ v : Data m r,
        let y := e.symm (s,v)
        if Y y = y then sign (g y + (h s + ∑ i, word s i * v.1 i * v.2.1 i)) else 0) /
        2^(2*m+r) := by
  classical
  let K (x : V (k+2*m+r)) (v : Data m r) : ℝ :=
    let y := e.symm (s,v)
    if C.eval (Lower.bits x ++ Lower.bits y) =
      bit (dotProduct x y + h s + ∑ i, word s i * v.1 i * v.2.1 i) then 1 else -1
  have h₁ : Score e word h C s = (∑ x, ∑ v, K x v) / 2^(k+2*m+r+(2*m+r)) := by
    unfold Score
    simp only [Fintype.sum_prod_type, K]
  have h₂ (v : Data m r) :
      (∑ x, K x v) =
        2^(k+2*m+r) * (if Y (e.symm (s,v)) = e.symm (s,v) then
          sign (g (e.symm (s,v)) + (h s + ∑ i, word s i * v.1 i * v.2.1 i)) else 0) := by
    simp only [K, hev, add_assoc (dotProduct _ _)]
    rw [x_orthogonality]
    split <;> simp
  rw [h₁, Finset.sum_comm]
  simp_rw [h₂, ← Finset.mul_sum, pow_add (2 : ℝ)]
  rw [mul_div_mul_left _ _ (by positivity)]

def Quad {ι : Type*} [Fintype ι] (f : (ι → F) → F) : Prop :=
  ∃ (o : F) (L : ι → F) (M : ι → ι → F), ∀ z,
    f z = o + ∑ j, z j * (L j + ∑ k, M j k * z k)

theorem quad_const {ι : Type*} [Fintype ι] (a : F) :
    Quad (fun _ : ι → F => a) :=
  ⟨a, 0, 0, fun _ => by simp⟩

theorem quad_add {ι : Type*} [Fintype ι] {f g : (ι → F) → F}
    (hf : Quad f) (hg : Quad g) : Quad (fun z => f z + g z) := by
  obtain ⟨a,L,M,hf⟩ := hf
  obtain ⟨b,K,N,hg⟩ := hg
  refine ⟨a+b,L+K,M+N,fun z => ?_⟩
  simp only [hf, hg, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hm (i : ι) :
      z i * (L i + K i + ((∑ j, M i j * z j) + ∑ j, N i j * z j)) =
        z i * (L i + ∑ j, M i j * z j) + z i * (K i + ∑ j, N i j * z j) := by ring
  simp_rw [hm, Finset.sum_add_distrib]
  ring

theorem quad_sum {ι η : Type*} [Fintype ι]
    (I : Finset η) (g : η → (ι → F) → F) (hg : ∀ i ∈ I, Quad (g i)) :
    Quad (fun z => ∑ i ∈ I, g i z) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using quad_const (ι:=ι) 0
  | @insert i I hi ih =>
    simpa only [Finset.sum_insert hi] using
      quad_add (hg i (Finset.mem_insert_self _ _)) (ih (fun j hj => hg j (Finset.mem_insert_of_mem hj)))

theorem quad_aff_prod {ι : Type*} [Fintype ι] (a b : F) (L M : (ι → F) →ₗ[F] F) :
    Quad (fun z => (a + L z) * (b + M z)) := by
  classical
  let l (i : ι) := L (Pi.single i 1)
  let m (i : ι) := M (Pi.single i 1)
  refine ⟨a*b, fun i => a*m i + l i*b, fun i j => l i * m j, fun z => ?_⟩
  change (a + L z) * (b + M z) = _
  rw [linear_coords L z, linear_coords M z]
  change (a + ∑ i, z i * l i) * (b + ∑ i, z i * m i) = _
  simp only [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  have h₁ : (∑ i, a * (z i * m i)) = ∑ i, z i * (a * m i) := by
    apply Finset.sum_congr rfl; intro i _; ring
  have h₂ : (∑ i, z i * l i * b) = ∑ i, z i * (l i * b) := by
    apply Finset.sum_congr rfl; intro i _; ring
  have h₃ : (∑ j, ∑ i, z i * l i * (z j * m j)) =
      ∑ i, ∑ j, z i * (l i * m j * z j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h₁,h₂,h₃]
  ring

theorem quad_affine {ι : Type*} [Fintype ι] (a : F) (L : (ι → F) →ₗ[F] F) :
    Quad (fun z => a + L z) := by
  simpa using quad_aff_prod a 1 L 0

theorem quad_pull {ι : Type*} [Fintype ι] {k : ℕ}
    (a : V k) (T : (ι → F) →ₗ[F] V k) {f : V k → F}
    (hf : ∃ (o : F) (l : V k) (M : Fin k → Fin k → F),
      ∀ s, f s = o + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j) :
    Quad (fun z => f (a + T z)) := by
  classical
  obtain ⟨o,l,M,hf⟩ := hf
  let P (i : Fin k) := (LinearMap.proj i).comp T
  have hl : Quad (fun z => dotProduct l (a + T z)) := by
    apply quad_sum Finset.univ
    intro i _
    simpa only [P, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, LinearMap.proj_apply,
      mul_add, Pi.add_apply] using quad_affine (l i*a i) (l i • P i)
  have hq : Quad (fun z => ∑ i, ∑ j, M i j * (a + T z) i * (a + T z) j) := by
    apply quad_sum Finset.univ
    intro i _
    apply quad_sum Finset.univ
    intro j _
    simpa only [P, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, LinearMap.proj_apply,
      mul_add, Pi.add_apply] using quad_aff_prod (M i j*a i) (a j) (M i j • P i) (P j)
  simp only [hf]
  exact quad_add (quad_add (quad_const o) hl) hq

theorem build_on_flat {n : ℕ} {ι η : Type*} [Fintype ι]
    (J : Finset η) (y₀ : V n) (T : (ι → F) →ₗ[F] V n) (hT : Function.Injective T)
    (A B : η → V n →ₗ[F] F) (atTap : η → ι) (g : (ι → F) → F) (hg : Quad g) :
    ∃ (C : Circuit) (Y : V n → V n) (G : V n → F),
      Fits (n:=n) (Fintype.card ι + J.card) C ∧
      (∀ y, Y y = y ↔ ∃ z, y = y₀ + T z) ∧
      (∀ z, G (y₀ + T z) = g z + ∑ i ∈ J, z (atTap i) * (A i (y₀ + T z) * B i (y₀ + T z))) ∧
      ∀ x y, C.eval (Lower.bits x ++ Lower.bits y) = bit (dotProduct x (Y y) + G y) := by
  classical
  obtain ⟨o,L,M,hg⟩ := hg
  obtain ⟨C,q,hC,hq,he⟩ := build_affine_address J y₀ T hT o L M A B atTap
  refine ⟨C, fun y => y₀ + T (q y), _, hC, ?_, ?_, he⟩
  · intro y
    exact ⟨fun h => ⟨q y,h.symm⟩, fun ⟨z,hz⟩ => by
      subst y
      change y₀ + T (q (y₀ + T z)) = y₀ + T z
      rw [hq]⟩
  · intro z
    rw [hq, ← hg]

def finExtend {p d : ℕ} (hp : p ≤ d) : V p →ₗ[F] V d where
  toFun v i := if h : i.val < p then v ⟨i.val,h⟩ else 0
  map_add' v w := by
    ext i
    by_cases h : i.val < p <;> simp [h]
  map_smul' c v := by
    ext i
    by_cases h : i.val < p <;> simp [h]

theorem finExtend_inj {p d : ℕ} (hp : p ≤ d) : Function.Injective (finExtend hp) := by
  intro v w hv
  ext i
  simpa [finExtend, i.isLt] using congrFun hv (Fin.castLE hp i)

theorem sign_difference (a b : F) : sign (a+b) = if b = a then 1 else -1 := by
  have h : a+b=0 ↔ b=a := by
    calc
      a+b=0 ↔ b + (-a) = 0 := by rw [CharTwo.neg_eq a, add_comm]
      _ ↔ b=a := by rw [← sub_eq_add_neg]; exact sub_eq_zero
  simp [sign, h]

theorem sum_image_const {α β : Type*} [Fintype α] [Fintype β] (E : α → β)
    (hE : Function.Injective E) [DecidablePred (fun b => b ∈ Set.range E)] (c : ℝ) :
    (∑ b : β, if b ∈ Set.range E then c else 0) = Fintype.card α * c := by
  classical
  have heq := Finset.sum_filter (s := (Finset.univ : Finset β))
    (fun b => b ∈ Set.range E) (fun _ => c)
  rw [← heq]
  let emb : α ↪ β := ⟨E,hE⟩
  have h : Finset.univ.filter (fun b => b ∈ Set.range E) = Finset.univ.map emb := by
    ext b
    simp [Set.mem_range, emb]
  rw [h, Finset.sum_map]
  simp [nsmul_eq_mul]

set_option maxHeartbeats 2000000 in
theorem attain_small {k m r p : ℕ} (hp : p < 2*m+r)
    (e : V (k+2*m+r) ≃ₗ[F] V k × Data m r)
    (word : V k → Fin m → F) (h f : V k → F) (a : V k) :
    ∃ C : Circuit, Fits (n:=k+2*m+r) p C ∧ ∀ s,
      Score e word h C s =
        (if h s = f s then 1 else -1) * (if s = a then 1 / 2^(2*m+r-p) else 0) := by
  classical
  let dataE : V (2*m+r) ≃ₗ[F] Data m r :=
    LinearEquiv.ofFinrankEq _ _ (by simp [Data, Module.finrank_prod, Module.finrank_fin_fun]; omega)
  let E := dataE.toLinearMap.comp (finExtend hp.le)
  have hE : Function.Injective E := dataE.injective.comp (finExtend_inj hp.le)
  let y₀ := e.symm (a,0)
  let T := e.symm.toLinearMap.comp ((LinearMap.inr F (V k) (Data m r)).comp E)
  have hT : Function.Injective T := fun u v huv =>
    hE (congrArg Prod.snd (e.symm.injective huv))
  have hparam (z : V p) : y₀ + T z = e.symm (a,E z) := by
    change e.symm (a,0) + e.symm (0,E z) = _
    rw [← map_add e.symm]
    congr 1
    simp
  let g (z : V p) := f a + ∑ i, word a i * (E z).1 i * (E z).2.1 i
  have hg : Quad g := by
    refine quad_add (quad_const _) (quad_sum Finset.univ _ ?_)
    intro i _
    let L := (LinearMap.proj i).comp ((LinearMap.fst F (V m) (V m × V r)).comp E)
    let R := (LinearMap.proj i).comp ((LinearMap.fst F (V m) (V r)).comp
      ((LinearMap.snd F (V m) (V m × V r)).comp E))
    simpa [L,R] using quad_aff_prod 0 0 (word a i • L) R
  obtain ⟨C,Y,G,hC,hY,hG,hev⟩ :=
    build_on_flat (∅ : Finset Empty) y₀ T hT Empty.elim Empty.elim Empty.elim g hg
  refine ⟨C, by simpa using hC, fun s => ?_⟩
  rw [score_address e word h C Y G hev]
  have hsupp (v : Data m r) : Y (e.symm (s,v)) = e.symm (s,v) ↔ s = a ∧ v ∈ Set.range E := by
    rw [hY]
    simp only [hparam, e.symm.injective.eq_iff, Prod.mk.injEq, Set.mem_range]
    exact ⟨fun ⟨z,hsz,hvz⟩ => ⟨hsz,z,hvz.symm⟩, fun ⟨hsz,z,hvz⟩ => ⟨z,hsz,hvz.symm⟩⟩
  by_cases hs : s = a
  · subst s
    have hterms (v : Data m r) :
        (if Y (e.symm (a,v)) = e.symm (a,v) then
          sign (G (e.symm (a,v)) + (h a + ∑ i, word a i * v.1 i * v.2.1 i)) else 0) =
        if v ∈ Set.range E then sign (f a + h a) else 0 := by
      by_cases hv : v ∈ Set.range E
      · rw [if_pos ((hsupp v).mpr ⟨rfl,hv⟩), if_pos hv]
        obtain ⟨z,rfl⟩ := hv
        rw [← hparam, hG]
        simp only [Finset.sum_empty, add_zero, g]
        congr 1
        rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]
      · rw [if_neg (fun hh => hv ((hsupp v).mp hh).2), if_neg hv]
    simp_rw [hterms]
    have hsum := sum_image_const (α := V p) (β := Data m r) E hE (sign (f a + h a))
    simp only [if_true]
    rw [hsum, ← sign_difference, Fintype.card_pi_const, ZMod.card]
    push_cast
    rw [show (2 : ℝ)^(2*m+r) = 2^p * 2^(2*m+r-p) by rw [← pow_add]; congr 1; omega]
    field_simp
    <;> ring
  · simp [hs, hsupp]

def pairCoords (m : ℕ) : (V m × V m) ≃ (Fin m → F × F) where
  toFun v i := (v.1 i, v.2 i)
  invFun v := (fun i => (v i).1, fun i => (v i).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_sign_pair (d : F) :
    (∑ a : F × F, sign (d * a.1 * a.2)) = if d = 0 then 4 else 2 := by
  have h : (Finset.univ : Finset F) = {0,1} := by decide
  have hh : ∀ a : F, a = 0 ∨ a = 1 := by decide
  rcases hh d with rfl|rfl <;>
    simp [Fintype.sum_prod_type, h, sign] <;> norm_num

theorem pair_bias {m r : ℕ} (d : V m) :
    (∑ v : Data m r, sign (∑ i, d i * v.1 i * v.2.1 i)) / 2^(2*m+r) =
      1 / 2^((Finset.univ : Finset (Fin m)).filter (fun i => d i ≠ 0)).card := by
  classical
  let H (bc : V m × V m) := sign (∑ i, d i * bc.1 i * bc.2 i)
  have h₁ : (∑ v : Data m r, sign (∑ i, d i * v.1 i * v.2.1 i)) =
      (∑ bc : V m × V m, H bc) * 2^r := by
    simp [Fintype.sum_prod_type, H, ZMod.card, nsmul_eq_mul, Finset.mul_sum, mul_comm]
  have h₂ : (∑ bc : V m × V m, H bc) =
      ∏ i, ∑ t : F × F, sign (d i * t.1 * t.2) := by
    rw [Fintype.prod_sum]
    apply Fintype.sum_equiv (pairCoords m)
    intro bc
    exact sign_sum Finset.univ _
  have h₃ : (2 : ℝ)^(2*m+r) = (∏ _ : Fin m, (4 : ℝ)) * 2^r := by
    rw [pow_add, pow_mul]
    norm_num
  rw [h₁,h₂,h₃,mul_div_mul_right _ _ (by positivity), ← Finset.prod_div_distrib]
  simp_rw [sum_sign_pair]
  have hh (i : Fin m) : ((if d i = 0 then 4 else 2) : ℝ) / 4 =
      if d i ≠ 0 then (2 : ℝ)⁻¹ else 1 := by
    by_cases hi : d i = 0 <;> norm_num [hi]
  simp_rw [hh]
  rw [Finset.prod_ite]
  simp [one_div]

def splitCoord {α β : Type*} : (α ⊕ β → F) ≃ₗ[F] (α → F) × (β → F) where
  toEquiv := Equiv.sumArrowEquivProdArrow α β F
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev LargeCoord (d m r : ℕ) := Fin d ⊕ (Fin m ⊕ (Fin m ⊕ Fin r))

def splitData (d m r : ℕ) : (LargeCoord d m r → F) ≃ₗ[F] V d × Data m r :=
  splitCoord.trans (LinearEquiv.prodCongr (LinearEquiv.refl F _)
    (splitCoord.trans (LinearEquiv.prodCongr (LinearEquiv.refl F _) splitCoord)))

theorem attain_large {k m r p : ℕ}
    (e : V (k+2*m+r) ≃ₗ[F] V k × Data m r)
    (A : Fin m → V k) (h f : V k → F) (a : V k) (W : Submodule F (V k))
    (J : Finset (Fin m)) (b₀ : V m)
    (hp : 2*m+r+Module.finrank F W+J.card ≤ p)
    (hf : ∃ (o : F) (l : V k) (M : Fin k → Fin k → F),
      ∀ s, f s = o + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j) :
    ∃ C : Circuit, Fits (n:=k+2*m+r) p C ∧ ∀ s,
      Score e (fun s i => dotProduct (A i) s) h C s =
        (if h s = f s then 1 else -1) *
          @ite ℝ (s-a ∈ W) (Classical.propDecidable _)
            (1 / 2^((Finset.univ : Finset (Fin m)).filter
              (fun i => i ∉ J ∧ dotProduct (A i) s ≠ b₀ i)).card) 0 := by
  classical
  let n := k+2*m+r
  let d := Module.finrank F W
  let ι := LargeCoord d m r
  let φ : V d ≃ₗ[F] W := LinearEquiv.ofFinrankEq _ _ (by simp [d, Module.finrank_fin_fun])
  let η := splitData d m r
  let U := (W.subtype.comp φ.toLinearMap).comp
    ((LinearMap.fst F (V d) (Data m r)).comp η.toLinearMap)
  let D := (LinearMap.snd F (V d) (Data m r)).comp η.toLinearMap
  let y₀ := e.symm (a,0)
  let T := e.symm.toLinearMap.comp (U.prod D)
  have hT : Function.Injective T := by
    intro u v huv
    have he : (U u,D u) = (U v,D v) := e.symm.injective huv
    apply η.injective
    apply Prod.ext
    · apply φ.injective
      apply Subtype.ext
      exact congrArg Prod.fst he
    · change D u = D v
      exact congrArg (fun x : V k × Data m r => x.2) he
  have hparam (z : ι → F) : y₀ + T z = e.symm (a+U z,D z) := by
    change e.symm (a,0) + e.symm (U z,D z) = _
    rw [← map_add e.symm]
    congr 1
    simp
  let atTap (i : Fin m) : ι := .inr (.inr (.inl i))
  have hTap (z : ι → F) (i : Fin m) : z (atTap i) = (D z).2.1 i := rfl
  let w (s : V k) (i : Fin m) := dotProduct (A i) s
  let α (i : Fin m) : V n →ₗ[F] F :=
    { toFun := fun y => dotProduct (A i) (e y).1
      map_add' := fun y z => by simp [dotProduct_add]
      map_smul' := fun a y => by simp [dotProduct_smul] }
  let β (i : Fin m) : V n →ₗ[F] F :=
    (LinearMap.proj i).comp ((LinearMap.fst F (V m) (V m × V r)).comp
      ((LinearMap.snd F (V k) (Data m r)).comp e.toLinearMap))
  have hα (s : V k) (v : Data m r) (i : Fin m) : α i (e.symm (s,v)) = w s i := by
    simp [α,w]
  have hβ (s : V k) (v : Data m r) (i : Fin m) : β i (e.symm (s,v)) = v.1 i := by
    simp [β]
  let g (z : ι → F) := f (a+U z) + ∑ i ∈ Finset.univ.filter (fun i => i ∉ J),
    b₀ i * (D z).1 i * (D z).2.1 i
  have hg : Quad g := by
    refine quad_add (quad_pull a U hf) (quad_sum _ _ ?_)
    intro i _
    let L := (LinearMap.proj i).comp ((LinearMap.fst F (V m) (V m × V r)).comp D)
    let R := (LinearMap.proj i).comp ((LinearMap.fst F (V m) (V r)).comp
      ((LinearMap.snd F (V m) (V m × V r)).comp D))
    simpa [L,R] using quad_aff_prod 0 0 (b₀ i • L) R
  obtain ⟨C,Y,G,hC,hY,hG,hev⟩ := build_on_flat J y₀ T hT α β atTap g hg
  refine ⟨C, fit_mono hC ?_, fun s => ?_⟩
  · have hcard : Fintype.card ι = d + (m + (m+r)) := by simp [ι, LargeCoord]
    rw [hcard]
    omega
  change Score e w h C s = _
  rw [score_address e w h C Y G hev]
  have hmem (v : Data m r) :
      Y (e.symm (s,v)) = e.symm (s,v) ↔ s-a ∈ W := by
    rw [hY]
    constructor
    · rintro ⟨z,hz⟩
      rw [hparam] at hz
      have hs : s = a+U z := congrArg Prod.fst (e.symm.injective hz)
      rw [hs,add_sub_cancel_left]
      exact (φ (η z).1).property
    · intro hs
      let q := η.symm (φ.symm ⟨s-a,hs⟩,v)
      have hU : U q = s-a := by simp [U,q]
      have hD : D q = v := by simp [D,q]
      refine ⟨q,?_⟩
      rw [hparam,hU,hD,add_comm a,sub_add_cancel]
  by_cases hs : s-a ∈ W
  · let δ (i : Fin m) := if i ∈ J then 0 else w s i + b₀ i
    have hG' (v : Data m r) :
        G (e.symm (s,v)) = f s + ∑ i, (if i ∈ J then w s i else b₀ i) * v.1 i * v.2.1 i := by
      obtain ⟨z,hz⟩ := (hY _).mp ((hmem v).mpr hs)
      have hsz : s = a+U z := congrArg Prod.fst (e.symm.injective (hz.trans (hparam z)))
      have hvz : v = D z := congrArg Prod.snd (e.symm.injective (hz.trans (hparam z)))
      have hx := hG z
      rw [← hz] at hx
      simp only [g,← hsz,← hvz,hα,hβ,hTap] at hx
      rw [hx]
      have hsplit : (∑ i, (if i ∈ J then w s i else b₀ i) * v.1 i * v.2.1 i) =
          (∑ i ∈ J, w s i * v.1 i * v.2.1 i) +
          ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), b₀ i * v.1 i * v.2.1 i := by
        simp_rw [ite_mul, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [hsplit,add_assoc,add_comm (∑ i ∈ J, _) (∑ i ∈ Finset.univ.filter _, _)]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hcancel (v : Data m r) :
        G (e.symm (s,v)) + (h s + ∑ i, w s i * v.1 i * v.2.1 i) =
          f s + h s + ∑ i, δ i * v.1 i * v.2.1 i := by
      rw [hG',add_add_add_comm,← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ J
      · simp [δ,hi,CharTwo.add_self_eq_zero]
      · simp [δ,hi,add_mul,add_comm]
    simp_rw [fun v => (hmem v).mpr hs, if_pos, hcancel, sign_add, ← Finset.mul_sum]
    rw [mul_div_assoc, pair_bias, ← sign_add, sign_difference, if_pos hs]
    have heq : (Finset.univ.filter (fun i => δ i ≠ 0)) =
        Finset.univ.filter (fun i => i ∉ J ∧ dotProduct (A i) s ≠ b₀ i) := by
      ext i
      by_cases hi : i ∈ J
      · simp [δ,hi]
      · simp [δ,hi,w,show dotProduct (A i) s + b₀ i = 0 ↔ dotProduct (A i) s = b₀ i from by
          calc
            dotProduct (A i) s + b₀ i = 0 ↔ dotProduct (A i) s + (-b₀ i) = 0 := by
              rw [CharTwo.neg_eq]
            _ ↔ _ := by rw [← sub_eq_add_neg]; exact sub_eq_zero]
    rw [heq]
  · simp [hmem, hs]

theorem attain (k m r : ℕ)
    (e : V (k+2*m+r) ≃ₗ[F] V k × Data m r)
    (A : Fin m → V k) (h : V k → F) (p : ℕ) :
    let base := 2*m+r
    let word := fun (s : V k) (i : Fin m) => dotProduct (A i) s
    let atom := fun (v : V k → ℝ) =>
      if p < base then ∃ a : V k, ∀ s, v s = if s = a then 1 / 2^(base-p) else 0
      else ∃ (a : V k) (W : Submodule F (V k)) (J : Finset (Fin m)) (b : V m),
        base + Module.finrank F W + J.card ≤ p ∧ ∀ s,
        let wt := ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ word s i ≠ b i)).card
        v s = @ite ℝ (s-a ∈ W) (Classical.propDecidable _) (1 / 2^wt) 0
    ∀ v : V k → ℝ, atom v → ∀ f : V k → F,
      (∃ (o : F) (l : V k) (M : Fin k → Fin k → F),
        ∀ s, f s = o + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j) →
      ∃ C : Circuit, Fits (n:=k+2*m+r) p C ∧
        ∀ s, Score e word h C s = (if h s = f s then 1 else -1) * v s := by
  dsimp only
  intro v hv f hf
  by_cases hp : p < 2*m+r
  · rw [if_pos hp] at hv
    obtain ⟨a,ha⟩ := hv
    obtain ⟨C,hC,hA⟩ := attain_small hp e (fun s i => dotProduct (A i) s) h f a
    exact ⟨C,hC,fun s => by rw [ha,hA]⟩
  · rw [if_neg hp] at hv
    obtain ⟨a,W,J,b,hcost,ha⟩ := hv
    obtain ⟨C,hC,hA⟩ := attain_large e A h f a W J b hcost hf
    exact ⟨C,hC,fun s => by rw [ha,hA]⟩

end Attainment
end PEqualNP.Outside.L_meta_32579_aux.Attain

namespace PEqualNP.Outside.L_meta_32579_aux.Upper

open scoped BigOperators
open PEqualNP.Outside.L_meta_32579_aux.RowPort.MonoSpan
open PEqualNP.Outside.L_meta_32579_aux.RowPort.Normalized (State)
open PEqualNP.Outside.L_meta_32579_aux.Row (mean phase bits circuit_rows row_address readWire)
open PEqualNP.Outside.L_meta_32579_aux.Mixtures

noncomputable def Atom {k m : ℕ} (base p : ℕ) (word : Vec k → Vec m) (v : Vec k → ℝ) : Prop :=
  if p < base then ∃ a : Vec k, ∀ s, v s = if s = a then 1/2^(base-p) else 0
  else ∃ (a : Vec k) (W : Submodule F (Vec k)) (J : Finset (Fin m)) (b : Vec m),
    base + Module.finrank F W + J.card ≤ p ∧ ∀ s,
    let wt := ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ word s i ≠ b i)).card
    v s = @ite ℝ (s-a ∈ W) (Classical.propDecidable _) (1/2^wt) 0

noncomputable def onSelector {k : ℕ} (W : Submodule F (Vec k)) (a : Vec k)
    (f : Vec k → ℝ) (s : Vec k) : ℝ :=
  @ite ℝ (s-a ∈ W) (Classical.propDecidable _) (f s) 0

theorem onSelector_pos {k : ℕ} (W : Submodule F (Vec k)) (a : Vec k) (f : Vec k → ℝ)
    (s : Vec k) (h : s-a ∈ W) : onSelector W a f s = f s := by
  unfold onSelector
  rw [if_pos h]

theorem onSelector_neg {k : ℕ} (W : Submodule F (Vec k)) (a : Vec k) (f : Vec k → ℝ)
    (s : Vec k) (h : s-a ∉ W) : onSelector W a f s = 0 := by
  unfold onSelector
  rw [if_neg h]

theorem onSelector_congr {k : ℕ} (W : Submodule F (Vec k)) (a : Vec k) (f g : Vec k → ℝ)
    (h : ∀ s, s-a ∈ W → f s = g s) : onSelector W a f = onSelector W a g := by
  funext s
  by_cases hs : s-a ∈ W
  · rw [onSelector_pos _ _ _ _ hs, onSelector_pos _ _ _ _ hs, h s hs]
  · rw [onSelector_neg _ _ _ _ hs, onSelector_neg _ _ _ _ hs]

private theorem singleton_atom {k m v p : ℕ} (word : Vec k → Vec m) (a : Vec k) :
    Atom v p word (fun s => if s = a then (if p < v then 1/2^(v-p) else 1) else 0) := by
  unfold Atom
  by_cases hp : p < v
  · rw [if_pos hp]
    exact ⟨a,by intro s; rw [if_pos hp]⟩
  · rw [if_neg hp]
    refine ⟨a,⊥,∅,word a,by simpa using Nat.le_of_not_gt hp,?_⟩
    intro s
    dsimp only
    rw [if_neg hp]
    have he : s-a ∈ (⊥ : Submodule F (Vec k)) ↔ s=a := by rw [Submodule.mem_bot,sub_eq_zero]
    by_cases h : s=a
    · subst s
      simp [he]
    · rw [if_neg h, if_neg (fun h' => h (he.mp h'))]

private theorem mass_factor {k v a : ℕ} (G : Submodule F (Vec k)) (U : Submodule F (Vec v))
    (h : Module.finrank F G + Module.finrank F U = a) : mass G * mass U = 2^a := by
  rw [mass,mass,← pow_add,h]

private theorem uniform_weights {k : ℕ} (R : Submodule F (Vec k)) [Fintype R] :
    (∑ _ : R, (1:ℝ)/mass R) = 1 := by
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_submodule]
  have hc : ((2^Module.finrank F R : ℕ) : ℝ) = mass R := by push_cast; rfl
  rw [hc, ← mul_div_assoc, mul_one, div_self (mass_pos _).ne']

private theorem lower_small {k v m a p : ℕ} (word : Vec k → Vec m)
    (G : Submodule F (Vec k)) (U : Submodule F (Vec v)) (a₀ : Vec k)
    (hd : Module.finrank F G + Module.finrank F U = a) (ha : a < v) (hp : a ≤ p)
    (f : Vec k → ℝ) (hf : ∀ s, |f s| ≤ 1) :
    Majorized (Atom v p word) (onSelector G a₀ (fun s => mass U / 2^v * f s)) := by
  classical
  let c : ℝ := if p < v then 1/2^(v-p) else 1
  let V : G → Vec k → ℝ := fun i s => if s = a₀+i.1 then c else 0
  have hc : 0 ≤ c := by dsimp [c]; split <;> positivity
  have hweight : 0 ≤ 1 / mass G := div_nonneg zero_le_one (mass_pos _).le
  have hratio : 0 ≤ mass U / (2:ℝ)^v := div_nonneg (mass_pos _).le (by positivity)
  have hle : mass U / (2:ℝ)^v ≤ (1/mass G)*c := by
    have h := mass_factor G U hd
    by_cases h' : p < v
    · have hN : a+(v-p) ≤ v := by omega
      have hP : (2:ℝ)^(a+(v-p)) ≤ 2^v := pow_le_pow_right₀ (by norm_num) hN
      rw [pow_add,← h] at hP
      dsimp only [c]
      rw [if_pos h']
      have hd₁ : 0 < mass G * (2:ℝ)^(v-p) := mul_pos (mass_pos _) (by positivity)
      rw [← mul_div_mul_comm, one_mul, div_le_div_iff₀ (by positivity) hd₁]
      convert hP using 1 <;> ring
    · dsimp only [c]
      rw [if_neg h',mul_one,div_le_div_iff₀ (by positivity) (mass_pos _)]
      have hP : (2:ℝ)^a ≤ 2^v := pow_le_pow_right₀ (by norm_num) ha.le
      rw [← h, mul_comm] at hP
      simpa using hP
  refine pack V (fun _ => 1/mass G) (fun i => ⟨singleton_atom word (a₀+i.1),hweight⟩)
    (uniform_weights G) ?_
  intro s
  have hNon (i : G) : 0 ≤ (1/mass G) * V i s := by
    apply mul_nonneg hweight
    unfold V
    split
    · exact hc
    · exact le_rfl
  by_cases hs : s-a₀ ∈ G
  · let j : G := ⟨s-a₀,hs⟩
    have hj : s = a₀+j.1 := by dsimp [j]; abel
    rw [onSelector_pos _ _ _ _ hs, abs_mul, abs_of_nonneg hratio]
    calc
      mass U / (2:ℝ)^v * |f s| ≤ mass U / 2^v := mul_le_of_le_one_right hratio (hf s)
      _ ≤ (1/mass G)*c := hle
      _ = (1/mass G)*V j s := by rw [show V j s = c from if_pos hj]
      _ ≤ ∑ i : G, (1/mass G)*V i s := Finset.single_le_sum (fun i _ => hNon i) (Finset.mem_univ j)
  · rw [onSelector_neg _ _ _ _ hs, abs_zero]
    exact Finset.sum_nonneg fun i _ => hNon i

noncomputable def pairPhase {k v m : ℕ} (P : Vec v →ₗ[F] Residual.Pairs m)
    (word : Vec k → Vec m) (s : Vec k) (x : Vec v) : F :=
  ∑ i, word s i * P x (i,false) * P x (i,true)

private theorem phase_eq_rank (x : F) : phase x = Rank.sign x := by
  have hb : ∀ x : F, x = 0 ∨ x = 1 := by decide
  rcases hb x with rfl | rfl <;> norm_num [phase, Rank.sign]

private theorem rank_leaf {k v m n d r : ℕ} (word : Vec k → Vec m)
    (P : Vec v →ₗ[F] Residual.Pairs m) (T : Residual.Part k v m)
    (hT : Residual.FreePairs P T) (y : Vec k → Vec v → Vec n) (hy : Residual.IsAffine T y)
    (S : State n n d r) (hE : Residual.IsAffine T (fun s x => S.env (y s x)))
    (j : ℕ) (h : Vec k → F) :
    ∃ b : Vec m, ∀ s,
      |averageOn T.dir (T.center s) (fun x => phase ((readWire S j).tail (S.env (y s x)) +
        dotProduct (fun i => (S.orig i).tail (S.env (y s x))) (y s x) + (h s + pairPhase P word s x)))| ≤
      (1:ℝ)/2^(Finset.univ.filter (fun i => i ∉ T.bad ∧ word s i ≠ b i)).card := by
  classical
  obtain ⟨q,B,A,c,hB,hq,h_eq⟩ := PhaseChart.fixed_quadratic T y hy S hE j h
  obtain ⟨b,hb⟩ := LeafAvg.exists_bias_center T.dir P T.bad T.side T.sectionMap
    hT.1 hT.2.1 hT.2.2 q B hB hq
  refine ⟨b,fun s => ?_⟩
  have he (z : T.dir) :
      (readWire S j).tail (S.env (y s (T.center s+z.1))) +
        dotProduct (fun i => (S.orig i).tail (S.env (y s (T.center s+z.1)))) (y s (T.center s+z.1)) +
        (h s + pairPhase P word s (T.center s+z.1)) =
      q (T.center s+z.1) + pairPhase P word s (T.center s+z.1) + A s (T.center s+z.1) + c s := by
    have hOn : Residual.On T s (T.center s+z.1) := by
      unfold Residual.On
      rw [add_sub_cancel_left]
      exact z.2
    rw [← add_assoc, h_eq _ _ hOn]
    abel
  have hb' := hb (T.center s) (word s) (A s) (c s)
  unfold averageOn mean
  simp_rw [he, phase_eq_rank]
  exact hb'

private theorem center_trim {k m : ℕ} (word : Vec k →ₗ[F] Vec m)
    (J₀ J : Finset (Fin m)) (hJ : J₀ ⊆ J) (W : Submodule F (Vec k))
    (hW : ∀ u ∈ W, ∀ i ∈ J₀, word u i = 0) (a : Vec k) (b : Vec m) :
    ∃ b' : Vec m, ∀ s, s-a ∈ W →
      ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J \ J₀ ∧ word s i ≠ b' i)) =
      ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ word s i ≠ b i)) := by
  classical
  refine ⟨fun i => if i ∈ J₀ then word a i else b i,?_⟩
  intro s hs
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ,true_and]
  by_cases hi : i ∈ J₀
  · have h0 := hW _ hs i hi
    rw [map_sub] at h0
    have he : word s i = word a i := sub_eq_zero.mp h0
    simp [hi,hJ hi,he]
  · simp [hi]

noncomputable def resPhase {k v m n d r : ℕ}
    (word : Vec k → Vec m) (P : Vec v →ₗ[F] Residual.Pairs m) (y : Vec k → Vec v → Vec n)
    (S : State n n d r) (j : ℕ) (h : Vec k → F) (s : Vec k) (x : Vec v) : ℝ :=
  phase ((readWire S j).tail (S.env (y s x)) +
    dotProduct (fun i => (S.orig i).tail (S.env (y s x))) (y s x) + (h s + pairPhase P word s x))

private theorem upper_large {k v m n d e a p : ℕ} (word : Vec k →ₗ[F] Vec m)
    (P : Vec v →ₗ[F] Residual.Pairs m) (hP : Function.Surjective P)
    (E : Vec n ≃ₗ[F] Vec k × Vec v) (S : State n n d e) (j : ℕ) (h : Vec k → F)
    (G : Submodule F (Vec k)) (U : Submodule F (Vec v))
    (a₀ : Vec k × Vec v) (t : Vec k → Vec v)
    (hd : Module.finrank F G + Module.finrank F U = a) (ha : v ≤ a) (hp : a+e ≤ p) :
    Majorized (Atom v p word) (onSelector G a₀.1 (fun s => mass U / 2^v *
      averageOn U (t s) (resPhase word P (fun s x => E.symm (s,x)) S j h s))) := by
  classical
  let y (s : Vec k) (x : Vec v) := E.symm (s,x)
  let g := resPhase word P y S j h
  have hu : Module.finrank F U ≤ v := by simpa using Submodule.finrank_le U
  have hwant : (a-v) + (v - Module.finrank F U) ≤ Module.finrank F G := by omega
  obtain ⟨J₀,side,L,W,hJ,hL,hfree,hzero,hWG,hWdim,hW⟩ :=
    Geometry.good_with_selector (d' := a-v) P hP U G word hwant
  obtain ⟨R,hRdim,hRep,hBack⟩ := Fibers.addressCosetReps hWG a₀
  change Module.finrank F W = a-v at hWdim
  change Module.finrank F W + Module.finrank F R = Module.finrank F G at hRdim
  have hmass : mass U / (2:ℝ)^v = 1/mass R := by
    have hd' : Module.finrank F R + Module.finrank F U = v := by omega
    have hm := mass_factor R U hd'
    rw [← hm]
    field_simp [(mass_pos U).ne']
  let T : Residual.Part k v m := ⟨t,U,J₀,side,L⟩
  obtain ⟨Q,hQ,hCov⟩ := Residual.partition P T ⟨hL,hfree,hzero⟩ y
    (PhaseChart.chart_y_affine E T) S.hEnv
  let leafWeight (i : Q) := mass i.1.dir / mass T.dir
  have hw := cutting_weights T Q (fun i hi => (hQ i hi).2.1) hCov 0
  have hbound (b₀ : Vec k) (i : Q) :
      Majorized (Atom v p word) (onSelector W b₀ (fun s => averageOn i.1.dir (i.1.center s) (g s))) := by
    obtain ⟨hP',hSub,hcard,hAff⟩ := hQ i.1 i.2
    obtain ⟨b,hb⟩ := rank_leaf word P i.1 hP' y (PhaseChart.chart_y_affine E i.1) S hAff j h
    obtain ⟨b',hb'⟩ := center_trim word J₀ i.1.bad hSub.1 W hW b₀ b
    let J := i.1.bad \ J₀
    let prof := onSelector W b₀ (fun s => (1:ℝ)/2^(Finset.univ.filter (fun l => l ∉ J ∧ word s l ≠ b' l)).card)
    refine majorized_of_atom (v := prof) ?_ ?_
    · unfold Atom
      rw [if_neg (by omega : ¬p<v)]
      refine ⟨b₀,W,J,b',?_,fun _ => rfl⟩
      have hcc := Finset.card_sdiff_add_card_eq_card hSub.1
      change (i.1.bad \ J₀).card + J₀.card = i.1.bad.card at hcc
      change v + Module.finrank F W + (i.1.bad \ J₀).card ≤ p
      have hQcard : i.1.bad.card ≤ J₀.card + e := hcard
      omega
    · intro s
      by_cases hs : s-b₀ ∈ W
      · unfold prof
        rw [onSelector_pos _ _ _ _ hs,onSelector_pos _ _ _ _ hs]
        change |averageOn i.1.dir (i.1.center s) (g s)| ≤
          (1:ℝ)/2^(Finset.univ.filter (fun l => l ∉ i.1.bad \ J₀ ∧ word s l ≠ b' l)).card
        rw [hb' _ hs]
        exact hb s
      · unfold prof
        rw [onSelector_neg _ _ _ _ hs,onSelector_neg _ _ _ _ hs,abs_zero]
  have hCoset (b₀ : Vec k) : Majorized (Atom v p word)
      (onSelector W b₀ (fun s => averageOn U (t s) (g s))) := by
    have hMix := mix (fun i : Q => onSelector W b₀ (fun s => averageOn i.1.dir (i.1.center s) (g s)))
      leafWeight hw.1 hw.2.1 (hbound b₀)
    have he : (fun s => ∑ i : Q, leafWeight i * onSelector W b₀
        (fun s => averageOn i.1.dir (i.1.center s) (g s)) s) =
        onSelector W b₀ (fun s => averageOn U (t s) (g s)) := by
      funext s
      by_cases hs : s-b₀ ∈ W
      · simp_rw [onSelector_pos _ _ _ _ hs]
        exact ((cutting_weights T Q (fun i hi => (hQ i hi).2.1) hCov s).2.2 (g s)).symm
      · simp_rw [onSelector_neg _ _ _ _ hs,mul_zero,Finset.sum_const_zero]
    rwa [he] at hMix
  let f := fun s => averageOn U (t s) (g s)
  have hMix := mix (fun i : R => onSelector W (a₀.1+i.1) f)
    (fun _ => 1/mass R) (fun _ => div_nonneg zero_le_one (mass_pos _).le) (uniform_weights R)
    (fun i => hCoset (a₀.1+i.1))
  have he : (fun s => ∑ i : R, (1/mass R) * onSelector W (a₀.1+i.1) f s) =
      onSelector G a₀.1 (fun s => mass U / 2^v * f s) := by
    funext s
    by_cases hs : s-a₀.1 ∈ G
    · obtain ⟨i,hi,huniq⟩ := hRep _ hs
      rw [onSelector_pos _ _ _ _ hs,Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · rw [onSelector_pos _ _ _ _ hi,hmass]
      · intro i' _ hi'
        rw [onSelector_neg _ _ _ _ (fun h' => hi' (huniq i' h')),mul_zero]
    · rw [onSelector_neg _ _ _ _ hs]
      exact Finset.sum_eq_zero fun i _ => by
        rw [onSelector_neg _ _ _ _ (fun h' => hs (hBack _ _ h')),mul_zero]
  rwa [he] at hMix

noncomputable def rowProfile {k v m n d r : ℕ} (word : Vec k → Vec m)
    (P : Vec v →ₗ[F] Residual.Pairs m) (E : Vec n ≃ₗ[F] Vec k × Vec v) (S : State n n d r)
    (j : ℕ) (h : Vec k → F) (s : Vec k) : ℝ :=
  mean fun x : Vec v => mean fun q : Vec d =>
    phase ((S.values q (E.symm (s,x))).getD j 0 +
      dotProduct (S.args q (E.symm (s,x))) (E.symm (s,x)) + (h s + pairPhase P word s x))

theorem row_bound {k v m n d r p : ℕ} (word : Vec k →ₗ[F] Vec m)
    (P : Vec v →ₗ[F] Residual.Pairs m) (hP : Function.Surjective P)
    (E : Vec n ≃ₗ[F] Vec k × Vec v) (S : State n n d r) (j : ℕ) (h : Vec k → F)
    (hc : n+r ≤ d+p) : Majorized (Atom v p word) (rowProfile word P E S j h) := by
  classical
  obtain ⟨H,a,ha,hRow⟩ := row_address S j
  let H' := H.map E.toLinearMap
  let a₀ := E a
  obtain ⟨G,U,t,hd,hDom⟩ := Fibers.affineAddressChart H' a₀
  have hd' : Module.finrank F G + Module.finrank F U = Module.finrank F H :=
    hd.trans (E.finrank_map_eq H)
  let g := resPhase word P (fun s x => E.symm (s,x)) S j h
  have hm (s : Vec k) (x : Vec v) :
      E.symm (s,x)-a ∈ H ↔ s-a₀.1 ∈ G ∧ x-t s ∈ U := by
    rw [← hDom]
    have hh : E (E.symm (s,x)-a) = (s,x)-a₀ := by simp [a₀]
    rw [← hh]
    constructor
    · intro hX
      exact Submodule.mem_map.mpr ⟨_,hX,rfl⟩
    · intro hX
      obtain ⟨z,hz,he⟩ := Submodule.mem_map.mp hX
      rwa [← E.injective he]
  have he : rowProfile word P E S j h = onSelector G a₀.1 (fun s =>
      mass U / 2^v * averageOn U (t s) (g s)) := by
    funext s
    have he' : rowProfile word P E S j h s = onSelector G a₀.1
        (fun s => cutSum U (t s) (g s) / 2^v) s := by
      unfold rowProfile
      simp_rw [hRow,hm]
      unfold mean
      rw [Row.vec_card, Nat.cast_pow]
      norm_cast
      by_cases hs : s-a₀.1 ∈ G
      · rw [onSelector_pos _ _ _ _ hs, cutSum]
        congr 1
        exact Finset.sum_congr rfl fun x _ => by simp [hs,g,resPhase]
      · rw [onSelector_neg _ _ _ _ hs]
        simp [hs]
    rw [he']
    apply congrFun (onSelector_congr _ _ _ _ fun z _ => ?_)
    rw [cutSum_eq]
    ring
  rw [he]
  by_cases ha' : Module.finrank F H < v
  · apply lower_small word G U a₀.1 hd' ha' (by omega)
    intro s
    exact averageOn_abs_le_one U (t s) (g s) (fun x => by unfold g resPhase phase; split <;> norm_num)
  · exact upper_large word P hP E S j h G U a₀ t hd' (by omega) (by omega)

private theorem mean_weighted {α ι : Type*} [Fintype α] [Fintype ι] (w : ι → ℝ) (f : ι → α → ℝ) :
    mean (fun x => ∑ i, w i * f i x) = ∑ i, w i * mean (f i) := by
  unfold mean
  rw [Finset.sum_comm,Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, mul_div_assoc]

noncomputable def wordLinear {k m : ℕ} (A : Fin m → Vec k) : Vec k →ₗ[F] Vec m :=
  LinearMap.pi fun i => (dotProductBilin F F) (A i)

private theorem normalized_score {k m r : ℕ}
    (E : Vec (k+2*m+r) ≃ₗ[F] Vec k × Attain.Data m r)
    (D : PhaseChart.Chart (2*m+r) m r) (word : Vec k → Vec m) (h : Vec k → F)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Vec k) :
    Attain.Score E word h C s =
    mean (fun u : Vec (2*m+r) => mean (fun x : Vec (k+2*m+r) =>
      let y := (PhaseChart.toProduct E D).symm (s,u)
      if C.eval (bits x ++ bits y) =
        RowPort.GateDecode.bit (dotProduct x y + (h s + pairPhase (PhaseChart.pairMap D) word s u))
        then (1:ℝ) else -1)) := by
  classical
  let g (x : Vec (k+2*m+r)) (z : Attain.Data m r) : ℝ :=
    let y := E.symm (s,z)
    if C.eval (bits x ++ bits y) =
      RowPort.GateDecode.bit (dotProduct x y + h s + ∑ i, word s i*z.1 i*z.2.1 i)
      then 1 else -1
  have hg (x : Vec (k+2*m+r)) :
      (∑ b : Vec m, ∑ c : Vec m, ∑ z : Vec r, g x (b,(c,z))) =
        ∑ u : Vec (2*m+r), g x (D u) := by
    rw [show (∑ u : Vec (2*m+r), g x (D u)) = ∑ z : Attain.Data m r, g x z from
      Equiv.sum_comp D.toEquiv (g x)]
    simp only [Attain.Data, Fintype.sum_prod_type]
  have hEval (u : Vec (2*m+r)) (x : Vec (k+2*m+r)) :
      g x (D u) =
        (let y := (PhaseChart.toProduct E D).symm (s,u)
         if C.eval (bits x ++ bits y) =
            RowPort.GateDecode.bit (dotProduct x y + (h s + pairPhase (PhaseChart.pairMap D) word s u))
          then (1:ℝ) else -1) := by
    simp only [g,PhaseChart.toProduct_symm,pairPhase,PhaseChart.pairMap_false,PhaseChart.pairMap_true,add_assoc]
    rfl
  change ((∑ x : Vec (k+2*m+r), ∑ b : Vec m, ∑ c : Vec m, ∑ z : Vec r, g x (b,(c,z))) /
    (2:ℝ)^(k+2*m+r+(2*m+r))) = _
  simp_rw [← hEval, hg]
  unfold mean
  rw [Row.vec_card, pow_add, Finset.sum_comm, ← Finset.sum_div]
  simp_rw [Row.vec_card, Nat.cast_pow]
  norm_cast
  push_cast
  rw [div_div]

set_option maxHeartbeats 1200000 in
theorem upper (k m r : ℕ)
    (E : Vec (k+2*m+r) ≃ₗ[F] Vec k × Attain.Data m r)
    (A : Fin m → Vec k) (h : Vec k → F) (p : ℕ) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, Attain.Fits (n:=k+2*m+r) p C →
      Majorized (Atom (2*m+r) p (fun s i => dotProduct (A i) s))
        (Attain.Score E (fun s i => dotProduct (A i) s) h C) := by
  intro C hC
  let D := PhaseChart.makeChart m r
  let E' := PhaseChart.toProduct E D
  let P := PhaseChart.pairMap D
  let word := wordLinear A
  obtain ⟨L,hL,hW,hR⟩ := circuit_rows (n := k+2*m+r) C hC.1.2
  let prof (t : Row.Leaf (k+2*m+r) (k+2*m+r)) :=
    rowProfile word P E' t.2.2 C.output h
  have hMembers (t : ℝ × Row.Leaf (k+2*m+r) (k+2*m+r)) (ht : t ∈ L) :
      Majorized (Atom (2*m+r) p word) (prof t.2) := by
    have hc := (hL t ht).2
    have hb : C.gates.countP RowPort.CircuitBridge.paid ≤ p := hC.2
    have hh : k+2*m+r+t.2.2.1 ≤ t.2.1+p := by omega
    exact row_bound word P (PhaseChart.pairMap_surj D) E' t.2.2.2 C.output h hh
  have hBound := mix_list L prof (fun t ht => (hL t ht).1) hW hMembers
  have he : ∀ s, Attain.Score E word h C s = Row.mixture L (fun t => prof t s) := by
    intro s
    rw [normalized_score E D word h C s]
    change mean (fun u : Vec (2*m+r) => mean (fun x : Vec (k+2*m+r) =>
      if C.eval (bits x ++ bits (E'.symm (s,u))) =
        RowPort.GateDecode.bit (dotProduct x (E'.symm (s,u)) + (h s + pairPhase P word s u))
        then (1:ℝ) else -1)) = _
    simp_rw [hR, list_mixture_eq_sum]
    rw [mean_weighted]
    rfl
  change Majorized (Atom (2*m+r) p word) (Attain.Score E word h C)
  rwa [funext he]

end PEqualNP.Outside.L_meta_32579_aux.Upper


theorem PEqualNP.Outside.L_meta_32579 : ∀ k m r : ℕ,
  let n := k+2*m+r
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (width : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack width C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (width : ℕ) (u : Fin width → F) => List.ofFn (fun j : Fin width => decide (u j = 1))
  let V := Fin n → F
  let S := Fin k → F
  let D := Fin m → F
  let Z := Fin r → F
  let base := 2*m+r
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S) (h : S → F),
    let word := fun (s : S) (i : Fin m) => dotProduct (A i) s
    let score := fun (C : Circ) (s : S) =>
      (∑ x : V, ∑ b : D, ∑ c : D, ∑ z : Z,
        let y := e.symm (s,(b,(c,z)))
        let v := dotProduct x y + h s + ∑ i, word s i * b i * c i
        if C.eval (bits n x ++ bits n y) = decide (v = 1) then (1 : ℝ) else -1) / 2^(n+base)
    let fits := fun (p : ℕ) (C : Circ) => legal (2*n) C ∧ cost C ≤ p
    let quad := fun (f : S → F) => ∃ (o : F) (l : S) (M : Fin k → Fin k → F),
      ∀ s, f s = o + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j
    ∀ p : ℕ,
      let atom := fun (v : S → ℝ) =>
        if p < base then ∃ a : S, ∀ s, v s = if s = a then 1 / 2^(base-p) else 0
        else ∃ (a : S) (W : Submodule F S) (J : Finset (Fin m)) (b : D),
          base + Module.finrank F W + J.card ≤ p ∧ ∀ s,
          let wt := ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ word s i ≠ b i)).card
          v s = @ite ℝ (s-a ∈ W) (Classical.propDecidable _) (1 / 2^wt) 0
      (∀ C : Circ, fits p C →
        ∃ (N : ℕ) (v : Fin N → S → ℝ) (w : Fin N → ℝ),
          (∀ i, atom (v i) ∧ 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
          ∀ s, |score C s| ≤ ∑ i, w i * v i s) ∧
      (∀ v : S → ℝ, atom v → ∀ f : S → F, quad f →
        ∃ C : Circ, fits p C ∧ ∀ s, score C s = (if h s = f s then 1 else -1) * v s) := by
  intro k m r
  dsimp only
  intro e A h p
  exact ⟨PEqualNP.Outside.L_meta_32579_aux.Upper.upper k m r e A h p,
    PEqualNP.Outside.L_meta_32579_aux.Attain.attain k m r e A h p⟩
