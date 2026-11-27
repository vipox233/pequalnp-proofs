import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.ZMod.Basic

namespace PEqualNP.Outside.L_lib_789_aux

def criterion {k m : ℕ} (v : Fin m → Fin k → ZMod 2)
    (P : Finset (Fin k)) (S : Finset (Fin m)) : Prop :=
  ∀ (w : S → ZMod 2) (t : ZMod 2),
    (∀ i : Fin k, i ∉ P → (∑ j : S, w j * v j.val i) = t) → w = 0 ∧ t = 0

private theorem no_relation_iff {k : ℕ} {R : Type} [Fintype R]
    (M : Matrix R (Fin k) (ZMod 2)) :
    (∀ z, M.vecMul z = 0 → z = 0) ↔ Function.Surjective M.mulVec := by
  constructor
  · intro h
    apply LinearIndependent.mulVec_surjective
    apply Matrix.vecMul_injective_iff.mp
    intro z w he
    apply sub_eq_zero.mp
    apply h
    rw [Matrix.sub_vecMul]
    exact sub_eq_zero.mpr he
  · intro hs
    have hi : LinearIndependent (ZMod 2) M.row := by
      apply linearIndependent_iff_card_eq_finrank_span.mpr
      change Fintype.card R = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range M.row))
      rw [← M.rank_eq_finrank_span_row]
      exact (Matrix.mulVec_surjective_iff_rank_eq_card.mp hs).symm
    intro z hz
    exact (Matrix.vecMul_injective_iff.mpr hi) (by simpa using hz)

private theorem uniform_iff {k : ℕ} {R : Type} [Fintype R]
    (M : Matrix R (Fin k) (ZMod 2)) :
    Function.Surjective M.mulVec ↔
      ∀ b : R → ZMod 2, 2^(Fintype.card R) *
        (Finset.univ.filter (fun x : Fin k → ZMod 2 => M.mulVec x = b)).card = 2^k := by
  constructor
  · intro hs b
    obtain ⟨x,rfl⟩ := hs b
    let f := M.mulVecLin
    let _ : Fintype (LinearMap.ker f) := Fintype.ofFinite _
    have hd := f.finrank_range_add_finrank_ker
    change M.rank + Module.finrank (ZMod 2) (LinearMap.ker f) = _ at hd
    rw [Matrix.mulVec_surjective_iff_rank_eq_card.mp hs,Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at hd
    have e : {y : Fin k → ZMod 2 // M.mulVec y = M.mulVec x} ≃ (LinearMap.ker f) :=
      f.toAddMonoidHom.fiberEquivKer x
    rw [← Fintype.card_subtype, Fintype.card_congr e,
      Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker f), ZMod.card, ← pow_add, hd]
  · intro h b
    have hc := h b
    have hp : 0 < (Finset.univ.filter (fun x : Fin k → ZMod 2 => M.mulVec x = b)).card := by
      by_contra! hn
      rw [Nat.eq_zero_of_le_zero hn,mul_zero] at hc
      exact (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2))) hc.symm
    obtain ⟨x,hx⟩ := Finset.card_pos.mp hp
    exact ⟨x,(Finset.mem_filter.mp hx).2⟩

private def probes {k m : ℕ} (v : Fin m → Fin k → ZMod 2)
    (P : Finset (Fin k)) (S : Finset (Fin m)) :
    Matrix (P ⊕ (Unit ⊕ S)) (Fin k) (ZMod 2) :=
  Sum.elim (fun p i => if i = p.val then 1 else 0)
    (Sum.elim (fun _ _ => 1) (fun j i => v j.val i))

private theorem pin_sum {k : ℕ} (P : Finset (Fin k)) (f : P → ZMod 2) (i : Fin k) :
    (∑ p : P, f p * (if i = p.val then 1 else 0)) =
      (if h : i ∈ P then f ⟨i,h⟩ else 0) := by
  by_cases hi : i ∈ P
  · rw [dite_eq_left hi, Finset.sum_eq_single ⟨i,hi⟩]
    · simp
    · intro b _ he
      have hn : i ≠ b.val := fun h => he (Subtype.ext h.symm)
      simp [hn]
    · simp
  · rw [dite_eq_right hi]
    apply Finset.sum_eq_zero
    intro p _
    have hn : i ≠ p.val := fun h => hi (h ▸ p.property)
    simp [hn]

private theorem relation_value {k m : ℕ} (v : Fin m → Fin k → ZMod 2)
    (P : Finset (Fin k)) (S : Finset (Fin m)) (z : P ⊕ (Unit ⊕ S) → ZMod 2) (i : Fin k) :
    (probes v P S).vecMul z i =
      (if h : i ∈ P then z (.inl ⟨i,h⟩) else 0) + z (.inr (.inl ())) +
      ∑ j : S, z (.inr (.inr j)) * v j.val i := by
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, probes, Sum.elim_inl,
    Sum.elim_inr, Fintype.sum_unique, mul_one, pin_sum, add_assoc]

private theorem criterion_relation {k m : ℕ} (v : Fin m → Fin k → ZMod 2)
    (P : Finset (Fin k)) (S : Finset (Fin m)) :
    criterion v P S ↔ ∀ z, (probes v P S).vecMul z = 0 → z = 0 := by
  constructor
  · intro hc z hz
    have total (i : Fin k) := (relation_value v P S z i).symm.trans (congrFun hz i)
    let w : S → ZMod 2 := fun j => z (.inr (.inr j))
    let t := z (.inr (.inl ()))
    obtain ⟨hw, ht⟩ := hc w (-t) (by
      intro i hi
      have he := total i
      simp only [dite_eq_right hi, zero_add, Pi.zero_apply] at he
      exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans he))
    have parzero : z (.inr (.inl ())) = 0 := neg_eq_zero.mp ht
    have szero (j : S) : z (.inr (.inr j)) = 0 := congrFun hw j
    funext r
    rcases r with p | u | j
    · have he := total p.val
      simpa [p.property,parzero,szero] using he
    · cases u
      exact parzero
    · exact szero j
  · intro hr w t h
    let z : P ⊕ (Unit ⊕ S) → ZMod 2 := Sum.elim
      (fun p => t - ∑ j : S, w j * v j.val p.val) (Sum.elim (fun _ => -t) w)
    have hz := hr z (by
      funext i
      rw [relation_value]
      by_cases hi : i ∈ P
      · simp only [dite_eq_left hi,z,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply]
        abel
      · simp only [dite_eq_right hi,z,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,zero_add,h i hi,neg_add_cancel])
    refine ⟨funext (fun j => congrFun hz (.inr (.inr j))),?_⟩
    exact neg_eq_zero.mp (congrFun hz (.inr (.inl ())))

private def answers {k m : ℕ} (P : Finset (Fin k)) (S : Finset (Fin m))
    (pins : Fin k → ZMod 2) (par : ZMod 2) (target : Fin m → ZMod 2) :
    P ⊕ (Unit ⊕ S) → ZMod 2 :=
  Sum.elim (fun p => pins p.val) (Sum.elim (fun _ => par) (fun j => target j.val))

private theorem probe_answers {k m : ℕ} (v : Fin m → Fin k → ZMod 2)
    (P : Finset (Fin k)) (S : Finset (Fin m)) (pins : Fin k → ZMod 2)
    (par : ZMod 2) (target : Fin m → ZMod 2) (x : Fin k → ZMod 2) :
    (probes v P S).mulVec x = answers P S pins par target ↔
      (∀ i ∈ P, x i = pins i) ∧ (∑ i, x i) = par ∧
        (∀ j ∈ S, (∑ i, x i * v j i) = target j) := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro i hi
      simpa [Matrix.mulVec,dotProduct,probes,answers,ite_mul] using congrFun h (.inl ⟨i,hi⟩)
    · simpa [Matrix.mulVec,dotProduct,probes,answers] using congrFun h (.inr (.inl ()))
    · intro j hj
      simpa [Matrix.mulVec,dotProduct,probes,answers,mul_comm] using congrFun h (.inr (.inr ⟨j,hj⟩))
  · rintro ⟨hp,hpar,ht⟩
    funext r
    rcases r with p | u | j
    · simpa [Matrix.mulVec,dotProduct,probes,answers,ite_mul] using hp p.val p.property
    · simpa [Matrix.mulVec,dotProduct,probes,answers] using hpar
    · simpa [Matrix.mulVec,dotProduct,probes,answers,mul_comm] using ht j.val j.property

theorem criterion_uniform {k m : ℕ} (v : Fin m → Fin k → ZMod 2)
    (P : Finset (Fin k)) (S : Finset (Fin m)) :
    criterion v P S ↔ ∀ (pins : Fin k → ZMod 2) (par : ZMod 2) (target : Fin m → ZMod 2),
      2^(P.card+1+S.card) * ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun x =>
            (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par ∧
            (∀ j ∈ S, (∑ i : Fin k, x i * v j i) = target j))).card = 2^k := by
  rw [criterion_relation, no_relation_iff, uniform_iff]
  have hcard : Fintype.card (P ⊕ (Unit ⊕ S)) = P.card+1+S.card := by simp [Nat.add_assoc]
  rw [hcard]
  constructor
  · intro h pins par target
    simpa only [probe_answers] using h (answers P S pins par target)
  · intro h b
    let pins (i : Fin k) := if hi : i ∈ P then b (.inl ⟨i,hi⟩) else 0
    let target (j : Fin m) := if hj : j ∈ S then b (.inr (.inr ⟨j,hj⟩)) else 0
    let par := b (.inr (.inl ()))
    have he : b = answers P S pins par target := by
      funext r
      rcases r with p | u | j
      · simp [answers,pins]
      · cases u; rfl
      · simp [answers,target]
    rw [he]
    simpa only [probe_answers] using h pins par target

private theorem bit_cases (x : ZMod 2) : x = 0 ∨ x = 1 :=
  (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) x

private theorem outside_pin {k d : ℕ} (P : Finset (Fin k)) (hp : P.card ≤ d) (hk : d < k) :
    ∃ i, i ∉ P := by
  classical
  by_contra! hall
  have e : P = Finset.univ := Finset.eq_univ_of_forall hall
  simp [e] at hp
  omega

private theorem weight_criterion {k m d g : ℕ} (hk : d < k) (v : Fin m → Fin k → ZMod 2) :
    (∀ S : Finset (Fin m), 0 < S.card → S.card ≤ g →
      let w := ((Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S, v j i) = 1)).card
      d < w ∧ w+d < k) ↔
    ∀ (P : Finset (Fin k)), P.card ≤ d → ∀ (S : Finset (Fin m)), S.card ≤ g → criterion v P S := by
  classical
  constructor
  · intro margins P hp S hs w t hc
    let coeff (j : Fin m) : ZMod 2 := if h : j ∈ S then w ⟨j,h⟩ else 0
    let U := S.filter (fun j => coeff j = 1)
    have sums (i : Fin k) : (∑ j ∈ U, v j i) = ∑ j : S, w j * v j.val i := by
      calc
        _ = ∑ j ∈ S, if coeff j = 1 then v j i else 0 := Finset.sum_filter _ _
        _ = ∑ j ∈ S, coeff j * v j i := by
          apply Finset.sum_congr rfl
          intro j _
          rcases bit_cases (coeff j) with h|h <;> simp [h]
        _ = ∑ j : S, coeff j.val * v j.val i := Finset.sum_subtype S (fun _ => Iff.rfl) _
        _ = _ := by apply Finset.sum_congr rfl; intro j _; simp [coeff,j.property]
    by_cases he : U.Nonempty
    · exfalso
      have hu := margins U (Finset.card_pos.mpr he) ((Finset.card_filter_le S _).trans hs)
      let ones := (Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ U, v j i) = 1)
      change d < ones.card ∧ ones.card + d < k at hu
      have card : ones.card + onesᶜ.card = k := by simp
      rcases bit_cases t with ht|ht
      · have sub : ones ⊆ P := by
          intro i hi
          by_contra h
          have eq := (sums i).trans (hc i h)
          have mem := (Finset.mem_filter.mp hi).2
          rw [eq,ht] at mem
          exact zero_ne_one mem
        have h := Finset.card_le_card sub
        omega
      · have sub : onesᶜ ⊆ P := by
          intro i hi
          by_contra h
          apply (Finset.mem_compl.mp hi)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (sums i).trans ((hc i h).trans ht)⟩
        have h := Finset.card_le_card sub
        omega
    · have wz : w = 0 := by
        funext j
        rcases bit_cases (w j) with h|h
        · exact h
        · exact False.elim (he ⟨j.val,Finset.mem_filter.mpr ⟨j.property,by simpa [coeff,j.property] using h⟩⟩)
      obtain ⟨i,hi⟩ := outside_pin P hp hk
      exact ⟨wz, by simpa [wz] using (hc i hi).symm⟩
  · intro crit S hpos hs
    let ones := (Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S, v j i) = 1)
    change d < ones.card ∧ ones.card+d < k
    have card : ones.card + onesᶜ.card = k := by simp
    have eqsum (i : Fin k) : (∑ j : S, (1 : ZMod 2) * v j.val i) = ∑ j ∈ S, v j i := by
      simp only [one_mul]
      symm
      exact Finset.sum_subtype S (fun _ => Iff.rfl) _
    constructor
    · by_contra! h
      have bad := crit ones h S hs (fun _ => 1) 0 (by
        intro i hi
        rw [eqsum]
        rcases bit_cases (∑ j ∈ S, v j i) with h0|h1
        · exact h0
        · exact False.elim (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1⟩)))
      obtain ⟨j,hj⟩ := Finset.card_pos.mp hpos
      exact one_ne_zero (congrFun bad.1 ⟨j,hj⟩)
    · by_contra! h
      have bad := crit onesᶜ (by omega) S hs (fun _ => 1) 1 (by
        intro i hi
        exact (eqsum i).trans ((Finset.mem_filter.mp (Finset.notMem_compl.mp hi)).2))
      exact one_ne_zero bad.2
end PEqualNP.Outside.L_lib_789_aux

theorem PEqualNP.Outside.L_lib_789 : (∀ (k m d g : ℕ), d < k →
  let F := ZMod 2
  let V := Fin k → F
  ∀ v : Fin m → V,
    (∀ S : Finset (Fin m), 0 < S.card → S.card ≤ g →
      let w := ((Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S, v j i) = 1)).card
      d < w ∧ w+d < k) ↔
    ∀ (P : Finset (Fin k)), P.card ≤ d →
      ∀ (pins : V) (par : F) (S : Finset (Fin m)), S.card ≤ g → ∀ target : Fin m → F,
        2^(P.card+1+S.card) *
          ((Finset.univ : Finset V).filter (fun x =>
            (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par ∧
            (∀ j ∈ S, (∑ i : Fin k, x i * v j i) = target j))).card = 2^k) := by
  intro k m d g hd
  dsimp only
  intro v
  rw [PEqualNP.Outside.L_lib_789_aux.weight_criterion hd v]
  constructor
  · intro h P hp pins par S hs target
    exact (PEqualNP.Outside.L_lib_789_aux.criterion_uniform v P S).mp (h P hp S hs) pins par target
  · intro h P hp S hs
    apply (PEqualNP.Outside.L_lib_789_aux.criterion_uniform v P S).mpr
    exact fun pins par target => h P hp pins par S hs target
