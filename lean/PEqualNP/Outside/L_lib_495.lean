import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_495

open MvPolynomial PEqualNP.ProofComplexity

abbrev P (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

noncomputable def baseF (n D : ℕ) (F : Set (P n)) : Submodule (ZMod 2) (P n) :=
  Submodule.span (ZMod 2) {p : P n | p ∈ F ∧ p.totalDegree ≤ D}

noncomputable def stepF (n D : ℕ) (W : Submodule (ZMod 2) (P n)) : Submodule (ZMod 2) (P n) :=
  W ⊔ Submodule.span (ZMod 2) {q : P n | ∃ i : Fin n, ∃ p ∈ W, q = MvPolynomial.X i * p ∧ q.totalDegree ≤ D}

noncomputable def Rd (n D : ℕ) : Submodule (ZMod 2) (P n) := restrictTotalDegree (Fin n) (ZMod 2) D

lemma le_step (n D : ℕ) (W : Submodule (ZMod 2) (P n)) : W ≤ stepF n D W := le_sup_left

lemma step_le_Rd (n D : ℕ) (W : Submodule (ZMod 2) (P n)) (h : W ≤ Rd n D) : stepF n D W ≤ Rd n D := by
  refine sup_le h (Submodule.span_le.mpr ?_)
  rintro q ⟨i, p, -, -, hq⟩
  exact (mem_restrictTotalDegree (Fin n) D q).mpr hq

lemma base_le_Rd (n D : ℕ) (F : Set (P n)) : baseF n D F ≤ Rd n D := by
  refine Submodule.span_le.mpr ?_
  rintro q ⟨-, hq⟩
  exact (mem_restrictTotalDegree (Fin n) D q).mpr hq

lemma iter_le_Rd (n D : ℕ) (F : Set (P n)) (m : ℕ) : (stepF n D)^[m] (baseF n D F) ≤ Rd n D := by
  induction m with
  | zero => exact base_le_Rd n D F
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact step_le_Rd n D _ ih

noncomputable def emb (n D : ℕ) (f : {s : Fin n →₀ ℕ | (s.sum fun _ e => e) ≤ D}) : Option (Fin n) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun o => Option.elim o (D - (f.1.sum fun _ e => e)) (fun i => f.1 i))

lemma emb_mem (n D : ℕ) (f : {s : Fin n →₀ ℕ | (s.sum fun _ e => e) ≤ D}) :
    emb n D f ∈ (Finset.univ : Finset (Option (Fin n))).finsuppAntidiag D := by
  rw [Finset.mem_finsuppAntidiag]
  refine ⟨?_, Finset.subset_univ _⟩
  have h1 : (f.1.sum fun _ e => e) = ∑ i, f.1 i := Finsupp.sum_fintype _ _ (fun _ => rfl)
  have h2 : (f.1.sum fun _ e => e) ≤ D := f.2
  rw [Fintype.sum_option]
  simp only [emb, Finsupp.equivFunOnFinite_symm_apply_apply, Option.elim]
  omega

lemma emb_inj (n D : ℕ) : Function.Injective
    (fun f : {s : Fin n →₀ ℕ | (s.sum fun _ e => e) ≤ D} =>
      (⟨emb n D f, emb_mem n D f⟩ : ((Finset.univ : Finset (Option (Fin n))).finsuppAntidiag D))) := by
  intro f g h
  have h' : emb n D f = emb n D g := congrArg Subtype.val h
  apply Subtype.ext
  ext i
  have := DFunLike.congr_fun h' (some i)
  simpa [emb] using this

lemma finrank_Rd (n D : ℕ) : Module.finrank (ZMod 2) (Rd n D) ≤ (n + D).choose n := by
  have hb := Module.finrank_eq_nat_card_basis
    (basisRestrictSupport (ZMod 2) {s : Fin n →₀ ℕ | (s.sum fun _ e => e) ≤ D})
  have hb' : Module.finrank (ZMod 2) (Rd n D) = Nat.card {s : Fin n →₀ ℕ | (s.sum fun _ e => e) ≤ D} := hb
  rw [hb']
  have hc := Nat.card_le_card_of_injective _ (emb_inj n D)
  refine le_trans hc ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_option, Fintype.card_fin]
  rw [show n + 1 + D - 1 = D + n by omega, Nat.choose_symm_add, Nat.add_comm]

lemma stab (n D N : ℕ) (F : Set (P n)) (hN : Module.finrank (ZMod 2) (Rd n D) ≤ N) :
    stepF n D ((stepF n D)^[N] (baseF n D F)) = (stepF n D)^[N] (baseF n D F) := by
  have : FiniteDimensional (ZMod 2) (Rd n D) := by
    unfold Rd
    infer_instance
  by_contra hne
  have hstrict : ∀ m, m ≤ N → (stepF n D)^[m] (baseF n D F) < (stepF n D)^[m + 1] (baseF n D F) := by
    intro m hm
    rw [Function.iterate_succ_apply']
    refine lt_of_le_of_ne (le_step n D _) ?_
    intro heq
    apply hne
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_comm, Function.iterate_add_apply]
    have hfix : (stepF n D)^[k] ((stepF n D)^[m] (baseF n D F)) = (stepF n D)^[m] (baseF n D F) :=
      Function.iterate_fixed heq.symm k
    rw [hfix]
    exact heq.symm
  have hgrow : ∀ m, m ≤ N + 1 → m ≤ Module.finrank (ZMod 2) ((stepF n D)^[m] (baseF n D F)) := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have : FiniteDimensional (ZMod 2) ((stepF n D)^[m + 1] (baseF n D F)) :=
        Submodule.finiteDimensional_of_le (iter_le_Rd n D F (m + 1))
      have h2 := Submodule.finrank_lt_finrank_of_lt (hstrict m (by omega))
      omega
  have h3 := hgrow (N + 1) le_rfl
  have h4 := Submodule.finrank_mono (iter_le_Rd n D F (N + 1))
  omega

lemma der_smul (n D : ℕ) (F : Set (P n)) (c : ZMod 2) (p : P n) (hp : PCDerivable F D p) :
    PCDerivable F D (c • p) := by
  have hc : c = 0 ∨ c = 1 := by
    revert c
    decide
  rcases hc with rfl | rfl
  · rw [zero_smul]
    exact PCDerivable.zero
  · rw [one_smul]
    exact hp

def Der (n D : ℕ) (F : Set (P n)) : Submodule (ZMod 2) (P n) :=
  { carrier := {p | PCDerivable F D p}, zero_mem' := PCDerivable.zero,
    smul_mem' := fun c _ hp => der_smul n D F c _ hp, add_mem' := fun hp hq => PCDerivable.add hp hq }

lemma iter_le_Der (n D : ℕ) (F : Set (P n)) (m : ℕ) : (stepF n D)^[m] (baseF n D F) ≤ Der n D F := by
  induction m with
  | zero =>
    refine Submodule.span_le.mpr ?_
    rintro q ⟨hq, hd⟩
    exact PCDerivable.ax hq hd
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    refine sup_le ih (Submodule.span_le.mpr ?_)
    rintro q ⟨i, p, hp, rfl, hd⟩
    exact PCDerivable.mulX i (ih hp) hd

lemma base_le_iter (n D : ℕ) (F : Set (P n)) (m : ℕ) : baseF n D F ≤ (stepF n D)^[m] (baseF n D F) := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans ih (le_step n D _)

theorem main (n D : ℕ) (F : Set (P n)) (p : P n) :
    PCDerivable F D p ↔ p ∈ (stepF n D)^[(n + D).choose n] (baseF n D F) := by
  constructor
  · intro h
    induction h with
    | ax hp hdeg => exact base_le_iter n D F _ (Submodule.subset_span ⟨hp, hdeg⟩)
    | zero => exact Submodule.zero_mem _
    | add _ _ ih1 ih2 => exact Submodule.add_mem _ ih1 ih2
    | mulX j _ hdeg ih =>
      rw [← stab n D _ F (finrank_Rd n D)]
      exact (le_sup_right : _ ≤ stepF n D _) (Submodule.subset_span ⟨j, _, ih, rfl, hdeg⟩)
  · intro h
    exact iter_le_Der n D F _ h

end PEqualNP.Outside.L_lib_495

theorem PEqualNP.Outside.L_lib_495 : ∀ (n D : ℕ), let P := MvPolynomial (Fin n) (ZMod 2)
  ∀ F : Set P,
    let base := Submodule.span (ZMod 2) {p : P | p ∈ F ∧ p.totalDegree ≤ D}
    let step := fun W : Submodule (ZMod 2) P =>
      W ⊔ Submodule.span (ZMod 2) {q : P | ∃ i : Fin n, ∃ p ∈ W,
                q = MvPolynomial.X i * p ∧ q.totalDegree ≤ D}
    ∀ p : P, PEqualNP.ProofComplexity.PCDerivable F D p ↔ p ∈ (step^[(n+D).choose n]) base := by
  intro n D P F base step p
  exact PEqualNP.Outside.L_lib_495.main n D F p
