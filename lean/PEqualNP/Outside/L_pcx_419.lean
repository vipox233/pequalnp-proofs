import PEqualNP.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_419_aux

section Algebra

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

private noncomputable def homogenize (A : AffineSubspace K V) : Submodule K (V × K) := by
  classical
  exact if hn : (A : Set V).Nonempty then
    A.direction.comap (LinearMap.fst K V K - (LinearMap.snd K V K).smulRight hn.choose)
  else ⊥

private theorem homogenize_slice (A : AffineSubspace K V) (x : V) :
    (x, (1 : K)) ∈ homogenize A ↔ x ∈ A := by
  classical
  unfold homogenize
  split
  · rename_i hn
    have base := hn.choose_spec
    change x - (1 : K) • hn.choose ∈ A.direction ↔ x ∈ A
    simpa using (A.vsub_right_mem_direction_iff_mem base x)
  · rename_i hn
    constructor
    · intro h
      have h' : (x, (1 : K)) = 0 := (Submodule.mem_bot K).1 h
      exact (one_ne_zero (congrArg Prod.snd h')).elim
    · exact fun h => (hn ⟨x,h⟩).elim

private theorem mem_intersection {ι : Type} (S : Finset ι)
    (W : ι → Submodule K V) (x : V) :
    x ∈ S.inf W ↔ ∀ i ∈ S, x ∈ W i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i T hi ih => simp [Finset.inf_insert, ih]

private theorem annihilator_sum {ι : Type} (S : Finset ι)
    (W : ι → Submodule K V) (f : V →ₗ[K] K) (hf : f ∈ (S.inf W).dualAnnihilator) :
    ∃ g : ι → V →ₗ[K] K, (∀ i ∈ S, g i ∈ (W i).dualAnnihilator) ∧
      (∑ i ∈ S, g i) = f := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty =>
    have hzero : f = 0 := by simpa using hf
    exact ⟨fun _ => 0, by simp, by simp [hzero]⟩
  | insert i T hi ih =>
    rw [Finset.inf_insert, Subspace.dualAnnihilator_inf_eq] at hf
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
    obtain ⟨g,hg,sum⟩ := ih b hb
    refine ⟨Function.update g i a, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa using ha
      · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] using hg j hj
    · rw [Finset.sum_insert hi, Function.update_self, ← sum]
      congr 1
      exact Finset.sum_congr rfl fun j hj => Function.update_of_ne
        (ne_of_mem_of_not_mem hj hi) a g

theorem affineCertificate {ι : Type} (P : AffineSubspace K V) (bad : ι → AffineSubspace K V)
    (S : Finset ι) (obstructed : ∀ x ∈ P, ∃ i ∈ S, x ∉ bad i) :
    ∃ (lin : ι → V →ₗ[K] K) (bias : ι → K),
      (∀ i ∈ S, ∀ x ∈ P, x ∈ bad i → lin i x + bias i = 0) ∧
      (∀ x ∈ P, (∑ i ∈ S, (lin i x + bias i)) = 1) := by
  classical
  let W := fun i => homogenize (bad i)
  let Q := homogenize P
  let second := LinearMap.snd K V K
  have stopper : second ∈ (Q ⊓ S.inf W).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    rintro ⟨x,t⟩ ht
    change t = 0
    by_contra ht0
    have ho : t⁻¹ • (x,t) ∈ Q ⊓ S.inf W := (Q ⊓ S.inf W).smul_mem _ ht
    have hscale : t⁻¹ • (x,t) = (t⁻¹ • x, (1 : K)) := by
      ext <;> simp [smul_eq_mul, ht0]
    rw [hscale] at ho
    obtain ⟨hp,hs⟩ := Submodule.mem_inf.mp ho
    obtain ⟨i,hi,hh⟩ := obstructed _ ((homogenize_slice _ _).1 hp)
    exact hh ((homogenize_slice _ _).1 ((mem_intersection _ _ _).1 hs i hi))
  rw [Subspace.dualAnnihilator_inf_eq] at stopper
  obtain ⟨a, ha, b, hb, ab⟩ := Submodule.mem_sup.mp stopper
  obtain ⟨g,hg,total⟩ := annihilator_sum S W b hb
  let lin := fun i => (g i).comp (LinearMap.inl K V K)
  let bias := fun i => g i (0,1)
  have eval (i : ι) (x : V) : lin i x + bias i = g i (x,1) := by
    change g i (x,0) + g i (0,1) = _
    rw [← map_add]
    simp
  refine ⟨lin,bias,?_,?_⟩
  · intro i hi x _ hx
    rw [eval]
    exact (Submodule.mem_dualAnnihilator _).1 (hg i hi) _ ((homogenize_slice _ _).2 hx)
  · intro x hx
    have zero := (Submodule.mem_dualAnnihilator _).1 ha (x,1) ((homogenize_slice _ _).2 hx)
    simp_rw [eval]
    have hb' : (∑ i ∈ S, g i) (x,1) = b (x,1) := congrArg (fun z : V × K →ₗ[K] K => z (x,1)) total
    rw [LinearMap.sum_apply] at hb'
    rw [hb']
    have h := congrArg (fun z : V × K →ₗ[K] K => z (x,1)) ab
    simpa [zero, second] using h

end Algebra

section Rank

variable {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W] [DecidableEq ι]

def NoCommon (P : AffineSubspace K V) (bad : ι → AffineSubspace K V) (S : Finset ι) : Prop :=
  ∀ x ∈ P, ∃ i ∈ S, x ∉ bad i

private theorem mem_flats (S : Finset ι) (bad : ι → AffineSubspace K V) (x : V) :
    x ∈ S.inf bad ↔ ∀ i ∈ S, x ∈ bad i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i T hi ih => simp [Finset.inf_insert, AffineSubspace.mem_inf_iff, ih]

private theorem blockUnion (cost : ι → ℕ) (S T : Finset ι) :
    (∑ i ∈ S ∪ T, cost i) ≤ (∑ i ∈ S, cost i) + ∑ i ∈ T, cost i := by
  classical
  have := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := cost)
  omega

private theorem blockRankAux (P : AffineSubspace K V) (bad : ι → AffineSubspace K V)
    (f : V →ᵃ[K] W) (cost : ι → ℕ) (cap : ℕ) (good : ι → Prop)
    (fibers : ∀ x ∈ P, ∃ S : Finset ι,
      (∑ i ∈ S, cost i) ≤ cap ∧ (∀ i ∈ S, good i) ∧
      (∀ z ∈ P, f z = f x → ∃ i ∈ S, z ∉ bad i)) :
    ∀ d (Q : AffineSubspace K V), Q ≤ P →
      Module.finrank K (Q.map f).direction + 1 ≤ d →
      ∃ S : Finset ι, (∑ i ∈ S, cost i) ≤ d * cap ∧
        (∀ i ∈ S, good i) ∧ NoCommon Q bad S := by
  classical
  intro d
  induction d with
  | zero => intro Q _ h; omega
  | succ d ih =>
    intro Q hQP bound
    by_cases empty : ¬ (Q : Set V).Nonempty
    · exact ⟨∅, by simp, by simp, fun x hx => (empty ⟨x,hx⟩).elim⟩
    obtain ⟨x,hx⟩ := not_not.mp empty
    obtain ⟨A,hA,gA,avoid⟩ := fibers x (hQP hx)
    let R := Q ⊓ A.inf bad
    have spent (z : V) (hz : z ∈ Q) : (∃ i ∈ A, z ∉ bad i) ∨ z ∈ R := by
      by_cases h : ∃ i ∈ A, z ∉ bad i
      · exact Or.inl h
      · right
        exact ⟨hz,(mem_flats _ _ _).2 (by push Not at h; exact h)⟩
    by_cases hR : ¬ (R : Set V).Nonempty
    · refine ⟨A, ?_, gA, fun z hz => (spent z hz).resolve_right (fun hr => hR ⟨z,hr⟩)⟩
      rw [Nat.succ_mul]
      omega
    have mapR : (R.map f : Set W).Nonempty := by
      obtain ⟨z,hz⟩ := not_not.mp hR
      exact ⟨f z, ⟨z,hz,rfl⟩⟩
    have maplt : R.map f < Q.map f := by
      refine lt_of_le_of_ne (AffineSubspace.map_mono f inf_le_left) ?_
      intro eq
      have inside : f x ∈ R.map f := eq ▸ (show f x ∈ Q.map f from ⟨x,hx,rfl⟩)
      obtain ⟨z,hz,eqout⟩ := inside
      obtain ⟨i,hi,notBad⟩ := avoid z (hQP hz.1) eqout
      exact notBad ((mem_flats _ _ _).1 hz.2 i hi)
    have ltRank := Submodule.finrank_lt_finrank_of_lt
      (AffineSubspace.direction_lt_of_nonempty maplt mapR)
    obtain ⟨B,hB,gB,blockB⟩ := ih R (inf_le_left.trans hQP) (by omega)
    refine ⟨A ∪ B, ?_, ?_, ?_⟩
    · have hu := blockUnion cost A B
      rw [Nat.succ_mul]
      omega
    · intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact gA i hi
      · exact gB i hi
    · intro z hz
      rcases spent z hz with before | after
      · obtain ⟨i,hi,miss⟩ := before
        exact ⟨i,Finset.mem_union_left _ hi,miss⟩
      · obtain ⟨i,hi,miss⟩ := blockB z after
        exact ⟨i,Finset.mem_union_right _ hi,miss⟩

theorem rankBatch (P : AffineSubspace K V) (bad : ι → AffineSubspace K V)
    (f : V →ᵃ[K] W) (cost : ι → ℕ) (cap : ℕ) (good : ι → Prop)
    (fibers : ∀ x ∈ P, ∃ S : Finset ι,
      (∑ i ∈ S, cost i) ≤ cap ∧ (∀ i ∈ S, good i) ∧
      (∀ z ∈ P, f z = f x → ∃ i ∈ S, z ∉ bad i)) :
    ∃ S : Finset ι, (∑ i ∈ S, cost i) ≤ (Module.finrank K W+1)*cap ∧
      (∀ i ∈ S, good i) ∧ NoCommon P bad S := by
  apply blockRankAux P bad f cost cap good fibers _ P le_rfl
  exact Nat.add_le_add_right (Submodule.finrank_le _) 1

end Rank

end PEqualNP.Outside.L_pcx_419_aux

namespace PEqualNP.Outside.L_pcx_419_aux

section Protocol

variable {V K ι : Type} [Field K] [AddCommGroup V] [Module K V]

abbrev H (K : Type) := List (List K)
abbrev Ask (K V : Type) [Field K] [AddCommGroup V] [Module K V] :=
  H K → ℕ → V →ₗ[K] K

def step (width : ℕ → ℕ) (ask : Ask K V) (offset : H K → ℕ → K) (x : V) (history : H K) : H K :=
  history ++ [List.ofFn (fun i : Fin (width history.length) => ask history i.val x + offset history i.val)]

def run (width : ℕ → ℕ) (ask : Ask K V) (offset : H K → ℕ → K) (x : V) : ℕ → H K → H K
  | 0, h => h
  | n+1, h => run width ask offset x n (step width ask offset x h)

theorem run_length (width : ℕ → ℕ) (ask : Ask K V) (offset) (x : V) (k : ℕ) (h : H K) :
    (run width ask offset x k h).length = h.length+k := by
  induction k generalizing h with
  | zero => simp [run]
  | succ k ih => simp [run,ih,step]; omega

theorem run_snoc (width : ℕ → ℕ) (ask : Ask K V) (offset) (x : V) (k : ℕ) (h : H K) :
    run width ask offset x (k+1) h =
      step width ask offset x (run width ask offset x k h) := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    change run width ask offset x (k+1) (step width ask offset x h) = _
    rw [ih]
    rfl

theorem run_eq_fold (width : ℕ → ℕ) (ask : Ask K V) (offset) (x : V) (k : ℕ) :
    run width ask offset x k [] =
      (List.range k).foldl (fun (h : H K) j =>
        h ++ [List.ofFn (fun i : Fin (width j) => ask h i.val x + offset h i.val)]) [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run_snoc,List.range_succ,List.foldl_append,← ih]
    have length := run_length width ask offset x k []
    simp only [List.length_nil,Nat.zero_add] at length
    change _ ++ [List.ofFn (fun i : Fin (width (run width ask offset x k []).length) => _)] = _
    generalize eq : run width ask offset x k [] = h at *
    simp only [length, Fin.val_cast, List.foldl_cons, List.foldl_nil]

theorem run_take (width : ℕ → ℕ) (ask : Ask K V) (offset) (x : V) {k r : ℕ} (hkr : k ≤ r) :
    (run width ask offset x r []).take k = run width ask offset x k [] := by
  induction hkr with
  | refl =>
    have h := run_length width ask offset x k []
    exact List.take_of_length_le (by simpa using h.le)
  | @step r kr ih =>
    rw [run_snoc]
    unfold step
    have length := run_length width ask offset x r []
    rw [List.take_append_of_le_length (by simpa [length] using kr), ih]

def Capacity (width : ℕ → ℕ) (r d : ℕ) : ℕ :=
  ∏ j ∈ (Finset.range r).filter (fun j => d ≤ j), (width j+1)

theorem cap_step (width : ℕ → ℕ) {r d : ℕ} (h : d<r) :
    Capacity width r d = (width d+1) * Capacity width r (d+1) := by
  unfold Capacity
  have eq : ((Finset.range r).filter fun j => d ≤ j) =
      insert d ((Finset.range r).filter fun j => d+1 ≤ j) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_insert]
    omega
  rw [eq, Finset.prod_insert (by simp)]

theorem cap_positive (width : ℕ → ℕ) (r d : ℕ) : 0 < Capacity width r d := by
  unfold Capacity
  positivity

theorem cap_antitone (width : ℕ → ℕ) {r d e : ℕ} (hde : d≤e) (her : e≤r) :
    Capacity width r e ≤ Capacity width r d := by
  induction hde with
  | refl => rfl
  | @step e hde ih =>
    have step := cap_step width (show e<r by omega)
    have le : Capacity width r (e+1) ≤ Capacity width r e := by
      rw [step]
      simpa using Nat.mul_le_mul_right (Capacity width r (e+1)) (show 1 ≤ width e+1 by omega)
    exact le.trans (ih (by omega))

def FitsFrom (width : ℕ → ℕ) (ask : Ask K V) (offset : H K → ℕ → K)
    (answer : H K → Option ι) (dead : ι → ℕ) (bad : ι → AffineSubspace K V)
    (h : H K) (fuel : ℕ) (Q : AffineSubspace K V) : Prop :=
  (∀ x ∈ Q, ∃ k ≤ fuel, (answer (run width ask offset x k h)).isSome = true) ∧
  ∀ x ∈ Q, ∀ k ≤ fuel, ∀ i, answer (run width ask offset x k h) = some i →
    h.length+k ≤ dead i ∧ x ∉ bad i

private def observeAffine (width : ℕ → ℕ) (ask : Ask K V) (offset : H K → ℕ → K) (h : H K) :
    V →ᵃ[K] (Fin (width h.length) → K) :=
  (LinearMap.pi (fun i : Fin (width h.length) => ask h i.val)).toAffineMap +
    AffineMap.const K V (fun i => offset h i.val)

private theorem observe_eq_step (width : ℕ → ℕ) (ask : Ask K V) (offset : H K → ℕ → K)
    (h : H K) (x z : V) (eq : observeAffine width ask offset h z = observeAffine width ask offset h x) :
    step width ask offset z h = step width ask offset x h := by
  change (fun i : Fin (width h.length) => ask h i.val z + offset h i.val) =
    (fun i : Fin (width h.length) => ask h i.val x + offset h i.val) at eq
  unfold step
  rw [eq]

private theorem stopped (width : ℕ → ℕ) (ask : Ask K V) (offset : H K → ℕ → K)
    (answer : H K → Option ι) (dead : ι → ℕ) (bad : ι → AffineSubspace K V)
    {r : ℕ} (dead_le : ∀ i, dead i ≤ r) {h : H K} {fuel : ℕ} {Q : AffineSubspace K V}
    (fit : FitsFrom width ask offset answer dead bad h fuel Q)
    {i : ι} (label : answer h = some i) :
    ∃ S : Finset ι, (∑ i ∈ S, Capacity width r (dead i)) ≤ Capacity width r h.length ∧
      NoCommon Q bad S := by
  by_cases empty : ¬ (Q : Set V).Nonempty
  · exact ⟨∅, by simp, fun x hx => (empty ⟨x,hx⟩).elim⟩
  obtain ⟨x,hx⟩ := not_not.mp empty
  refine ⟨{i}, ?_, ?_⟩
  · have deadline := (fit.2 x hx 0 (Nat.zero_le _) i label).1
    simpa using cap_antitone width (by simpa using deadline) (dead_le i)
  · intro z hz
    exact ⟨i,by simp,(fit.2 z hz 0 (Nat.zero_le _) i label).2⟩

theorem boundedLabels [DecidableEq ι] (width : ℕ → ℕ) (ask : Ask K V) (offset : H K → ℕ → K)
    (answer : H K → Option ι) (dead : ι → ℕ) (bad : ι → AffineSubspace K V)
    (r : ℕ) (dead_le : ∀ i, dead i ≤ r) :
    ∀ fuel (h : H K) (Q : AffineSubspace K V), h.length+fuel = r →
      FitsFrom width ask offset answer dead bad h fuel Q →
      ∃ S : Finset ι, (∑ i ∈ S, Capacity width r (dead i)) ≤ Capacity width r h.length ∧
        NoCommon Q bad S := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro h Q _ fit
    cases eq : answer h with
    | some i => exact stopped width ask offset answer dead bad dead_le fit eq
    | none =>
      refine ⟨∅,by simp,?_⟩
      intro x hx
      obtain ⟨k,hk,yes⟩ := fit.1 x hx
      have : k=0 := by omega
      simp [this,run,eq] at yes
  | succ fuel ih =>
    intro h Q length fit
    cases eq : answer h with
    | some i => exact stopped width ask offset answer dead bad dead_le fit eq
    | none =>
      let f := observeAffine width ask offset h
      let cost := fun i => Capacity width r (dead i)
      have fiber : ∀ x ∈ Q, ∃ S : Finset ι,
          (∑ i ∈ S, cost i) ≤ Capacity width r (h.length+1) ∧
          (∀ _i ∈ S, True) ∧
          (∀ z ∈ Q, f z = f x → ∃ i ∈ S, z ∉ bad i) := by
        intro x hx
        let h' := step width ask offset x h
        let Q' := Q ⊓ (AffineSubspace.mk' (f x) ⊥).comap f
        have Q'mem (z : V) : z ∈ Q' ↔ z ∈ Q ∧ f z = f x := by
          change z ∈ Q ⊓ (AffineSubspace.mk' (f x) ⊥).comap f ↔ _
          simp [AffineSubspace.mem_inf_iff, AffineSubspace.mem_comap, AffineSubspace.mem_mk', sub_eq_zero]
        have len : h'.length = h.length+1 := by simp [h',step]
        have transition (z : V) (hz : z ∈ Q') (k : ℕ) :
            run width ask offset z (k+1) h = run width ask offset z k h' := by
          change run width ask offset z k (step width ask offset z h) = _
          have same := observe_eq_step width ask offset h x z (Q'mem z |>.1 hz).2
          rw [same]
        have fit' : FitsFrom width ask offset answer dead bad h' fuel Q' := by
          constructor
          · intro z hz
            obtain ⟨k,hk,yes⟩ := fit.1 z ((Q'mem z).1 hz).1
            cases k with
            | zero => simp [run,eq] at yes
            | succ k =>
              rw [transition z hz k] at yes
              exact ⟨k,by omega,yes⟩
          · intro z hz k hk i found
            rw [← transition z hz k] at found
            have valid := fit.2 z ((Q'mem z).1 hz).1 (k+1) (by omega) i found
            rw [len]
            exact ⟨by omega, valid.2⟩
        obtain ⟨S,spend,covers⟩ := ih h' Q' (by omega) fit'
        exact ⟨S,by simpa only [len] using spend, fun _ _ => trivial,
          fun z hz same => covers z ((Q'mem z).2 ⟨hz,same⟩)⟩
      obtain ⟨S,spend,_,covers⟩ := rankBatch Q bad f cost _ (fun _ => True) fiber
      have rank : Module.finrank K (Fin (width h.length) → K) = width h.length := by simp
      rw [rank,← cap_step width (show h.length<r by omega)] at spend
      exact ⟨S,spend,covers⟩

end Protocol

end PEqualNP.Outside.L_pcx_419_aux

namespace PEqualNP.Outside.L_pcx_419_aux

theorem forwardCriterion {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [DecidableEq ι]
    (width : ℕ → ℕ) (ask : Ask K V) (offset : H K → ℕ → K)
    (answer : H K → Option ι) (dead : ι → ℕ) (bad : ι → AffineSubspace K V)
    (r : ℕ) (dead_le : ∀ i, dead i≤r) (P : AffineSubspace K V)
    (fit : FitsFrom width ask offset answer dead bad [] r P) :
    ∃ (S : Finset ι) (lin : ι → V →ₗ[K] K) (bias : ι → K),
      (∑ i ∈ S, Capacity width r (dead i)) ≤ Capacity width r 0 ∧
      (∀ i ∈ S, ∀ x ∈ P, x ∈ bad i → lin i x + bias i = 0) ∧
      (∀ x ∈ P, (∑ i ∈ S, (lin i x + bias i)) = 1) := by
  obtain ⟨S,hS,cover⟩ := boundedLabels width ask offset answer dead bad r dead_le r [] P (by simp) fit
  obtain ⟨l,b,vanishes,sum⟩ := affineCertificate P bad S cover
  exact ⟨S,l,b,hS,vanishes,sum⟩


end PEqualNP.Outside.L_pcx_419_aux

namespace PEqualNP.Outside.L_pcx_419_aux

section Packing

theorem cap_dvd (width : ℕ → ℕ) {r a b : ℕ} (ab : a≤b) (br : b≤r) :
    Capacity width r b ∣ Capacity width r a := by
  induction ab with
  | refl => exact dvd_refl _
  | @step b ab ih =>
    refine dvd_trans ?_ (ih (by omega))
    rw [cap_step width (show b<r by omega)]
    exact dvd_mul_left _ _

structure Packed {ι : Type} (width : ℕ → ℕ) (r : ℕ) (dead : ι → ℕ)
    (S : Finset ι) where
  start : ι → ℕ
  align : ∀ i∈S, Capacity width r (dead i) ∣ start i
  root : ∀ i∈S, start i + Capacity width r (dead i) ≤ Capacity width r 0
  apart : ∀ i∈S, ∀ j∈S, i≠j →
    start i+Capacity width r (dead i) ≤ start j ∨ start j+Capacity width r (dead j) ≤ start i

noncomputable def pack {m r : ℕ} (width : ℕ → ℕ) (dead : Fin m → ℕ) (S : Finset (Fin m))
    (le : ∀ i, dead i≤r)
    (spend : (∑ i∈S, Capacity width r (dead i)) ≤ Capacity width r 0) :
    Packed width r dead S := by
  let key := fun (i : Fin m) => dead i*(m+1)+i.val
  let cost := fun (i : Fin m) => Capacity width r (dead i)
  let earlier := fun i => S.filter (fun j => key j < key i)
  let start := fun i => ∑ j∈earlier i, cost j
  have order {i j} (h : key i ≤ key j) : dead i ≤ dead j := by
    by_contra! bad
    have twice := Nat.mul_le_mul_right (m+1) (show dead j+1≤dead i by omega)
    rw [Nat.add_mul,one_mul] at twice
    dsimp [key] at h
    have := j.isLt
    omega
  have inj : Function.Injective key := by
    intro i j h
    have hd := Nat.le_antisymm (order h.le) (order h.ge)
    dsimp [key] at h
    rw [hd] at h
    exact Fin.ext (by omega)
  have notBefore (i) : i∉earlier i := by simp [earlier]
  refine ⟨start,?_,?_,?_⟩
  · intro i hi
    apply Finset.dvd_sum
    intro j hj
    exact cap_dvd width (order (Finset.mem_filter.mp hj).2.le) (le i)
  · intro i hi
    have sub : insert i (earlier i) ⊆ S := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact (Finset.mem_filter.mp hj).1
    have h := Finset.sum_le_sum_of_subset (f := cost) sub
    rw [Finset.sum_insert (notBefore i)] at h
    dsimp [cost,start] at *
    omega
  · intro i hi j hj ne
    have before {i j} (hi : i∈S) (lt : key i<key j) :
        start i+cost i ≤ start j := by
      have sub : insert i (earlier i) ⊆ earlier j := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_filter.mpr ⟨hi,lt⟩
        · obtain ⟨mem,h⟩ := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨mem,h.trans lt⟩
      have h := Finset.sum_le_sum_of_subset (f := cost) sub
      rw [Finset.sum_insert (notBefore i)] at h
      dsimp [start]
      omega
    rcases lt_or_gt_of_ne (fun h => ne (inj h)) with h | h
    · exact Or.inl (before hi h)
    · exact Or.inr (before hj h)

variable {ι : Type} [DecidableEq ι] {width : ℕ → ℕ} {r : ℕ}
  {dead : ι → ℕ} {S : Finset ι}

def bucket (p : Packed width r dead S) (d lo : ℕ) : Finset ι :=
  S.filter (fun i => lo ≤ p.start i ∧ p.start i+Capacity width r (dead i) ≤ lo+Capacity width r d)

omit [DecidableEq ι] in
lemma bucket_root (p : Packed width r dead S) : bucket p 0 0 = S := by
  exact Finset.filter_true_of_mem (fun i hi => ⟨Nat.zero_le _,by simpa using p.root i hi⟩)

lemma full_bucket (p : Packed width r dead S) {d lo : ℕ} {i : ι}
    (hi : i ∈ bucket p d lo) (hd : dead i=d) :
    bucket p d lo = {i} := by
  have ⟨hiS,left,right⟩ := Finset.mem_filter.mp hi
  rw [hd] at right
  have same : p.start i=lo := by omega
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hi,?_⟩
  intro j hj
  by_contra ne
  obtain ⟨hjS,leftj,rightj⟩ := Finset.mem_filter.mp hj
  have dis := p.apart i hiS j hjS (Ne.symm ne)
  rw [hd,same] at dis
  have pos := cap_positive width r (dead j)
  omega

def childBucket (p : Packed width r dead S) (d lo j : ℕ) : Finset ι :=
  bucket p (d+1) (lo+j*Capacity width r (d+1))

omit [DecidableEq ι] in
private lemma child_subset (p : Packed width r dead S) {d lo j : ℕ} (dr : d<r)
    (jlt : j<width d+1) : childBucket p d lo j ⊆ bucket p d lo := by
  intro i hi
  obtain ⟨inS,left,right⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨inS,?_,?_⟩
  · exact (Nat.le_add_right _ _).trans left
  · rw [cap_step width dr]
    have mul := Nat.mul_le_mul_right (Capacity width r (d+1)) (show j+1≤width d+1 by omega)
    rw [Nat.add_mul,one_mul] at mul
    omega

theorem buckets_partition (p : Packed width r dead S) {d lo : ℕ}
    (dr : d<r) (aligned : Capacity width r d ∣ lo)
    (d_le : ∀ i, dead i≤r) (pending : ∀ i∈bucket p d lo, d<dead i) :
    ((Finset.univ : Finset (Fin (width d+1))).biUnion
      (fun j => childBucket p d lo j.val)) = bucket p d lo ∧
    ((Finset.univ : Finset (Fin (width d+1))) : Set (Fin (width d+1))).PairwiseDisjoint
      (fun j => childBucket p d lo j.val) := by
  classical
  let c := Capacity width r (d+1)
  have pos : 0<c := cap_positive width r _
  constructor
  · ext i
    constructor
    · intro hi
      obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hi
      exact child_subset p dr j.isLt hj
    · intro hi
      obtain ⟨iS,left,right⟩ := Finset.mem_filter.mp hi
      let j := (p.start i-lo)/c
      have hmul : j*c ≤ p.start i-lo := Nat.div_mul_le_self _ _
      have upper : p.start i-lo < (j+1)*c := (Nat.div_lt_iff_lt_mul pos).mp (Nat.lt_succ_self _)
      have jlt : j<width d+1 := by
        apply (Nat.div_lt_iff_lt_mul pos).mpr
        have cap := cap_positive width r (dead i)
        rw [cap_step width dr] at right
        change p.start i+Capacity width r (dead i) ≤ lo+(width d+1)*c at right
        omega
      have childLeft : lo+j*c ≤ p.start i := by omega
      refine Finset.mem_biUnion.mpr ⟨⟨j,jlt⟩,Finset.mem_univ _,Finset.mem_filter.mpr ⟨iS,childLeft,?_⟩⟩
      have len : Capacity width r (dead i) ∣ c := cap_dvd width (by have := pending i hi; omega) (d_le i)
      have dlo : Capacity width r (dead i) ∣ lo :=
        (cap_dvd width (Nat.le_of_lt (pending i hi)) (d_le i)).trans aligned
      have endDvd : Capacity width r (dead i) ∣ lo+(j+1)*c :=
        Nat.dvd_add dlo (dvd_mul_of_dvd_right len _)
      have gap : Capacity width r (dead i) ∣ (lo+(j+1)*c)-p.start i :=
        Nat.dvd_sub endDvd (p.align i iS)
      have delta : 0 < (lo+(j+1)*c)-p.start i := by omega
      have wle := Nat.le_of_dvd delta gap
      have childRight : p.start i+Capacity width r (dead i) ≤ lo+(j+1)*c := by omega
      show p.start i+Capacity width r (dead i) ≤ lo+j*c+c
      simpa only [Nat.add_mul,one_mul,add_assoc] using childRight
  · intro j _ k _ ne
    apply Finset.disjoint_left.mpr
    intro i hj hk
    obtain ⟨_,lj,rj⟩ := Finset.mem_filter.mp hj
    obtain ⟨_,lk,rk⟩ := Finset.mem_filter.mp hk
    change lo+j.val*c ≤ p.start i at lj
    change lo+k.val*c ≤ p.start i at lk
    change p.start i+Capacity width r (dead i) ≤ lo+j.val*c+c at rj
    change p.start i+Capacity width r (dead i) ≤ lo+k.val*c+c at rk
    have plen := cap_positive width r (dead i)
    rcases lt_or_gt_of_ne (fun h => ne (Fin.ext h)) with h | h
    · have m := Nat.mul_le_mul_right c (show j.val+1≤k.val by omega)
      rw [Nat.add_mul,one_mul] at m
      omega
    · have m := Nat.mul_le_mul_right c (show k.val+1≤j.val by omega)
      rw [Nat.add_mul,one_mul] at m
      omega

end Packing

end PEqualNP.Outside.L_pcx_419_aux

namespace PEqualNP.Outside.L_pcx_419_aux

section Build

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]

inductive Plan (K V ι : Type) [Field K] [AddCommGroup V] [Module K V]
  | leaf (result : Option ι)
  | branch (ask : ℕ → V →ₗ[K] K) (offset : ℕ → K) (next : List K → Plan K V ι)

def Plan.label : Plan K V ι → Option ι
  | .leaf i => i
  | .branch .. => none

def Plan.linear : Plan K V ι → ℕ → V →ₗ[K] K
  | .leaf _ => fun _ => 0
  | .branch q _ _ => q

def Plan.offset : Plan K V ι → ℕ → K
  | .leaf _ => fun _ => 0
  | .branch _ off _ => off

def Plan.follow : H K → Plan K V ι → Plan K V ι
  | [], p => p
  | _ :: h, .leaf _ => Plan.follow h (.leaf none)
  | a :: h, .branch _ _ next => Plan.follow h (next a)

theorem follow_append (h t : H K) (p : Plan K V ι) :
    Plan.follow (h++t) p = Plan.follow t (Plan.follow h p) := by
  induction h generalizing p with
  | nil => rfl
  | cons a h ih => cases p <;> simp only [List.cons_append,Plan.follow,ih]

def Plan.move (w : ℕ) (x : V) (p : Plan K V ι) : Plan K V ι :=
  Plan.follow [List.ofFn (fun j : Fin w => p.linear j.val x + p.offset j.val)] p

def drive (width : ℕ → ℕ) (x : V) : ℕ → ℕ → Plan K V ι → Plan K V ι
  | 0, _, p => p
  | k+1, d, p => drive width x k (d+1) (p.move (width d) x)

theorem drive_leaf (width : ℕ → ℕ) (x : V) (k d : ℕ) (i : Option ι) :
    drive (K := K) width x (k+1) d (.leaf i) = .leaf none := by
  induction k generalizing d i with
  | zero => rfl
  | succ k ih => exact ih (d+1) none

theorem plan_run (width : ℕ → ℕ) (x : V) (p : Plan K V ι) (h : H K) (k : ℕ) :
    Plan.follow (run width (fun h => (Plan.follow h p).linear) (fun h => (Plan.follow h p).offset) x k h) p =
      drive width x k h.length (Plan.follow h p) := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    let q := fun h => (Plan.follow h p).linear
    let off := fun h => (Plan.follow h p).offset
    let h' := step width q off x h
    change Plan.follow (run width q off x k h') p = _
    rw [ih h']
    have len : h'.length = h.length+1 := by simp [h',step]
    have node : Plan.follow h' p = (Plan.follow h p).move (width h.length) x := by
      unfold h' step Plan.move
      rw [follow_append]
    rw [len,node]
    rfl

def Plan.Valid (width : ℕ → ℕ) (dead : ι → ℕ) (bad : ι → AffineSubspace K V)
    (d fuel : ℕ) (p : Plan K V ι) (x : V) : Prop :=
  (∃ k≤fuel, (drive width x k d p).label.isSome = true) ∧
  ∀ k≤fuel, ∀ i, (drive width x k d p).label = some i → d+k≤dead i ∧ x∉bad i

private theorem plan_leaf (width : ℕ → ℕ) (dead : ι → ℕ) (bad : ι → AffineSubspace K V)
    (d fuel : ℕ) (x : V) (i : ι) (valid : d≤dead i ∧ x∉bad i) :
    Plan.Valid width dead bad d fuel (.leaf (some i)) x := by
  refine ⟨⟨0,Nat.zero_le _,rfl⟩,?_⟩
  intro k hk j eq
  cases k with
  | zero =>
    change some i = some j at eq
    cases Option.some.inj eq
    simpa using valid
  | succ k => simp [drive_leaf,Plan.label] at eq

private noncomputable def selectDigit [DecidableEq K] (w : ℕ) (a : List K) : Fin (w+1) :=
  if h : ∃ j : Fin w, a.getD j.val 0 ≠ 0 then (Classical.choose h).castSucc else Fin.last w

private lemma goodDigit [DecidableEq K] (w : ℕ) (z : Fin (w+1) → K)
    (nz : (∑ j, z j) ≠ 0) :
    z (selectDigit w (List.ofFn (fun j : Fin w => z j.castSucc))) ≠ 0 := by
  classical
  have get (j : Fin w) :
      (List.ofFn (fun j : Fin w => z j.castSucc)).getD j.val 0 = z j.castSucc := by
    simp [List.getD_eq_getElem?_getD,j.isLt]
  unfold selectDigit
  split
  · rename_i h
    simpa only [get] using Classical.choose_spec h
  · rename_i h
    intro eq
    apply nz
    rw [Fin.sum_univ_castSucc]
    simp only [eq,add_zero]
    apply Finset.sum_eq_zero
    intro j _
    by_contra hj
    exact h ⟨j,by simpa only [get] using hj⟩

variable [DecidableEq ι] [DecidableEq K] {width : ℕ → ℕ} {r : ℕ} {dead : ι → ℕ} {S : Finset ι}

def score (lin : ι → V →ₗ[K] K) (bias : ι → K) (B : Finset ι) (x : V) : K :=
  ∑ i∈B, (lin i x+bias i)

theorem planFromPacking (p : Packed width r dead S) (dead_le : ∀ i, dead i≤r)
    (P : AffineSubspace K V) (bad : ι → AffineSubspace K V)
    (lin : ι → V →ₗ[K] K) (bias : ι → K)
    (vanishes : ∀ i∈S, ∀ x∈P, x∈bad i → lin i x+bias i=0) :
    ∀ fuel d lo, d+fuel=r → Capacity width r d ∣ lo →
      (∀ i∈bucket p d lo, d≤dead i) →
      ∃ tree : Plan K V ι, ∀ x∈P, score lin bias (bucket p d lo) x≠0 →
        tree.Valid width dead bad d fuel x := by
  classical
  have leafAt (fuel d lo : ℕ) {i} (mem : i∈bucket p d lo) (di : dead i=d) :
      ∃ tree : Plan K V ι, ∀ x∈P, score lin bias (bucket p d lo) x≠0 →
        tree.Valid width dead bad d fuel x := by
    refine ⟨.leaf (some i),?_⟩
    intro x hx nz
    apply plan_leaf
    refine ⟨by omega,?_⟩
    intro hb
    apply nz
    rw [full_bucket p mem di]
    simp [score,vanishes i (Finset.mem_filter.mp mem).1 x hx hb]
  intro fuel
  induction fuel with
  | zero =>
    intro d lo dr align pending
    by_cases has : ∃ i∈bucket p d lo, dead i=d
    · obtain ⟨i,mem,di⟩ := has
      exact leafAt 0 d lo mem di
    · refine ⟨.leaf none,?_⟩
      intro x hx nz
      exfalso
      apply nz
      apply Finset.sum_eq_zero
      intro i hi
      exact (has ⟨i,hi,by have := pending i hi; have := dead_le i; omega⟩).elim
  | succ fuel ih =>
    intro d lo dr align pending
    by_cases has : ∃ i∈bucket p d lo, dead i=d
    · obtain ⟨i,mem,di⟩ := has
      exact leafAt (fuel+1) d lo mem di
    have earlier : ∀ i∈bucket p d lo, d<dead i := by
      intro i hi
      have := pending i hi
      have ne : dead i ≠ d := fun eq => has ⟨i,hi,eq⟩
      omega
    have time : d<r := by omega
    let B := fun j : Fin (width d+1) => childBucket p d lo j.val
    have blocks := buckets_partition p time align dead_le earlier
    have branches (j : Fin (width d+1)) :
        ∃ tree : Plan K V ι, ∀ x∈P, score lin bias (B j) x≠0 →
          tree.Valid width dead bad (d+1) fuel x := by
      have a : Capacity width r (d+1) ∣ lo+j.val*Capacity width r (d+1) :=
        Nat.dvd_add ((cap_dvd width (by omega) (by omega)).trans align) (dvd_mul_left _ _)
      apply ih (d+1) (lo+j.val*Capacity width r (d+1)) (by omega) a
      intro i hi
      exact earlier i (child_subset p time j.isLt hi)
    choose trees checks using branches
    let q := fun j : ℕ => if h:j<width d then ∑ i∈B ⟨j,by omega⟩, lin i else 0
    let o := fun j : ℕ => if h:j<width d then ∑ i∈B ⟨j,by omega⟩, bias i else 0
    let t : Plan K V ι := .branch q o (fun a => trees (selectDigit (width d) a))
    refine ⟨t,?_⟩
    intro x hx nonzero
    let y := fun j : Fin (width d+1) => score lin bias (B j) x
    have parts : ∑ j, y j = score lin bias (bucket p d lo) x := by
      symm
      change (∑ i ∈ bucket p d lo, (lin i x+bias i)) = _
      rw [← blocks.1, Finset.sum_biUnion blocks.2]
      rfl
    have batch : (fun j : Fin (width d) => q j.val x + o j.val) = fun j => y j.castSucc := by
      funext j
      dsimp [q,o,y]
      simp only [dite_eq_left j.isLt,LinearMap.sum_apply,score,Finset.sum_add_distrib]
      rfl
    let j := selectDigit (width d) (List.ofFn (fun j : Fin (width d) => y j.castSucc))
    have chosen : y j≠0 := goodDigit (width d) y (by rw [parts]; exact nonzero)
    have moved : t.move (width d) x = trees j := by
      change trees (selectDigit (width d) (List.ofFn (fun j : Fin (width d) => q j.val x + o j.val))) = trees j
      rw [batch]
    have valid := checks j x hx chosen
    constructor
    · obtain ⟨k,hk,hx⟩ := valid.1
      refine ⟨k+1,by omega,?_⟩
      simpa only [drive,moved] using hx
    · intro k hk i found
      cases k with
      | zero => simp [drive,t,Plan.label] at found
      | succ k =>
        simp only [drive,moved] at found
        obtain ⟨time,good⟩ := valid.2 k (by omega) i found
        exact ⟨by omega,good⟩

end Build

end PEqualNP.Outside.L_pcx_419_aux

namespace PEqualNP.Outside.L_pcx_419_aux

theorem backwardCriterion {K V : Type} [Field K] [DecidableEq K]
    [AddCommGroup V] [Module K V] {m r : ℕ}
    (P : AffineSubspace K V) (bad : Fin m → AffineSubspace K V)
    (width : ℕ → ℕ) (dead : Fin m → ℕ) (le : ∀ i, dead i≤r)
    (S : Finset (Fin m)) (lin : Fin m → V →ₗ[K] K) (bias : Fin m → K)
    (spend : (∑ i∈S, Capacity width r (dead i)) ≤ Capacity width r 0)
    (zero_on_bad : ∀ i∈S, ∀ x∈P, x∈bad i → lin i x+bias i=0)
    (sum_one : ∀ x∈P, (∑ i∈S, (lin i x+bias i))=1) :
    ∃ (ask : Ask K V) (offset : H K → ℕ → K) (answer : H K → Option (Fin m)),
      FitsFrom width ask offset answer dead bad [] r P := by
  let packed := pack width dead S le spend
  obtain ⟨p,valid⟩ := planFromPacking packed le P bad lin bias zero_on_bad
    r 0 0 (by simp) (dvd_zero _) (fun _ _ => Nat.zero_le _)
  have follows (x : V) (k : ℕ) :
      Plan.follow (run width (fun h => (Plan.follow h p).linear)
        (fun h => (Plan.follow h p).offset) x k []) p =
        drive width x k 0 p := by
    exact plan_run width x p [] k
  have report (x : V) (hx : x∈P) : p.Valid width dead bad 0 r x := by
    apply valid x hx
    rw [bucket_root,score,sum_one x hx]
    exact one_ne_zero
  refine ⟨fun h => (Plan.follow h p).linear,fun h => (Plan.follow h p).offset,
    fun h => (Plan.follow h p).label,?_⟩
  constructor
  · intro x hx
    obtain ⟨k,hk,ok⟩ := (report x hx).1
    exact ⟨k,hk,by simpa only [follows] using ok⟩
  · intro x hx k hk i answer
    change (Plan.follow (run width (fun h => (Plan.follow h p).linear)
      (fun h => (Plan.follow h p).offset) x k []) p).label = some i at answer
    rw [follows] at answer
    simpa using (report x hx).2 k hk i answer

theorem fits_fold_iff {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    (P : AffineSubspace K V) (bad : ι → AffineSubspace K V)
    (width : ℕ → ℕ) (dead : ι → ℕ) (r : ℕ)
    (ask : Ask K V) (offset : H K → ℕ → K) (answer : H K → Option ι) :
    let obs := fun (x : V) =>
      (List.range r).foldl (fun (h : H K) (j : ℕ) =>
        h ++ [List.ofFn (fun i : Fin (width j) => ask h i.val x + offset h i.val)]) []
    FitsFrom width ask offset answer dead bad [] r P ↔
      (∀ x∈P, ∃ k≤r, (answer ((obs x).take k)).isSome=true) ∧
      ∀ x∈P, ∀ k≤r, ∀ i, answer ((obs x).take k)=some i → k≤dead i ∧ x∉bad i := by
  dsimp only
  have transition (x : V) (k : ℕ) (hk : k≤r) :
      ((List.range r).foldl (fun (h : H K) (j : ℕ) =>
        h ++ [List.ofFn (fun i : Fin (width j) => ask h i.val x + offset h i.val)]) []).take k =
      run width ask offset x k [] := by
    rw [← run_eq_fold]
    exact run_take width ask offset x hk
  constructor
  · rintro ⟨hit,safe⟩
    constructor
    · intro x hx
      obtain ⟨k,hk,ok⟩ := hit x hx
      exact ⟨k,hk,by rwa [transition x k hk]⟩
    · intro x hx k hk i h
      rw [transition x k hk] at h
      simpa using safe x hx k hk i h
  · rintro ⟨hit,safe⟩
    constructor
    · intro x hx
      obtain ⟨k,hk,ok⟩ := hit x hx
      exact ⟨k,hk,by rwa [← transition x k hk]⟩
    · intro x hx k hk i h
      rw [← transition x k hk] at h
      simpa using safe x hx k hk i h

end PEqualNP.Outside.L_pcx_419_aux

open PEqualNP.Outside.L_pcx_419_aux in
theorem PEqualNP.Outside.L_pcx_419 :
∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (n m r : ℕ),
  let X := Fin n → K
  ∀ (P : AffineSubspace K X) (bad : Fin m → AffineSubspace K X)
    (width : ℕ → ℕ) (deadline : Fin m → Fin (r+1)),
    (∃ x : X, x ∈ P) →
    let H := List (List K)
    let obs := fun (ask : H → ℕ → X →ₗ[K] K) (off : H → ℕ → K) (x : X) =>
      (List.range r).foldl (fun (h : H) (j : ℕ) =>
        h ++ [List.ofFn (fun i : Fin (width j) => ask h i.val x + off h i.val)]) []
    let room := ∏ j ∈ Finset.range r, (width j + 1)
    let price := fun i : Fin m => ∏ j ∈ (Finset.range r).filter
      (fun j => (deadline i).val ≤ j), (width j + 1)
    (∃ (ask : H → ℕ → X →ₗ[K] K) (off : H → ℕ → K) (answer : H → Option (Fin m)),
      (∀ x ∈ P, ∃ k ≤ r, (answer ((obs ask off x).take k)).isSome = true) ∧
      ∀ x ∈ P, ∀ k ≤ r, ∀ i, answer ((obs ask off x).take k) = some i →
        k ≤ (deadline i).val ∧ x ∉ bad i) ↔
    ∃ (S : Finset (Fin m)) (lin : Fin m → X →ₗ[K] K) (bias : Fin m → K),
      (∑ i ∈ S, price i) ≤ room ∧
      (∀ i ∈ S, ∀ x ∈ P, x ∈ bad i → lin i x + bias i = 0) ∧
      ∀ x ∈ P, (∑ i ∈ S, (lin i x + bias i)) = 1
  := by
  intro K field finite dec n m r
  dsimp only
  intro P bad width deadline _
  let dead := fun i : Fin m => (deadline i).val
  have le (i : Fin m) : dead i ≤ r := Nat.le_of_lt_succ (deadline i).isLt
  constructor
  · rintro ⟨ask,offset,answer,fit⟩
    have fits := (fits_fold_iff P bad width dead r ask offset answer).2 fit
    simpa [Capacity,dead] using forwardCriterion width ask offset answer dead bad r le P fits
  · rintro ⟨S,lin,bias,spend,zero_on_bad,sum_one⟩
    have spend' : (∑ i∈S, Capacity width r (dead i)) ≤ Capacity width r 0 := by
      simpa [Capacity,dead] using spend
    obtain ⟨ask,offset,answer,fit⟩ :=
      backwardCriterion P bad width dead le S lin bias spend' zero_on_bad sum_one
    exact ⟨ask,offset,answer,(fits_fold_iff P bad width dead r ask offset answer).1 fit⟩
