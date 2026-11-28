import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1073_aux

open scoped BigOperators

abbrev F2 := ZMod 2

private lemma card_filter_add_not {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  classical
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h1 : ∀ x ∈ s, (if p x then 1 else 0) + (if ¬ p x then 1 else 0) = 1 := by
    intro x _; by_cases hp : p x <;> simp [hp]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]

private def det2 (u v : F2 × F2) : F2 := u.1 * v.2 + u.2 * v.1

private lemma det2_self (u : F2 × F2) : det2 u u = 0 := by
  revert u; decide

private lemma det2_comm (u v : F2 × F2) : det2 u v = det2 v u := by
  revert u v; decide

private lemma det2_ne_zero_left {u v : F2 × F2} (h : det2 u v = 1) : u ≠ (0, 0) := by
  revert u v h; decide

private def colorVec : Fin 3 → F2 × F2
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)

private def vecColor : F2 × F2 → Fin 3
  | (1, 0) => 0
  | (0, 1) => 1
  | (1, 1) => 2
  | (0, 0) => 0

private lemma vecColor_colorVec (c : Fin 3) : vecColor (colorVec c) = c := by
  fin_cases c <;> rfl

private lemma colorVec_vecColor {v : F2 × F2} (hv : v ≠ (0, 0)) : colorVec (vecColor v) = v := by
  revert v hv; decide

private lemma colorVec_ne_zero (c : Fin 3) : colorVec c ≠ (0, 0) := by
  fin_cases c <;> decide

private lemma colorVec_inj : Function.Injective colorVec := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [colorVec]

private lemma card_partners (u : F2 × F2) (hu : u ≠ (0, 0)) :
    (Finset.univ.filter (fun v : F2 × F2 => det2 u v = 1)).card = 2 := by
  revert u hu; decide

private lemma unique_w (c d w : F2 × F2) (b : Bool) (hcd : det2 c d = 1) :
    (det2 c w = 0 ∧ decide (det2 d w = 1) = b) ↔ w = if b then c else (0, 0) := by
  revert c d w b hcd; decide

private lemma card_t_bichromatic (ci cj : F2 × F2) (hci : ci ≠ (0, 0)) (hcj : cj ≠ (0, 0))
    (hneq : ci ≠ cj) (s : Bool) :
    (Finset.univ.filter (fun t : F2 × F2 => det2 ci t = 1 ∧ decide (det2 cj t = 1) = s)).card = 1 := by
  revert ci cj hci hcj hneq s; decide

private lemma det2_zero_left (t : F2 × F2) : det2 (0, 0) t = 0 := by
  revert t; decide

private def matOfVec {n : ℕ} (v : Fin n → F2 × F2) : Matrix (Fin n) (Fin n) F2 :=
  fun i j => det2 (v i) (v j)

private lemma matOfVec_alt {n : ℕ} (v : Fin n → F2 × F2) :
    (∀ i, matOfVec v i i = 0) ∧ ∀ i j, matOfVec v i j = matOfVec v j i :=
  ⟨fun i => det2_self (v i), fun i j => det2_comm (v i) (v j)⟩

private lemma matOfVec_rank_le_two {n : ℕ} (v : Fin n → F2 × F2) :
    Matrix.rank (matOfVec v) ≤ 2 := by
  let u1 : Fin n → F2 := fun i => (v i).1
  let u2 : Fin n → F2 := fun i => (v i).2
  have hle : LinearMap.range (matOfVec v).mulVecLin ≤ Submodule.span F2 ({u1, u2} : Set (Fin n → F2)) := by
    rintro _ ⟨x, rfl⟩
    have hEq : (matOfVec v).mulVecLin x = (∑ j : Fin n, (v j).2 * x j) • u1 +
        (∑ j : Fin n, (v j).1 * x j) • u2 := by
      funext i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, matOfVec, det2,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, u1, u2, Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hEq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert u1 _)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem u1 (Set.mem_singleton u2))))
  have h1 : Matrix.rank (matOfVec v) ≤ Module.finrank F2 (Submodule.span F2 ({u1, u2} : Set (Fin n → F2))) :=
    Submodule.finrank_mono hle
  have h2 : Module.finrank F2 (Submodule.span F2 ({u1, u2} : Set (Fin n → F2))) ≤ 2 := by
    have hcard := finrank_span_le_card (R := F2) ({u1, u2} : Set (Fin n → F2))
    have hle2 : ({u1, u2} : Set (Fin n → F2)).toFinset.card ≤ 2 := by
      calc ({u1, u2} : Set (Fin n → F2)).toFinset.card
          = ({u1, u2} : Finset (Fin n → F2)).card := by congr 1; ext z; simp
        _ ≤ 2 := Finset.card_le_two
    exact le_trans hcard hle2
  exact le_trans h1 h2

private lemma eq_matOfVec_of_rank_le_two {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) F2) (hrk : Matrix.rank A ≤ 2)
    (halt : (∀ i, A i i = 0) ∧ ∀ i j, A i j = A j i)
    (h01 : A ⟨0, by omega⟩ ⟨1, by omega⟩ = 1) :
    A = matOfVec (fun i => (A i ⟨1, by omega⟩, A i ⟨0, by omega⟩)) := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let c0 : Fin n → F2 := fun i => A i i0
  let c1 : Fin n → F2 := fun i => A i i1
  have hc0_mem : c0 ∈ LinearMap.range A.mulVecLin := by
    refine ⟨Pi.single i0 1, ?_⟩
    funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply, c0]
  have hc1_mem : c1 ∈ LinearMap.range A.mulVecLin := by
    refine ⟨Pi.single i1 1, ?_⟩
    funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply, c1]
  let S := Submodule.span F2 ({c0, c1} : Set (Fin n → F2))
  have hSle : S ≤ LinearMap.range A.mulVecLin := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hc0_mem
    · exact hc1_mem
  have h01' : A i0 i1 = 1 := h01
  have hli : LinearIndependent F2 ![c0, c1] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := congr_fun hg i0
    have h1 := congr_fun hg i1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, c0, c1,
      halt.1 i0, halt.1 i1, halt.2 i1 i0, h01', mul_zero, mul_one, zero_add, add_zero] at h0 h1
    intro j; fin_cases j
    · exact h1
    · exact h0
  have hSdim : Module.finrank F2 S = 2 := by
    have hset : ({c0, c1} : Set (Fin n → F2)) = Set.range ![c0, c1] := by
      ext x; simp [Fin.exists_fin_two, or_comm]
    have hrng : S = Submodule.span F2 (Set.range ![c0, c1]) := congrArg (Submodule.span F2) hset
    rw [hrng, finrank_span_eq_card hli, Fintype.card_fin]
  have hSeq : S = LinearMap.range A.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq hSle
    have hle2 : Module.finrank F2 (LinearMap.range A.mulVecLin) ≤ 2 := hrk
    have hge2 : 2 ≤ Module.finrank F2 (LinearMap.range A.mulVecLin) :=
      le_trans (le_of_eq hSdim.symm) (Submodule.finrank_mono hSle)
    omega
  ext i j
  have hcol_mem : (fun r => A r j) ∈ S := by
    rw [hSeq]
    refine ⟨Pi.single j 1, ?_⟩
    funext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hmem_pair : (fun r => A r j) ∈ Submodule.span F2 ({c0, c1} : Set (Fin n → F2)) := hcol_mem
  rw [Submodule.mem_span_pair] at hmem_pair
  rcases hmem_pair with ⟨a, b, hab⟩
  have hAt0 := congr_fun hab i0
  have hAt1 := congr_fun hab i1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, c0, c1,
    halt.1 i0, halt.1 i1, halt.2 i1 i0, h01', mul_zero, mul_one, zero_add, add_zero] at hAt0 hAt1
  have hAti := congr_fun hab i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, c0, c1] at hAti
  rw [← hAti, hAt0, hAt1]
  simp only [matOfVec, det2]
  rw [halt.2 i1 j, halt.2 i0 j]
  ring

private lemma card_pairs (k : ℕ) :
    ((Finset.univ : Finset (Fin k × Fin k)).filter (fun e => e.1 < e.2)).card = k.choose 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    let P := (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).filter (fun e => e.1 < e.2)
    let P1 := P.filter (fun e => e.2 < Fin.last k)
    let P2 := P.filter (fun e => ¬ e.2 < Fin.last k)
    have hsplit : P.card = P1.card + P2.card := (card_filter_add_not P _).symm
    have hP1 : P1.card = k.choose 2 := by
      rw [← ih]
      refine Finset.card_bij
        (fun e he => (⟨e.1.val, by
            have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
            have h2 := (Finset.mem_filter.mp he).2
            change e.1.val < e.2.val at h1
            change e.2.val < k at h2
            omega⟩,
          ⟨e.2.val, by
            have h2 := (Finset.mem_filter.mp he).2
            change e.2.val < k at h2
            omega⟩)) ?_ ?_ ?_
      · intro e he
        have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h1
      · intro e1 _ e2 _ h
        have h1 := congr_arg (fun p => p.1.val) h
        have h2 := congr_arg (fun p => p.2.val) h
        exact Prod.ext (Fin.ext h1) (Fin.ext h2)
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        refine ⟨(e.1.castSucc, e.2.castSucc), ?_, ?_⟩
        · simp only [P1, P, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨he, e.2.isLt⟩
        · exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
    have hP2 : P2.card = k := by
      trans (Finset.univ : Finset (Fin k)).card
      swap
      · exact Finset.card_fin k
      refine Finset.card_bij
        (fun e he => ⟨e.1.val, by
          have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
          have h2 := (Finset.mem_filter.mp he).2
          change e.1.val < e.2.val at h1
          have h2' : e.2.val = k := by
            have := e.2.isLt
            change ¬ e.2.val < k at h2
            omega
          omega⟩) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro e1 he1 e2 he2 h
        have h1 : e1.1.val = e2.1.val := congr_arg (fun z : Fin k => z.val) h
        have h2a := (Finset.mem_filter.mp he1).2
        have h2b := (Finset.mem_filter.mp he2).2
        have he12 : e1.2.val = k := by have := e1.2.isLt; change ¬ e1.2.val < k at h2a; omega
        have he22 : e2.2.val = k := by have := e2.2.isLt; change ¬ e2.2.val < k at h2b; omega
        exact Prod.ext (Fin.ext h1) (Fin.ext (he12.trans he22.symm))
      · intro i _
        refine ⟨(i.castSucc, Fin.last k), ?_, Fin.ext rfl⟩
        simp only [P2, P, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i.isLt, Nat.lt_irrefl k⟩
    rw [hsplit, hP1, hP2, Nat.choose_succ_succ, Nat.choose_one_right]
    ring

private noncomputable def pairEquiv (k : ℕ) :
    Fin (k.choose 2) ≃ {ij : Fin k × Fin k // ij.1 < ij.2} :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype]
    exact card_pairs k)).symm

private def idx0 (k : ℕ) : Fin (2 + 2 * k + 2 * k.choose 2) := ⟨0, by omega⟩
private def idx1 (k : ℕ) : Fin (2 + 2 * k + 2 * k.choose 2) := ⟨1, by omega⟩
private def cIdx (k : ℕ) (i : Fin k) : Fin (2 + 2 * k + 2 * k.choose 2) :=
  ⟨2 + 2 * i.val, by omega⟩
private def dIdx (k : ℕ) (i : Fin k) : Fin (2 + 2 * k + 2 * k.choose 2) :=
  ⟨2 + 2 * i.val + 1, by omega⟩
private def wIdx (k : ℕ) (e : Fin (k.choose 2)) : Fin (2 + 2 * k + 2 * k.choose 2) :=
  ⟨2 + 2 * k + 2 * e.val, by omega⟩
private def tIdx (k : ℕ) (e : Fin (k.choose 2)) : Fin (2 + 2 * k + 2 * k.choose 2) :=
  ⟨2 + 2 * k + 2 * e.val + 1, by omega⟩

private lemma idx_ne_helpers (k : ℕ) :
    (idx0 k < idx1 k) ∧
    (∀ i : Fin k, cIdx k i < dIdx k i) ∧
    (∀ (j : Fin k) (e : Fin (k.choose 2)), cIdx k j < wIdx k e) ∧
    (∀ (j : Fin k) (e : Fin (k.choose 2)), dIdx k j < wIdx k e) ∧
    (∀ (i : Fin k) (e : Fin (k.choose 2)), cIdx k i < tIdx k e) ∧
    (∀ e : Fin (k.choose 2), wIdx k e < tIdx k e) := by
  refine ⟨by change 0 < 1; omega,
    fun i => by change 2 + 2 * i.val < 2 + 2 * i.val + 1; omega,
    fun j e => by change 2 + 2 * j.val < 2 + 2 * k + 2 * e.val; omega,
    fun j e => by change 2 + 2 * j.val + 1 < 2 + 2 * k + 2 * e.val; omega,
    fun i e => by change 2 + 2 * i.val < 2 + 2 * k + 2 * e.val + 1; omega,
    fun e => by change 2 + 2 * k + 2 * e.val < 2 + 2 * k + 2 * e.val + 1; omega⟩

private lemma main_proof (k : ℕ) :
    let K := Fin k
    let p := k.choose 2
    let n := 2 + 2 * k + 2 * p
    let I := Fin n
    let Mat := Matrix I I (ZMod 2)
    let colors := K → Fin 3
    let edges := fun (g : K → K → Bool) => (Finset.univ : Finset (K × K)).filter
      (fun e => e.1 < e.2 ∧ g e.1 e.2 = true)
    let alt := fun (A : Mat) => (∀ i, A i i = 0) ∧ ∀ i j, A i j = A j i
    ∃ (H S : Finset (I × I)) (base : I × I → Bool) (ask : I × I → Option (K × K))
      (decode : Mat → colors),
      H.card = 1 + k + 3 * p ∧ S.card = p ∧ Disjoint H S ∧
      (∀ e ∈ H ∪ S, e.1 < e.2) ∧
      (∀ e ∈ H, ∀ i j, ask e = some (i, j) → i < j) ∧
      (∀ i j : K, i < j → ∃! e : I × I, e ∈ H ∧ ask e = some (i, j)) ∧
      ∀ (g : K → K → Bool) (c : colors) (q : ℕ),
        let m := (edges g).card
        let d := ((edges g).filter (fun e => c e.1 = c e.2)).card
        let label := fun e => (ask e).elim (base e) (fun ij => g ij.1 ij.2)
        let accepts := fun (A : Mat) => Matrix.rank A ≤ 2 ∧ alt A ∧ decode A = c ∧
          (∀ e ∈ H, decide (A e.1 e.2 = 1) = label e) ∧
          (S.filter (fun e => A e.1 e.2 = 1)).card = q
        ((Finset.univ : Finset Mat).filter
          (fun A => @decide (accepts A) (Classical.propDecidable _))).card =
          if d ≤ q then 2 ^ (k + (p - m) + d) * (m - d).choose (q - d) else 0 := by
  classical
  let K := Fin k
  let p := k.choose 2
  let n := 2 + 2 * k + 2 * p
  let I := Fin n
  let Mat := Matrix I I (ZMod 2)
  let pe := pairEquiv k
  let H0 : Finset (I × I) := {(idx0 k, idx1 k)}
  let H1 : Finset (I × I) := Finset.univ.image (fun i : K => (cIdx k i, dIdx k i))
  let H2 : Finset (I × I) := Finset.univ.image (fun e : Fin p => (cIdx k (pe e).1.2, wIdx k e))
  let H3 : Finset (I × I) := Finset.univ.image (fun e : Fin p => (dIdx k (pe e).1.2, wIdx k e))
  let H4 : Finset (I × I) := Finset.univ.image (fun e : Fin p => (cIdx k (pe e).1.1, tIdx k e))
  let H : Finset (I × I) := H0 ∪ H1 ∪ H2 ∪ H3 ∪ H4
  let S : Finset (I × I) := Finset.univ.image (fun e : Fin p => (wIdx k e, tIdx k e))
  let base : I × I → Bool := fun x => if x ∈ H2 then false else true
  let ask : I × I → Option (K × K) := fun x =>
    if h : ∃ e : Fin p, x = (dIdx k (pe e).1.2, wIdx k e) then
      some (pe (Classical.choose h)).1
    else none
  let decode : Mat → (K → Fin 3) := fun A i => vecColor (A (cIdx k i) (idx1 k), A (cIdx k i) (idx0 k))
  have hH0_card : H0.card = 1 := Finset.card_singleton _
  have hH1_card : H1.card = k := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_fin k
    · intro i1 i2 h
      have := congr_arg (fun x => x.1.val) h
      exact Fin.ext (by dsimp [cIdx] at this; omega)
  have hH2_card : H2.card = p := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_fin p
    · intro e1 e2 h
      have := congr_arg (fun x => x.2.val) h
      exact Fin.ext (by dsimp [wIdx] at this; omega)
  have hH3_card : H3.card = p := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_fin p
    · intro e1 e2 h
      have := congr_arg (fun x => x.2.val) h
      exact Fin.ext (by dsimp [wIdx] at this; omega)
  have hH4_card : H4.card = p := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_fin p
    · intro e1 e2 h
      have := congr_arg (fun x => x.2.val) h
      exact Fin.ext (by dsimp [tIdx] at this; omega)
  have hS_card : S.card = p := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_fin p
    · intro e1 e2 h
      have := congr_arg (fun x => x.1.val) h
      exact Fin.ext (by dsimp [wIdx] at this; omega)
  have hdisj01 : Disjoint H0 H1 := by
    rw [Finset.disjoint_left]; intro x hx0 hx1
    simp only [H0, Finset.mem_singleton] at hx0; subst hx0
    simp only [H1, Finset.mem_image, Finset.mem_univ, true_and] at hx1
    rcases hx1 with ⟨i, hi⟩
    have := congr_arg (fun z => z.1.val) hi
    dsimp [idx0, cIdx] at this; omega
  have hdisj01_2 : Disjoint (H0 ∪ H1) H2 := by
    rw [Finset.disjoint_left]; intro x hx hx2
    simp only [H2, Finset.mem_image, Finset.mem_univ, true_and] at hx2
    rcases hx2 with ⟨e, rfl⟩
    simp only [Finset.mem_union, H0, H1, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with h | ⟨i, hi⟩
    · have := congr_arg (fun z => z.2.val) h; dsimp [idx1, wIdx] at this; omega
    · have := congr_arg (fun z => z.2.val) hi; dsimp [dIdx, wIdx] at this; omega
  have hdisj012_3 : Disjoint (H0 ∪ H1 ∪ H2) H3 := by
    rw [Finset.disjoint_left]; intro x hx hx3
    simp only [H3, Finset.mem_image, Finset.mem_univ, true_and] at hx3
    rcases hx3 with ⟨e, rfl⟩
    simp only [Finset.mem_union, H0, H1, H2, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with (h | ⟨i, hi⟩) | ⟨e', he'⟩
    · have := congr_arg (fun z => z.2.val) h; dsimp [idx1, wIdx] at this; omega
    · have := congr_arg (fun z => z.2.val) hi; dsimp [dIdx, wIdx] at this; omega
    · have := congr_arg (fun z => z.1.val) he'; dsimp [cIdx, dIdx] at this; omega
  have hdisj0123_4 : Disjoint (H0 ∪ H1 ∪ H2 ∪ H3) H4 := by
    rw [Finset.disjoint_left]; intro x hx hx4
    simp only [H4, Finset.mem_image, Finset.mem_univ, true_and] at hx4
    rcases hx4 with ⟨e, rfl⟩
    simp only [Finset.mem_union, H0, H1, H2, H3, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with ((h | ⟨i, hi⟩) | ⟨e', he'⟩) | ⟨e', he'⟩
    · have := congr_arg (fun z => z.2.val) h; dsimp [idx1, tIdx] at this; omega
    · have := congr_arg (fun z => z.2.val) hi; dsimp [dIdx, tIdx] at this; omega
    · have := congr_arg (fun z => z.2.val) he'; dsimp [wIdx, tIdx] at this; omega
    · have := congr_arg (fun z => z.2.val) he'; dsimp [wIdx, tIdx] at this; omega
  have hH_card : H.card = 1 + k + 3 * p := by
    simp only [H]
    rw [Finset.card_union_of_disjoint hdisj0123_4, Finset.card_union_of_disjoint hdisj012_3,
      Finset.card_union_of_disjoint hdisj01_2, Finset.card_union_of_disjoint hdisj01,
      hH0_card, hH1_card, hH2_card, hH3_card, hH4_card]
    omega
  have hdisjHS : Disjoint H S := by
    rw [Finset.disjoint_left]; intro x hxH hxS
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hxS
    rcases hxS with ⟨e, rfl⟩
    simp only [H, Finset.mem_union, H0, H1, H2, H3, H4, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and] at hxH
    rcases hxH with (((h | ⟨i, hi⟩) | ⟨e', he'⟩) | ⟨e', he'⟩) | ⟨e', he'⟩
    · have := congr_arg (fun z => z.1.val) h; dsimp [idx0, wIdx] at this; omega
    · have := congr_arg (fun z => z.1.val) hi; dsimp [cIdx, wIdx] at this; omega
    · have := congr_arg (fun z => z.1.val) he'; dsimp [cIdx, wIdx] at this; omega
    · have := congr_arg (fun z => z.1.val) he'; dsimp [dIdx, wIdx] at this; omega
    · have := congr_arg (fun z => z.1.val) he'; dsimp [cIdx, wIdx] at this; omega
  have hltHS : ∀ x ∈ H ∪ S, x.1 < x.2 := by
    intro x hx
    have hhlp := idx_ne_helpers k
    simp only [Finset.mem_union, H, H0, H1, H2, H3, H4, S, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and] at hx
    rcases hx with ((((rfl | ⟨i, rfl⟩) | ⟨e, rfl⟩) | ⟨e, rfl⟩) | ⟨e, rfl⟩) | ⟨e, rfl⟩
    · exact hhlp.1
    · exact hhlp.2.1 i
    · exact hhlp.2.2.1 _ e
    · exact hhlp.2.2.2.1 _ e
    · exact hhlp.2.2.2.2.1 _ e
    · exact hhlp.2.2.2.2.2 e
  have hask_H3 : ∀ e : Fin p, ask (dIdx k (pe e).1.2, wIdx k e) = some (pe e).1 := by
    intro e
    simp only [ask]
    split_ifs with h
    · have hch : (dIdx k (pe e).1.2, wIdx k e) =
          (dIdx k (pe (Classical.choose h)).1.2, wIdx k (Classical.choose h)) :=
        Classical.choose_spec h
      have hw : wIdx k e = wIdx k (Classical.choose h) := congr_arg Prod.snd hch
      have hval : 2 + 2 * k + 2 * e.val = 2 + 2 * k + 2 * (Classical.choose h).val :=
        congr_arg Fin.val hw
      have heq : Classical.choose h = e := Fin.ext (by omega)
      rw [heq]
    · exact absurd ⟨e, rfl⟩ h
  have hask_none : ∀ x, x ∉ H3 → ask x = none := by
    intro x hx
    simp only [ask]
    rw [dif_neg]
    rintro ⟨e, rfl⟩
    exact hx (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩)
  have hask_lt : ∀ x ∈ H, ∀ i j, ask x = some (i, j) → i < j := by
    intro x _ i j h
    by_cases hx3 : x ∈ H3
    · rcases Finset.mem_image.mp hx3 with ⟨e, _, rfl⟩
      rw [hask_H3 e] at h
      have hij : (pe e).1 = (i, j) := Option.some.inj h
      have hlt := (pe e).2
      rw [hij] at hlt
      exact hlt
    · rw [hask_none x hx3] at h; cases h
  have hask_uniq : ∀ i j : K, i < j → ∃! x : I × I, x ∈ H ∧ ask x = some (i, j) := by
    intro i j hij
    let e : Fin p := pe.symm ⟨(i, j), hij⟩
    have hpe : pe e = ⟨(i, j), hij⟩ := pe.apply_symm_apply _
    refine ⟨(dIdx k (pe e).1.2, wIdx k e), ⟨?_, ?_⟩, ?_⟩
    · simp only [H, Finset.mem_union]
      left; right
      exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
    · rw [hask_H3 e, hpe]
    · rintro x ⟨_, hxask⟩
      by_cases hx3 : x ∈ H3
      · rcases Finset.mem_image.mp hx3 with ⟨e', _, rfl⟩
        rw [hask_H3 e'] at hxask
        have hpe' : pe e' = ⟨(i, j), hij⟩ := Subtype.ext (Option.some.inj hxask)
        have hee' : e' = e := pe.injective (hpe'.trans hpe.symm)
        subst hee'; rfl
      · rw [hask_none x hx3] at hxask; cases hxask
  refine ⟨H, S, base, ask, decode, hH_card, hS_card, hdisjHS, hltHS, hask_lt, hask_uniq, ?_⟩
  intro g c q
  dsimp only
  let edges_g := (Finset.univ : Finset (K × K)).filter (fun e => e.1 < e.2 ∧ g e.1 e.2 = true)
  let m := edges_g.card
  let d := (edges_g.filter (fun e => c e.1 = c e.2)).card
  let label := fun x => (ask x).elim (base x) (fun ij => g ij.1 ij.2)
  let accepts := fun (A : Mat) => Matrix.rank A ≤ 2 ∧ ((∀ i, A i i = 0) ∧ ∀ i j, A i j = A j i) ∧
    decode A = c ∧ (∀ x ∈ H, decide (A x.1 x.2 = 1) = label x) ∧
    (S.filter (fun x => A x.1 x.2 = 1)).card = q
  let P_all : Finset (Fin p) := Finset.univ
  let P_edge : Finset (Fin p) := P_all.filter (fun e => g (pe e).1.1 (pe e).1.2 = true)
  let P_mono : Finset (Fin p) := P_edge.filter (fun e => c (pe e).1.1 = c (pe e).1.2)
  let P_bi : Finset (Fin p) := P_edge.filter (fun e => c (pe e).1.1 ≠ c (pe e).1.2)
  have hP_edge_card : P_edge.card = m := by
    refine Finset.card_bij (fun e _ => (pe e).1) ?_ ?_ ?_
    · intro e he
      simp only [P_edge, P_all, Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [edges_g, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(pe e).2, he⟩
    · intro e1 _ e2 _ h; exact pe.injective (Subtype.ext h)
    · intro ij hij
      simp only [edges_g, Finset.mem_filter, Finset.mem_univ, true_and] at hij
      refine ⟨pe.symm ⟨ij, hij.1⟩, ?_, ?_⟩
      · simp only [P_edge, P_all, Finset.mem_filter, Finset.mem_univ, true_and, pe.apply_symm_apply]
        exact hij.2
      · simp [pe.apply_symm_apply]
  have hP_mono_card : P_mono.card = d := by
    refine Finset.card_bij (fun e _ => (pe e).1) ?_ ?_ ?_
    · intro e he
      simp only [P_mono, P_edge, P_all, Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [edges_g, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨(pe e).2, he.1⟩, he.2⟩
    · intro e1 _ e2 _ h; exact pe.injective (Subtype.ext h)
    · intro ij hij
      simp only [edges_g, Finset.mem_filter, Finset.mem_univ, true_and] at hij
      refine ⟨pe.symm ⟨ij, hij.1.1⟩, ?_, ?_⟩
      · simp only [P_mono, P_edge, P_all, Finset.mem_filter, Finset.mem_univ, true_and, pe.apply_symm_apply]
        exact ⟨hij.1.2, hij.2⟩
      · simp [pe.apply_symm_apply]
  have hP_bi_card : P_bi.card = m - d := by
    have hsplit : P_mono.card + P_bi.card = P_edge.card :=
      card_filter_add_not P_edge _
    omega
  have hm_le_p : m ≤ p := by
    calc m = P_edge.card := hP_edge_card.symm
      _ ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_le_univ P_edge
      _ = p := Finset.card_fin p
  have hd_le_m : d ≤ m := by
    rw [← hP_mono_card, ← hP_edge_card]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  let wTarget : Fin p → F2 × F2 := fun e =>
    if g (pe e).1.1 (pe e).1.2 then colorVec (c (pe e).1.2) else (0, 0)
  let scoreOf : Fin p → F2 × F2 → Bool := fun e t => decide (det2 (wTarget e) t = 1)
  let buildVec : (Fin k → F2 × F2) → (Fin p → F2 × F2) → (I → F2 × F2) := fun dv tv x =>
    if hx0 : x.val = 0 then (1, 0)
    else if hx1 : x.val = 1 then (0, 1)
    else if hlt : x.val < 2 + 2 * k then
      let idx : Fin k := ⟨(x.val - 2) / 2, by omega⟩
      if x.val % 2 = 0 then colorVec (c idx) else dv idx
    else
      let eidx : Fin p := ⟨(x.val - (2 + 2 * k)) / 2, by
        have hxlt : x.val < 2 + 2 * k + 2 * p := x.isLt
        have hxge : 2 + 2 * k ≤ x.val := Nat.le_of_not_lt hlt
        omega⟩
      if x.val % 2 = 0 then wTarget eidx else tv eidx
  have hbv0 : ∀ dv tv, buildVec dv tv (idx0 k) = (1, 0) := fun _ _ => rfl
  have hbv1 : ∀ dv tv, buildVec dv tv (idx1 k) = (0, 1) := fun _ _ => rfl
  have hbv_c : ∀ dv tv (i : Fin k), buildVec dv tv (cIdx k i) = colorVec (c i) := by
    intro dv tv i
    have hne0 : (cIdx k i).val ≠ 0 := by dsimp [cIdx]; omega
    have hne1 : (cIdx k i).val ≠ 1 := by dsimp [cIdx]; omega
    have hlt : (cIdx k i).val < 2 + 2 * k := by dsimp [cIdx]; omega
    have hev : (cIdx k i).val % 2 = 0 := by dsimp [cIdx]; omega
    have hdiv : ((cIdx k i).val - 2) / 2 = i.val := by dsimp [cIdx]; omega
    simp only [buildVec, dif_neg hne0, dif_neg hne1, dif_pos hlt, if_pos hev]
    congr 2; exact Fin.ext hdiv
  have hbv_d : ∀ dv tv (i : Fin k), buildVec dv tv (dIdx k i) = dv i := by
    intro dv tv i
    have hne0 : (dIdx k i).val ≠ 0 := by dsimp [dIdx]; omega
    have hne1 : (dIdx k i).val ≠ 1 := by dsimp [dIdx]; omega
    have hlt : (dIdx k i).val < 2 + 2 * k := by dsimp [dIdx]; omega
    have hodd : (dIdx k i).val % 2 ≠ 0 := by dsimp [dIdx]; omega
    have hdiv : ((dIdx k i).val - 2) / 2 = i.val := by dsimp [dIdx]; omega
    simp only [buildVec, dif_neg hne0, dif_neg hne1, dif_pos hlt, if_neg hodd]
    congr 1; exact Fin.ext hdiv
  have hbv_w : ∀ dv tv (e : Fin p), buildVec dv tv (wIdx k e) = wTarget e := by
    intro dv tv e
    have hne0 : (wIdx k e).val ≠ 0 := by dsimp [wIdx]; omega
    have hne1 : (wIdx k e).val ≠ 1 := by dsimp [wIdx]; omega
    have hnlt : ¬ (wIdx k e).val < 2 + 2 * k := by dsimp [wIdx]; omega
    have hev : (wIdx k e).val % 2 = 0 := by dsimp [wIdx]; omega
    have hdiv : ((wIdx k e).val - (2 + 2 * k)) / 2 = e.val := by dsimp [wIdx]; omega
    simp only [buildVec, dif_neg hne0, dif_neg hne1, dif_neg hnlt, if_pos hev]
    congr 1; exact Fin.ext hdiv
  have hbv_t : ∀ dv tv (e : Fin p), buildVec dv tv (tIdx k e) = tv e := by
    intro dv tv e
    have hne0 : (tIdx k e).val ≠ 0 := by dsimp [tIdx]; omega
    have hne1 : (tIdx k e).val ≠ 1 := by dsimp [tIdx]; omega
    have hnlt : ¬ (tIdx k e).val < 2 + 2 * k := by dsimp [tIdx]; omega
    have hodd : (tIdx k e).val % 2 ≠ 0 := by dsimp [tIdx]; omega
    have hdiv : ((tIdx k e).val - (2 + 2 * k)) / 2 = e.val := by dsimp [tIdx]; omega
    simp only [buildVec, dif_neg hne0, dif_neg hne1, dif_neg hnlt, if_neg hodd]
    congr 1; exact Fin.ext hdiv
  let GoodDT := (Finset.univ : Finset ((Fin k → F2 × F2) × (Fin p → F2 × F2))).filter
    (fun dt => (∀ i : Fin k, det2 (colorVec (c i)) (dt.1 i) = 1) ∧
      (∀ e : Fin p, det2 (colorVec (c (pe e).1.1)) (dt.2 e) = 1) ∧
      (Finset.univ.filter (fun e : Fin p => scoreOf e (dt.2 e) = true)).card = q)
  have hbij_mat : ((Finset.univ : Finset Mat).filter
      (fun A => @decide (accepts A) (Classical.propDecidable _))).card = GoodDT.card := by
    refine Finset.card_bij
      (fun A _ => (fun i => (A (dIdx k i) (idx1 k), A (dIdx k i) (idx0 k)),
                   fun e => (A (tIdx k e) (idx1 k), A (tIdx k e) (idx0 k)))) ?_ ?_ ?_
    · intro A hA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hA
      rcases hA with ⟨hrk, halt, hdec, hH, hS⟩
      have h01_mem : (idx0 k, idx1 k) ∈ H := by
        simp only [H, Finset.mem_union, H0, Finset.mem_singleton]; left; left; left; left; trivial
      have h01_notH3 : (idx0 k, idx1 k) ∉ H3 := by
        intro h3; rcases Finset.mem_image.mp h3 with ⟨e, _, he⟩
        have := congr_arg (fun z => z.1.val) he; dsimp [idx0, dIdx] at this; omega
      have h01_notH2 : (idx0 k, idx1 k) ∉ H2 := by
        intro h2; rcases Finset.mem_image.mp h2 with ⟨e, _, he⟩
        have := congr_arg (fun z => z.1.val) he; dsimp [idx0, cIdx] at this; omega
      have h01 : A (idx0 k) (idx1 k) = 1 := by
        have h := hH (idx0 k, idx1 k) h01_mem
        simp only [label, hask_none _ h01_notH3, Option.elim_none, base, if_neg h01_notH2,
          decide_eq_true_eq] at h
        exact h
      have hA_eq := eq_matOfVec_of_rank_le_two (by omega) A hrk halt h01
      let v : I → F2 × F2 := fun x => (A x (idx1 k), A x (idx0 k))
      have hv_cd : ∀ i : Fin k, det2 (v (cIdx k i)) (v (dIdx k i)) = 1 := by
        intro i
        have hmem : (cIdx k i, dIdx k i) ∈ H := by
          simp only [H, Finset.mem_union, H1, Finset.mem_image, Finset.mem_univ, true_and]
          left; left; left; right; exact ⟨i, rfl⟩
        have hnot3 : (cIdx k i, dIdx k i) ∉ H3 := by
          intro h3; rcases Finset.mem_image.mp h3 with ⟨e, _, he⟩
          have := congr_arg (fun z => z.2.val) he; dsimp [dIdx, wIdx] at this; omega
        have hnot2 : (cIdx k i, dIdx k i) ∉ H2 := by
          intro h2; rcases Finset.mem_image.mp h2 with ⟨e, _, he⟩
          have := congr_arg (fun z => z.2.val) he; dsimp [dIdx, wIdx] at this; omega
        have h := hH (cIdx k i, dIdx k i) hmem
        simp only [label, hask_none _ hnot3, Option.elim_none, base, if_neg hnot2,
          decide_eq_true_eq] at h
        rw [hA_eq] at h; exact h
      have hv_c : ∀ i : Fin k, v (cIdx k i) = colorVec (c i) := by
        intro i
        have hne0 := det2_ne_zero_left (hv_cd i)
        have hci : vecColor (v (cIdx k i)) = c i := congr_fun hdec i
        rw [← hci, colorVec_vecColor hne0]
      have hv_w : ∀ e : Fin p, v (wIdx k e) = wTarget e := by
        intro e
        have hmem2 : (cIdx k (pe e).1.2, wIdx k e) ∈ H := by
          simp only [H, Finset.mem_union, H2, Finset.mem_image, Finset.mem_univ, true_and]
          left; left; right; exact ⟨e, rfl⟩
        have hnot3 : (cIdx k (pe e).1.2, wIdx k e) ∉ H3 := by
          intro h3; rcases Finset.mem_image.mp h3 with ⟨e', _, he'⟩
          have := congr_arg (fun z => z.1.val) he'; dsimp [cIdx, dIdx] at this; omega
        have hin2 : (cIdx k (pe e).1.2, wIdx k e) ∈ H2 :=
          Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
        have h2 := hH (cIdx k (pe e).1.2, wIdx k e) hmem2
        simp only [label, hask_none _ hnot3, Option.elim_none, base, if_pos hin2,
          decide_eq_false_iff_not] at h2
        have h2_0 : det2 (colorVec (c (pe e).1.2)) (v (wIdx k e)) = 0 := by
          rw [hA_eq] at h2
          change det2 (v (cIdx k (pe e).1.2)) (v (wIdx k e)) ≠ 1 at h2
          rw [hv_c] at h2
          revert h2; generalize det2 (colorVec (c (pe e).1.2)) (v (wIdx k e)) = z; revert z; decide
        have hmem3 : (dIdx k (pe e).1.2, wIdx k e) ∈ H := by
          simp only [H, Finset.mem_union, H3, Finset.mem_image, Finset.mem_univ, true_and]
          left; right; exact ⟨e, rfl⟩
        have h3 := hH (dIdx k (pe e).1.2, wIdx k e) hmem3
        simp only [label, hask_H3 e, Option.elim_some] at h3
        rw [hA_eq] at h3
        have hcd' : det2 (colorVec (c (pe e).1.2)) (v (dIdx k (pe e).1.2)) = 1 := by
          rw [← hv_c]; exact hv_cd _
        exact (unique_w _ _ _ _ hcd').mp ⟨h2_0, h3⟩
      have hv_t : ∀ e : Fin p, det2 (colorVec (c (pe e).1.1)) (v (tIdx k e)) = 1 := by
        intro e
        have hmem4 : (cIdx k (pe e).1.1, tIdx k e) ∈ H := by
          simp only [H, Finset.mem_union, H4, Finset.mem_image, Finset.mem_univ, true_and]
          right; exact ⟨e, rfl⟩
        have hnot3 : (cIdx k (pe e).1.1, tIdx k e) ∉ H3 := by
          intro h3; rcases Finset.mem_image.mp h3 with ⟨e', _, he'⟩
          have := congr_arg (fun z => z.2.val) he'; dsimp [wIdx, tIdx] at this; omega
        have hnot2 : (cIdx k (pe e).1.1, tIdx k e) ∉ H2 := by
          intro h2; rcases Finset.mem_image.mp h2 with ⟨e', _, he'⟩
          have := congr_arg (fun z => z.2.val) he'; dsimp [wIdx, tIdx] at this; omega
        have h4 := hH (cIdx k (pe e).1.1, tIdx k e) hmem4
        simp only [label, hask_none _ hnot3, Option.elim_none, base, if_neg hnot2,
          decide_eq_true_eq] at h4
        rw [hA_eq] at h4
        change det2 (v (cIdx k (pe e).1.1)) (v (tIdx k e)) = 1 at h4
        rw [hv_c] at h4; exact h4
      simp only [GoodDT, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun i => by rw [← hv_c i]; exact hv_cd i, hv_t, ?_⟩
      rw [← hS]
      refine Finset.card_bij (fun e _ => (wIdx k e, tIdx k e)) ?_ ?_ ?_
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, scoreOf, decide_eq_true_eq] at he
        simp only [Finset.mem_filter, S, Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨⟨e, rfl⟩, ?_⟩
        rw [hA_eq]; change det2 (v (wIdx k e)) (v (tIdx k e)) = 1; rw [hv_w e]; exact he
      · intro e1 _ e2 _ h
        have := congr_arg (fun z => z.1.val) h
        exact Fin.ext (by dsimp [wIdx] at this; omega)
      · intro x hx
        simp only [Finset.mem_filter, S, Finset.mem_image, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨⟨e, rfl⟩, h1⟩
        refine ⟨e, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, scoreOf, decide_eq_true_eq]
        rw [hA_eq] at h1; change det2 (v (wIdx k e)) (v (tIdx k e)) = 1 at h1; rw [← hv_w e]; exact h1
    · intro A1 hA1 A2 hA2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hA1 hA2
      have hreconstruct : ∀ A : Mat, accepts A →
          A = matOfVec (buildVec
            (fun i => (A (dIdx k i) (idx1 k), A (dIdx k i) (idx0 k)))
            (fun e => (A (tIdx k e) (idx1 k), A (tIdx k e) (idx0 k)))) := by
        intro A ⟨hrk, halt, hdec, hH, _⟩
        have h01_mem : (idx0 k, idx1 k) ∈ H := by
          simp only [H, Finset.mem_union, H0, Finset.mem_singleton]; left; left; left; left; trivial
        have h01_notH3 : (idx0 k, idx1 k) ∉ H3 := by
          intro h3; rcases Finset.mem_image.mp h3 with ⟨e, _, he⟩
          have := congr_arg (fun z => z.1.val) he; dsimp [idx0, dIdx] at this; omega
        have h01_notH2 : (idx0 k, idx1 k) ∉ H2 := by
          intro h2; rcases Finset.mem_image.mp h2 with ⟨e, _, he⟩
          have := congr_arg (fun z => z.1.val) he; dsimp [idx0, cIdx] at this; omega
        have h01 : A (idx0 k) (idx1 k) = 1 := by
          have h := hH (idx0 k, idx1 k) h01_mem
          simp only [label, hask_none _ h01_notH3, Option.elim_none, base, if_neg h01_notH2,
            decide_eq_true_eq] at h
          exact h
        have hA_eq := eq_matOfVec_of_rank_le_two (by omega) A hrk halt h01
        let v : I → F2 × F2 := fun x => (A x (idx1 k), A x (idx0 k))
        have hv_cd : ∀ i : Fin k, det2 (v (cIdx k i)) (v (dIdx k i)) = 1 := by
          intro i
          have hmem : (cIdx k i, dIdx k i) ∈ H := by
            simp only [H, Finset.mem_union, H1, Finset.mem_image, Finset.mem_univ, true_and]
            left; left; left; right; exact ⟨i, rfl⟩
          have hnot3 : (cIdx k i, dIdx k i) ∉ H3 := by
            intro h3; rcases Finset.mem_image.mp h3 with ⟨e, _, he⟩
            have := congr_arg (fun z => z.2.val) he; dsimp [dIdx, wIdx] at this; omega
          have hnot2 : (cIdx k i, dIdx k i) ∉ H2 := by
            intro h2; rcases Finset.mem_image.mp h2 with ⟨e, _, he⟩
            have := congr_arg (fun z => z.2.val) he; dsimp [dIdx, wIdx] at this; omega
          have h := hH (cIdx k i, dIdx k i) hmem
          simp only [label, hask_none _ hnot3, Option.elim_none, base, if_neg hnot2,
            decide_eq_true_eq] at h
          rw [hA_eq] at h; exact h
        have hv_c : ∀ i : Fin k, v (cIdx k i) = colorVec (c i) := by
          intro i
          have hne0 := det2_ne_zero_left (hv_cd i)
          have hci : vecColor (v (cIdx k i)) = c i := congr_fun hdec i
          rw [← hci, colorVec_vecColor hne0]
        have hv_w : ∀ e : Fin p, v (wIdx k e) = wTarget e := by
          intro e
          have hmem2 : (cIdx k (pe e).1.2, wIdx k e) ∈ H := by
            simp only [H, Finset.mem_union, H2, Finset.mem_image, Finset.mem_univ, true_and]
            left; left; right; exact ⟨e, rfl⟩
          have hnot3 : (cIdx k (pe e).1.2, wIdx k e) ∉ H3 := by
            intro h3; rcases Finset.mem_image.mp h3 with ⟨e', _, he'⟩
            have := congr_arg (fun z => z.1.val) he'; dsimp [cIdx, dIdx] at this; omega
          have hin2 : (cIdx k (pe e).1.2, wIdx k e) ∈ H2 :=
            Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
          have h2 := hH (cIdx k (pe e).1.2, wIdx k e) hmem2
          simp only [label, hask_none _ hnot3, Option.elim_none, base, if_pos hin2,
            decide_eq_false_iff_not] at h2
          have h2_0 : det2 (colorVec (c (pe e).1.2)) (v (wIdx k e)) = 0 := by
            rw [hA_eq] at h2
            change det2 (v (cIdx k (pe e).1.2)) (v (wIdx k e)) ≠ 1 at h2
            rw [hv_c] at h2
            revert h2; generalize det2 (colorVec (c (pe e).1.2)) (v (wIdx k e)) = z; revert z; decide
          have hmem3 : (dIdx k (pe e).1.2, wIdx k e) ∈ H := by
            simp only [H, Finset.mem_union, H3, Finset.mem_image, Finset.mem_univ, true_and]
            left; right; exact ⟨e, rfl⟩
          have h3 := hH (dIdx k (pe e).1.2, wIdx k e) hmem3
          simp only [label, hask_H3 e, Option.elim_some] at h3
          rw [hA_eq] at h3
          have hcd' : det2 (colorVec (c (pe e).1.2)) (v (dIdx k (pe e).1.2)) = 1 := by
            rw [← hv_c]; exact hv_cd _
          exact (unique_w _ _ _ _ hcd').mp ⟨h2_0, h3⟩
        have hvec_eq : (fun x : I => (A x ⟨1, by omega⟩, A x ⟨0, by omega⟩)) =
            buildVec (fun i => (A (dIdx k i) (idx1 k), A (dIdx k i) (idx0 k)))
              (fun e => (A (tIdx k e) (idx1 k), A (tIdx k e) (idx0 k))) := by
          funext x
          let dvA : Fin k → F2 × F2 := fun i => (A (dIdx k i) (idx1 k), A (dIdx k i) (idx0 k))
          let tvA : Fin p → F2 × F2 := fun e => (A (tIdx k e) (idx1 k), A (tIdx k e) (idx0 k))
          change (A x (idx1 k), A x (idx0 k)) = buildVec dvA tvA x
          by_cases hx0 : x.val = 0
          · have hx : x = idx0 k := Fin.ext hx0; subst hx
            rw [hbv0 dvA tvA]; exact Prod.ext h01 (halt.1 _)
          · by_cases hx1 : x.val = 1
            · have hx : x = idx1 k := Fin.ext hx1; subst hx
              rw [hbv1 dvA tvA]; exact Prod.ext (halt.1 _) (by dsimp only; rw [halt.2]; exact h01)
            · by_cases hlt : x.val < 2 + 2 * k
              · let idx : Fin k := ⟨(x.val - 2) / 2, by omega⟩
                by_cases hev : x.val % 2 = 0
                · have hx : x = cIdx k idx := Fin.ext (by dsimp [cIdx, idx]; omega)
                  rw [hx, hbv_c dvA tvA idx]; exact hv_c idx
                · have hx : x = dIdx k idx := Fin.ext (by dsimp [dIdx, idx]; omega)
                  rw [hx, hbv_d dvA tvA idx]
              · let eidx : Fin p := ⟨(x.val - (2 + 2 * k)) / 2, by
                  have hxlt : x.val < 2 + 2 * k + 2 * p := x.isLt
                  have hxge : 2 + 2 * k ≤ x.val := Nat.le_of_not_lt hlt
                  omega⟩
                by_cases hev : x.val % 2 = 0
                · have hx : x = wIdx k eidx := Fin.ext (by dsimp [wIdx, eidx]; omega)
                  rw [hx, hbv_w dvA tvA eidx]; exact hv_w eidx
                · have hx : x = tIdx k eidx := Fin.ext (by dsimp [tIdx, eidx]; omega)
                  rw [hx, hbv_t dvA tvA eidx]
        conv_lhs => rw [hA_eq]
        congr 1
      rw [hreconstruct A1 hA1, hreconstruct A2 hA2]
      have h1 : (fun i => (A1 (dIdx k i) (idx1 k), A1 (dIdx k i) (idx0 k))) =
          (fun i => (A2 (dIdx k i) (idx1 k), A2 (dIdx k i) (idx0 k))) := congr_arg Prod.fst heq
      have h2 : (fun e => (A1 (tIdx k e) (idx1 k), A1 (tIdx k e) (idx0 k))) =
          (fun e => (A2 (tIdx k e) (idx1 k), A2 (tIdx k e) (idx0 k))) := congr_arg Prod.snd heq
      rw [h1, h2]
    · rintro ⟨dv, tv⟩ hdt
      simp only [GoodDT, Finset.mem_filter, Finset.mem_univ, true_and] at hdt
      rcases hdt with ⟨hd_ok, ht_ok, hq_ok⟩
      let v := buildVec dv tv
      let A := matOfVec v
      have hA_v : ∀ x : I, (A x (idx1 k), A x (idx0 k)) = v x := by
        intro x
        simp only [A, matOfVec, det2, v, hbv0, hbv1]
        ext <;> ring
      refine ⟨A, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
        refine ⟨matOfVec_rank_le_two v, matOfVec_alt v, ?_, ?_, ?_⟩
        · funext i
          simp only [decode, hA_v, v, hbv_c, vecColor_colorVec]
        · intro x hx
          simp only [H, Finset.mem_union, H0, H1, H2, H3, H4, Finset.mem_singleton, Finset.mem_image,
            Finset.mem_univ, true_and] at hx
          rcases hx with (((rfl | ⟨i, rfl⟩) | ⟨e, rfl⟩) | ⟨e, rfl⟩) | ⟨e, rfl⟩
          · have hnot3 : (idx0 k, idx1 k) ∉ H3 := by
              intro h3; rcases Finset.mem_image.mp h3 with ⟨e, _, he⟩
              have := congr_arg (fun z => z.1.val) he; dsimp [idx0, dIdx] at this; omega
            have hnot2 : (idx0 k, idx1 k) ∉ H2 := by
              intro h2; rcases Finset.mem_image.mp h2 with ⟨e, _, he⟩
              have := congr_arg (fun z => z.1.val) he; dsimp [idx0, cIdx] at this; omega
            simp only [label, hask_none _ hnot3, Option.elim_none, base, if_neg hnot2,
              A, matOfVec, v, hbv0, hbv1]
            decide
          · have hnot3 : (cIdx k i, dIdx k i) ∉ H3 := by
              intro h3; rcases Finset.mem_image.mp h3 with ⟨e, _, he⟩
              have := congr_arg (fun z => z.2.val) he; dsimp [dIdx, wIdx] at this; omega
            have hnot2 : (cIdx k i, dIdx k i) ∉ H2 := by
              intro h2; rcases Finset.mem_image.mp h2 with ⟨e, _, he⟩
              have := congr_arg (fun z => z.2.val) he; dsimp [dIdx, wIdx] at this; omega
            simp only [label, hask_none _ hnot3, Option.elim_none, base, if_neg hnot2,
              A, matOfVec, v, hbv_c, hbv_d, hd_ok i]
            rfl
          · have hnot3 : (cIdx k (pe e).1.2, wIdx k e) ∉ H3 := by
              intro h3; rcases Finset.mem_image.mp h3 with ⟨e', _, he'⟩
              have := congr_arg (fun z => z.1.val) he'; dsimp [cIdx, dIdx] at this; omega
            have hin2 : (cIdx k (pe e).1.2, wIdx k e) ∈ H2 :=
              Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
            simp only [label, hask_none _ hnot3, Option.elim_none, base, if_pos hin2,
              A, matOfVec, v, hbv_c, hbv_w]
            have h0 : det2 (colorVec (c (pe e).1.2)) (wTarget e) = 0 :=
              ((unique_w _ _ _ _ (hd_ok (pe e).1.2)).mpr rfl).1
            rw [h0]; decide
          · simp only [label, hask_H3 e, Option.elim_some, A, matOfVec, v, hbv_d, hbv_w]
            exact ((unique_w _ _ _ _ (hd_ok (pe e).1.2)).mpr rfl).2
          · have hnot3 : (cIdx k (pe e).1.1, tIdx k e) ∉ H3 := by
              intro h3; rcases Finset.mem_image.mp h3 with ⟨e', _, he'⟩
              have := congr_arg (fun z => z.2.val) he'; dsimp [wIdx, tIdx] at this; omega
            have hnot2 : (cIdx k (pe e).1.1, tIdx k e) ∉ H2 := by
              intro h2; rcases Finset.mem_image.mp h2 with ⟨e', _, he'⟩
              have := congr_arg (fun z => z.2.val) he'; dsimp [wIdx, tIdx] at this; omega
            simp only [label, hask_none _ hnot3, Option.elim_none, base, if_neg hnot2,
              A, matOfVec, v, hbv_c, hbv_t, ht_ok e]
            rfl
        · rw [← hq_ok]
          symm
          refine Finset.card_bij (fun e _ => (wIdx k e, tIdx k e)) ?_ ?_ ?_
          · intro e he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, scoreOf, decide_eq_true_eq] at he
            simp only [Finset.mem_filter, S, Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨⟨e, rfl⟩, by simpa only [A, matOfVec, v, hbv_w, hbv_t] using he⟩
          · intro e1 _ e2 _ h
            have hval : (wIdx k e1).val = (wIdx k e2).val := congr_arg (fun z => z.1.val) h
            simp only [wIdx] at hval
            exact Fin.ext (by omega)
          · intro x hx
            simp only [Finset.mem_filter, S, Finset.mem_image, Finset.mem_univ, true_and] at hx
            rcases hx with ⟨⟨e, rfl⟩, hx1⟩
            refine ⟨e, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, scoreOf, decide_eq_true_eq]
            simpa only [A, matOfVec, v, hbv_w, hbv_t] using hx1
      · refine Prod.ext (funext fun i => ?_) (funext fun e => ?_)
        · dsimp only; rw [hA_v]; dsimp only [v]; rw [hbv_d]
        · dsimp only; rw [hA_v]; dsimp only [v]; rw [hbv_t]
  rw [hbij_mat]
  have hscore_abs : ∀ e : Fin p, e ∉ P_edge → ∀ t, scoreOf e t = false := by
    intro e he t
    simp only [P_edge, P_all, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at he
    simp only [scoreOf, wTarget, he, Bool.false_eq_true, ↓reduceIte, det2_zero_left]
    decide
  have hscore_mono : ∀ e ∈ P_mono, ∀ t, det2 (colorVec (c (pe e).1.1)) t = 1 → scoreOf e t = true := by
    intro e he t ht
    simp only [P_mono, P_edge, P_all, Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp only [scoreOf, wTarget, he.1, ↓reduceIte, ← he.2, ht, decide_true]
  have hscore_split : ∀ (tv : Fin p → F2 × F2),
      (∀ e : Fin p, det2 (colorVec (c (pe e).1.1)) (tv e) = 1) →
      Finset.univ.filter (fun e : Fin p => scoreOf e (tv e) = true) =
        P_mono ∪ P_bi.filter (fun e => scoreOf e (tv e) = true) := by
    intro tv htv
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hs
      by_cases hedge : e ∈ P_edge
      · by_cases hmc : c (pe e).1.1 = c (pe e).1.2
        · left; exact Finset.mem_filter.mpr ⟨hedge, hmc⟩
        · right; exact ⟨Finset.mem_filter.mpr ⟨hedge, hmc⟩, hs⟩
      · rw [hscore_abs e hedge] at hs; cases hs
    · rintro (hm | ⟨_, hs⟩)
      · exact hscore_mono e hm (tv e) (htv e)
      · exact hs
  have hdisj_mb : Disjoint P_mono P_bi := by
    rw [Finset.disjoint_left]; intro e h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  by_cases hdq : d ≤ q
  · rw [if_pos hdq]
    have hfib : GoodDT.card = ∑ T ∈ P_bi.powersetCard (q - d),
        (GoodDT.filter (fun dt => P_bi.filter (fun e => scoreOf e (dt.2 e) = true) = T)).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun dt : (Fin k → F2 × F2) × (Fin p → F2 × F2) =>
          P_bi.filter (fun e => scoreOf e (dt.2 e) = true))]
      intro dt hdt
      simp only [Finset.mem_coe, GoodDT, Finset.mem_filter, Finset.mem_univ, true_and] at hdt
      simp only [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      have hU := hscore_split dt.2 hdt.2.1
      have hcard := congr_arg Finset.card hU
      rw [hdt.2.2, Finset.card_union_of_disjoint (Disjoint.mono_right (Finset.filter_subset _ _) hdisj_mb),
        hP_mono_card] at hcard
      omega
    rw [hfib]
    have hperT : ∀ T ∈ P_bi.powersetCard (q - d),
        (GoodDT.filter (fun dt => P_bi.filter (fun e => scoreOf e (dt.2 e) = true) = T)).card =
          2 ^ (k + (p - m) + d) := by
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      let D_set : Fin k → Finset (F2 × F2) := fun i =>
        Finset.univ.filter (fun x => det2 (colorVec (c i)) x = 1)
      let T_set : Fin p → Finset (F2 × F2) := fun e =>
        if e ∈ P_bi then
          Finset.univ.filter (fun t => det2 (colorVec (c (pe e).1.1)) t = 1 ∧
            scoreOf e t = decide (e ∈ T))
        else
          Finset.univ.filter (fun t => det2 (colorVec (c (pe e).1.1)) t = 1)
      let ProdSet := (Fintype.piFinset D_set) ×ˢ (Fintype.piFinset T_set)
      have hEqSet : GoodDT.filter (fun dt => P_bi.filter (fun e => scoreOf e (dt.2 e) = true) = T) =
          ProdSet := by
        ext ⟨dv, tv⟩
        simp only [GoodDT, ProdSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          Fintype.mem_piFinset, D_set, T_set]
        constructor
        · rintro ⟨⟨hd1, ht1, _⟩, hTeq⟩
          refine ⟨hd1, fun e => ?_⟩
          by_cases hbi : e ∈ P_bi
          · simp only [if_pos hbi, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨ht1 e, ?_⟩
            by_cases heT : e ∈ T
            · simp only [heT, decide_true]
              rw [← hTeq] at heT
              exact (Finset.mem_filter.mp heT).2
            · simp only [heT, decide_false]
              by_contra hne
              have htrue : scoreOf e (tv e) = true := by revert hne; cases scoreOf e (tv e) <;> decide
              exact heT (hTeq ▸ Finset.mem_filter.mpr ⟨hbi, htrue⟩)
          · simp only [if_neg hbi, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ht1 e
        · rintro ⟨hd1, ht1⟩
          have htv_ok : ∀ e : Fin p, det2 (colorVec (c (pe e).1.1)) (tv e) = 1 := by
            intro e
            have h := ht1 e
            by_cases hbi : e ∈ P_bi
            · simp only [if_pos hbi, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.1
            · simp only [if_neg hbi, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h
          have hTeq : P_bi.filter (fun e => scoreOf e (tv e) = true) = T := by
            ext e
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hbi, hs⟩
              have h := ht1 e
              simp only [if_pos hbi, Finset.mem_filter, Finset.mem_univ, true_and] at h
              rw [hs] at h
              exact of_decide_eq_true h.2.symm
            · intro heT
              have hbi : e ∈ P_bi := hT.1 heT
              have h := ht1 e
              simp only [if_pos hbi, Finset.mem_filter, Finset.mem_univ, true_and, heT, decide_true] at h
              exact ⟨hbi, h.2⟩
          refine ⟨⟨hd1, htv_ok, ?_⟩, hTeq⟩
          rw [hscore_split tv htv_ok, hTeq,
            Finset.card_union_of_disjoint (Disjoint.mono_right hT.1 hdisj_mb), hP_mono_card, hT.2]
          omega
      rw [hEqSet, Finset.card_product, Fintype.card_piFinset, Fintype.card_piFinset]
      have hDprod : ∏ i : Fin k, (D_set i).card = 2 ^ k := by
        have h2 : ∀ i : Fin k, (D_set i).card = 2 := fun i => card_partners _ (colorVec_ne_zero _)
        simp [h2]
      have hTcard : ∀ e : Fin p, (T_set e).card = if e ∈ P_bi then 1 else 2 := by
        intro e
        by_cases hbi : e ∈ P_bi
        · simp only [T_set, if_pos hbi]
          have hbi' := hbi
          simp only [P_bi, P_edge, P_all, Finset.mem_filter, Finset.mem_univ, true_and] at hbi'
          have hneq : colorVec (c (pe e).1.1) ≠ colorVec (c (pe e).1.2) :=
            fun h => hbi'.2 (colorVec_inj h)
          have hw : wTarget e = colorVec (c (pe e).1.2) := by simp [wTarget, hbi'.1]
          simpa only [scoreOf, hw] using
            card_t_bichromatic _ _ (colorVec_ne_zero _) (colorVec_ne_zero _) hneq (decide (e ∈ T))
        · simp only [T_set, if_neg hbi]
          exact card_partners _ (colorVec_ne_zero _)
      have hTprod : ∏ e : Fin p, (T_set e).card = 2 ^ ((p - m) + d) := by
        simp_rw [hTcard]
        rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
        have hnotbi : (Finset.univ.filter (fun e : Fin p => e ∉ P_bi)).card = (p - m) + d := by
          have h1 := card_filter_add_not (Finset.univ : Finset (Fin p)) (fun e => e ∈ P_bi)
          have h2 : (Finset.univ.filter (fun e : Fin p => e ∈ P_bi)).card = P_bi.card := by
            congr 1; ext e; simp
          rw [h2, Finset.card_fin, hP_bi_card] at h1
          omega
        rw [hnotbi]
      rw [hDprod, hTprod, ← pow_add, add_assoc]
    rw [Finset.sum_congr rfl hperT, Finset.sum_const, smul_eq_mul, Finset.card_powersetCard,
      hP_bi_card, mul_comm]
  · rw [if_neg hdq]
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro ⟨dv, tv⟩ hdt
    simp only [GoodDT, Finset.mem_filter, Finset.mem_univ, true_and] at hdt
    have hU := hscore_split tv hdt.2.1
    have hcard := congr_arg Finset.card hU
    rw [hdt.2.2, Finset.card_union_of_disjoint (Disjoint.mono_right (Finset.filter_subset _ _) hdisj_mb),
      hP_mono_card] at hcard
    omega

end PEqualNP.Outside.L_lib_1073_aux

theorem PEqualNP.Outside.L_lib_1073 :
  ∀ k : ℕ,
    let K := Fin k
    let p := k.choose 2
    let n := 2+2*k+2*p
    let I := Fin n
    let Mat := Matrix I I (ZMod 2)
    let colors := K → Fin 3
    let edges := fun (g : K → K → Bool) => (Finset.univ : Finset (K × K)).filter
      (fun e => e.1 < e.2 ∧ g e.1 e.2 = true)
    let alt := fun (A : Mat) => (∀ i, A i i = 0) ∧ ∀ i j, A i j = A j i
    ∃ (H S : Finset (I × I)) (base : I × I → Bool) (ask : I × I → Option (K × K))
      (decode : Mat → colors),
      H.card = 1+k+3*p ∧ S.card = p ∧ Disjoint H S ∧
      (∀ e ∈ H ∪ S, e.1 < e.2) ∧
      (∀ e ∈ H, ∀ i j, ask e = some (i,j) → i < j) ∧
      (∀ i j : K, i < j → ∃! e : I × I, e ∈ H ∧ ask e = some (i,j)) ∧
      ∀ (g : K → K → Bool) (c : colors) (q : ℕ),
        let m := (edges g).card
        let d := ((edges g).filter (fun e => c e.1 = c e.2)).card
        let label := fun e => (ask e).elim (base e) (fun ij => g ij.1 ij.2)
        let accepts := fun (A : Mat) => Matrix.rank A ≤ 2 ∧ alt A ∧ decode A = c ∧
          (∀ e ∈ H, decide (A e.1 e.2 = 1) = label e) ∧
          (S.filter (fun e => A e.1 e.2 = 1)).card = q
        ((Finset.univ : Finset Mat).filter
          (fun A => @decide (accepts A) (Classical.propDecidable _))).card =
          if d ≤ q then 2^(k+(p-m)+d) * (m-d).choose (q-d) else 0 := by
  intro k
  exact PEqualNP.Outside.L_lib_1073_aux.main_proof k
