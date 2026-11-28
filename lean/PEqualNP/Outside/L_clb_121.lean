import PEqualNP.Defs
import PEqualNP.Outside.L_lib_871
import PEqualNP.Outside.L_lib_377

namespace PEqualNP.Outside.L_clb_121_aux

lemma encode_automaton {n K : ℕ} {Row : Type} {State : Type} [Fintype State]
    (s0 : State) (stepS : Fin n → State → Row → State) (outS : State → Bool × Bool)
    (hcard : Fintype.card State ≤ K) :
    ∃ (start : Fin K) (step : Fin n → Fin K → Row → Fin K) (out : Fin K → Bool × Bool),
      ∀ raw : Fin n → Row,
        out ((List.finRange n).foldl (fun st pos => step pos st (raw pos)) start) =
          outS ((List.finRange n).foldl (fun st pos => stepS pos st (raw pos)) s0) := by
  let e : State ≃ Fin (Fintype.card State) := Fintype.equivFin State
  let enc : State → Fin K := fun s => ⟨(e s).val, lt_of_lt_of_le (e s).isLt hcard⟩
  let dec : Fin K → State := fun k => if hk : k.val < Fintype.card State then e.symm ⟨k.val, hk⟩ else s0
  have hdec_enc : ∀ s : State, dec (enc s) = s := by
    intro s
    dsimp only [dec, enc]
    rw [dif_pos (e s).isLt]
    exact e.symm_apply_apply s
  let start : Fin K := enc s0
  let step : Fin n → Fin K → Row → Fin K := fun pos k r => enc (stepS pos (dec k) r)
  let out : Fin K → Bool × Bool := fun k => outS (dec k)
  refine ⟨start, step, out, ?_⟩
  intro raw
  have hfold : ∀ (L : List (Fin n)) (s : State),
      L.foldl (fun st pos => step pos st (raw pos)) (enc s) =
        enc (L.foldl (fun st pos => stepS pos st (raw pos)) s) := by
    intro L
    induction L with
    | nil =>
      intro s
      rfl
    | cons pos tl ih =>
      intro s
      simp only [List.foldl_cons, step, hdec_enc]
      exact ih (stepS pos s (raw pos))
  show out ((List.finRange n).foldl (fun st pos => step pos st (raw pos)) (enc s0)) = _
  rw [hfold (List.finRange n) s0]
  dsimp only [out]
  rw [hdec_enc]

lemma foldl_mask_spec {n w : ℕ} (hn : 0 < n) (raw : Fin n → (Fin (w + 1) → Bool) → Bool)
    (L : List (Fin n)) (st : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (L.foldl (fun acc pos => fun y => acc y && raw pos (fun j => y ⟨(pos.val + j.val) % n, Nat.mod_lt _ hn⟩)) st) x = true ↔
      st x = true ∧ ∀ i ∈ L, raw i (fun j => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true := by
  induction L generalizing st with
  | nil =>
    simp
  | cons a tl ih =>
    simp only [List.foldl_cons, ih, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, and_assoc]

lemma foldl_update_of_not_mem {n : ℕ} {Row : Type} (raw : Fin n → Row)
    (L : List (Fin n)) (st : Fin n → Row) (i : Fin n) (hi : i ∉ L) :
    (L.foldl (fun acc pos => Function.update acc pos (raw pos)) st) i = st i := by
  induction L generalizing st with
  | nil =>
    rfl
  | cons a tl ih =>
    simp only [List.mem_cons, not_or] at hi
    simp only [List.foldl_cons]
    rw [ih (Function.update st a (raw a)) hi.2]
    exact Function.update_of_ne hi.1 _ _

lemma foldl_update_of_mem {n : ℕ} {Row : Type} (raw : Fin n → Row)
    (L : List (Fin n)) (st : Fin n → Row) (i : Fin n) (hi : i ∈ L) :
    (L.foldl (fun acc pos => Function.update acc pos (raw pos)) st) i = raw i := by
  induction L generalizing st with
  | nil =>
    cases hi
  | cons a tl ih =>
    simp only [List.foldl_cons]
    by_cases htl : i ∈ tl
    · exact ih (Function.update st a (raw a)) htl
    · simp only [List.mem_cons] at hi
      have hia : i = a := hi.resolve_right htl
      rw [foldl_update_of_not_mem raw tl (Function.update st a (raw a)) i htl, hia, Function.update_self]

def snocPat {w : ℕ} (p : Fin w → Bool) (bit : Bool) : Fin (w + 1) → Bool :=
  fun j => if hj : j.val < w then p ⟨j.val, hj⟩ else bit

def stepNatMat {w : ℕ} (row : (Fin (w + 1) → Bool) → Bool) :
    Matrix (Fin w → Bool) (Fin w → Bool) ℕ :=
  Matrix.of fun p q =>
    (Finset.univ.filter fun bit : Bool =>
      row (snocPat p bit) = true ∧ PEqualNP.Outside.L_lib_377.nx p bit = q).card

def toBoolMat {α : Type} (M : Matrix α α ℕ) : Matrix α α Bool :=
  fun p q => decide (0 < M p q)

def idBoolMat {α : Type} [DecidableEq α] : Matrix α α Bool :=
  fun p q => decide (p = q)

def boolMatMul {α : Type} [Fintype α] (A B : Matrix α α Bool) : Matrix α α Bool :=
  fun p q => decide (∃ r : α, A p r = true ∧ B r q = true)

def toZ2Mat {α : Type} (M : Matrix α α ℕ) : Matrix α α (ZMod 2) :=
  M.map (Nat.cast : ℕ → ZMod 2)

lemma toBoolMat_one {α : Type} [DecidableEq α] :
    toBoolMat (1 : Matrix α α ℕ) = idBoolMat := by
  funext p q
  by_cases h : p = q <;> simp [toBoolMat, idBoolMat, Matrix.one_apply, h]

lemma toBoolMat_mul {α : Type} [Fintype α] (A B : Matrix α α ℕ) :
    toBoolMat (A * B) = boolMatMul (toBoolMat A) (toBoolMat B) := by
  funext p q
  apply Bool.eq_iff_iff.mpr
  simp only [toBoolMat, boolMatMul, decide_eq_true_eq, Matrix.mul_apply,
    Nat.pos_iff_ne_zero, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ, true_imp_iff,
    not_forall, mul_eq_zero, not_or]

lemma trace_pos_iff_exists_bool {α : Type} [Fintype α] (P : Matrix α α ℕ) :
    decide (∃ p : α, toBoolMat P p p = true) = decide (0 < Matrix.trace P) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, toBoolMat, Matrix.trace, Matrix.diag,
    Nat.pos_iff_ne_zero, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ, true_imp_iff,
    not_forall]

lemma toZ2Mat_one {α : Type} [DecidableEq α] :
    toZ2Mat (1 : Matrix α α ℕ) = (1 : Matrix α α (ZMod 2)) := by
  funext p q
  by_cases h : p = q <;> simp [toZ2Mat, Matrix.one_apply, h]

lemma toZ2Mat_mul {α : Type} [Fintype α] (A B : Matrix α α ℕ) :
    toZ2Mat (A * B) = toZ2Mat A * toZ2Mat B := by
  funext p q
  simp only [toZ2Mat, Matrix.map_apply, Matrix.mul_apply, Nat.cast_sum, Nat.cast_mul]

lemma foldl_pair_spec {α : Type} [Fintype α] [DecidableEq α]
    (L : List (Matrix α α ℕ)) (acc : Matrix α α ℕ) :
    L.foldl (fun st M => (boolMatMul st.1 (toBoolMat M), st.2 * toZ2Mat M))
      (toBoolMat acc, toZ2Mat acc) =
      (toBoolMat (L.foldl (· * ·) acc), toZ2Mat (L.foldl (· * ·) acc)) := by
  induction L generalizing acc with
  | nil =>
    rfl
  | cons M tl ih =>
    simp only [List.foldl_cons, ← toBoolMat_mul, ← toZ2Mat_mul]
    exact ih (acc * M)

lemma foldl_mul_eq_mul_prod {G : Type} [Monoid G] (L : List G) (acc : G) :
    L.foldl (· * ·) acc = acc * L.prod := by
  induction L generalizing acc with
  | nil =>
    simp
  | cons a tl ih =>
    simp only [List.foldl_cons, List.prod_cons, ih, mul_assoc]

lemma map_finRange_eq_ofFn {n : ℕ} {α : Type} (f : Fin n → α) :
    (List.finRange n).map f = List.ofFn f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

lemma testBit_zero_eq_decide_zmod2 (c : ℕ) :
    c.testBit 0 = decide ((c : ZMod 2) = 1) := by
  rw [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
  · have hdiv : c = 2 * (c / 2) := by omega
    have hz : (c : ZMod 2) = 0 := by
      rw [hdiv]
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]
    rw [h0, hz]
    decide
  · have hdiv : c = 2 * (c / 2) + 1 := by omega
    have hz : (c : ZMod 2) = 1 := by
      rw [hdiv]
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul, zero_add]
    rw [h1, hz]
    decide

lemma trace_stepNatMat_eq_total (t w : ℕ)
    (raw : Fin (t + 1) → (Fin (w + 1) → Bool) → Bool) :
    Matrix.trace (List.ofFn (fun i : Fin (t + 1) => stepNatMat (raw i))).prod =
      ((Finset.univ : Finset (Fin (t + 1) → Bool)).filter (fun x =>
        ∀ i : Fin (t + 1), raw i (fun j => x ⟨(i.val + j.val) % (t + 1), Nat.mod_lt _ (Nat.succ_pos t)⟩) = true)).card := by
  let test : Fin (t + 1) → (Fin w → Bool) → Bool → Bool := fun i p bit => raw i (snocPat p bit)
  have h377 := PEqualNP.Outside.L_lib_377 t w test
  dsimp only at h377
  have hstep : (fun i : Fin (t + 1) => stepNatMat (raw i)) =
      fun i : Fin (t + 1) =>
        (Matrix.of (fun p q : Fin w → Bool =>
          (Finset.univ.filter (fun bit : Bool =>
            test i p bit = true ∧
              (fun (state : Fin w → Bool) (b : Bool) (j : Fin w) =>
                if h : j.val + 1 < w then state ⟨j.val + 1, h⟩ else b) p bit = q)).card) :
          Matrix (Fin w → Bool) (Fin w → Bool) ℕ) := rfl
  rw [hstep, h377]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall_congr'
  intro a
  have hpat : snocPat (fun pos : Fin w => x (Fin.ofNat (t + 1) (a.val + pos.val)))
      (x (Fin.ofNat (t + 1) (a.val + w))) =
      fun j : Fin (w + 1) => x ⟨(a.val + j.val) % (t + 1), Nat.mod_lt _ (Nat.succ_pos t)⟩ := by
    funext j
    dsimp only [snocPat]
    by_cases hj : j.val < w
    · simp only [hj, ↓reduceDIte]
      congr 1
    · simp only [hj, ↓reduceDIte]
      have hjw : j.val = w := by omega
      rw [hjw]
      congr 1
  simp only [test, hpat]

lemma conj1 (n w : ℕ) (hn : 0 < n) (hw : 0 < w) :
    let D := 2 ^ w
    let B := min (2 ^ n) (min (n * D) (D * D))
    let Pat := Fin (w + 1) → Bool
    let Row := Pat → Bool
    let Tab := Fin n → Row
    let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
    let total := fun (table : Tab) =>
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ∀ i : Fin n, table i (fun j => x (loc (i.val + j.val))) = true)).card
    ∃ (start : Fin (2 ^ (2 * B))) (step : Fin n → Fin (2 ^ (2 * B)) → Row → Fin (2 ^ (2 * B)))
      (out : Fin (2 ^ (2 * B)) → Bool × Bool), ∀ raw : Tab,
      out ((List.finRange n).foldl (fun st pos => step pos st (raw pos)) start) =
        (decide (0 < total raw), (total raw).testBit 0) := by
  intro D B Pat Row Tab loc total
  rcases le_total (2 ^ n) (min (n * D) (D * D)) with h1 | h1
  · have hB : B = 2 ^ n := min_eq_left h1
    let State := (Fin n → Bool) → Bool
    have hcard : Fintype.card State ≤ 2 ^ (2 * B) := by
      have hc : Fintype.card State = 2 ^ (2 ^ n) := by
        simp [State, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      rw [hc, hB]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    let s0 : State := fun _ => true
    let stepS : Fin n → State → Row → State :=
      fun pos st row => fun x => st x && row (fun j => x (loc (pos.val + j.val)))
    let outS : State → Bool × Bool := fun st =>
      let c := ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => st x = true)).card
      (decide (0 < c), c.testBit 0)
    obtain ⟨start, step, out, hout⟩ := encode_automaton s0 stepS outS hcard
    refine ⟨start, step, out, ?_⟩
    intro raw
    rw [hout raw]
    dsimp only [outS]
    have hfilt : ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ((List.finRange n).foldl (fun st pos => stepS pos st (raw pos)) s0) x = true)) =
        ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
          ∀ i : Fin n, raw i (fun j => x (loc (i.val + j.val))) = true)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hspec := foldl_mask_spec hn raw (List.finRange n) s0 x
      simpa [stepS, s0, loc, List.mem_finRange] using hspec
    rw [hfilt]
  · rcases le_total (n * D) (D * D) with h2 | h2
    · have hB : B = n * D := by
        change min (2 ^ n) (min (n * D) (D * D)) = n * D
        rw [min_eq_right h1, min_eq_left h2]
      have hcard : Fintype.card Tab ≤ 2 ^ (2 * B) := by
        have hc : Fintype.card Tab = 2 ^ (2 ^ (w + 1) * n) := by
          simp [Tab, Row, Pat, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul]
        rw [hc, hB]
        have hexp : 2 ^ (w + 1) * n = 2 * (n * D) := by
          dsimp only [D]
          rw [pow_succ]
          ring
        rw [hexp]
      let s0 : Tab := fun _ _ => false
      let stepS : Fin n → Tab → Row → Tab := fun pos st row => Function.update st pos row
      let outS : Tab → Bool × Bool := fun st => (decide (0 < total st), (total st).testBit 0)
      obtain ⟨start, step, out, hout⟩ := encode_automaton s0 stepS outS hcard
      refine ⟨start, step, out, ?_⟩
      intro raw
      rw [hout raw]
      have heq : (List.finRange n).foldl (fun st pos => stepS pos st (raw pos)) s0 = raw := by
        funext i
        exact foldl_update_of_mem raw (List.finRange n) s0 i (List.mem_finRange i)
      dsimp only [outS]
      rw [heq]
    · have hB : B = D * D := by
        change min (2 ^ n) (min (n * D) (D * D)) = D * D
        rw [min_eq_right h1, min_eq_right h2]
      let WState := Fin w → Bool
      let State := Matrix WState WState Bool × Matrix WState WState (ZMod 2)
      have hcardW : Fintype.card WState = D := by
        simp [WState, D, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      have hcard : Fintype.card State ≤ 2 ^ (2 * B) := by
        have hc1 : Fintype.card (Matrix WState WState Bool) = 2 ^ (D * D) := by
          rw [← Fintype.card_congr Matrix.of]
          simp [Fintype.card_fun, Fintype.card_bool, hcardW, ← pow_mul]
        have hc2 : Fintype.card (Matrix WState WState (ZMod 2)) = 2 ^ (D * D) := by
          rw [← Fintype.card_congr Matrix.of]
          simp [Fintype.card_fun, ZMod.card, hcardW, ← pow_mul]
        have hc : Fintype.card State = 2 ^ (2 * (D * D)) := by
          simp only [State, Fintype.card_prod, hc1, hc2, ← pow_add]
          congr 1
          ring
        rw [hc, hB]
      let s0 : State := (idBoolMat, (1 : Matrix WState WState (ZMod 2)))
      let stepS : Fin n → State → Row → State := fun _ st row =>
        let M := stepNatMat row
        (boolMatMul st.1 (toBoolMat M), st.2 * toZ2Mat M)
      let outS : State → Bool × Bool := fun st =>
        (decide (∃ p : WState, st.1 p p = true), decide (Matrix.trace st.2 = 1))
      obtain ⟨start, step, out, hout⟩ := encode_automaton s0 stepS outS hcard
      refine ⟨start, step, out, ?_⟩
      intro raw
      rw [hout raw]
      have hfold_pair :
          (List.finRange n).foldl (fun st pos => stepS pos st (raw pos)) s0 =
            (toBoolMat (List.ofFn (fun i : Fin n => stepNatMat (raw i))).prod,
             toZ2Mat (List.ofFn (fun i : Fin n => stepNatMat (raw i))).prod) := by
        have hs0 : s0 = (toBoolMat (1 : Matrix WState WState ℕ), toZ2Mat (1 : Matrix WState WState ℕ)) := by
          simp only [s0, toBoolMat_one, toZ2Mat_one]
        rw [hs0]
        have hmap : (List.finRange n).foldl (fun st pos => stepS pos st (raw pos))
            (toBoolMat (1 : Matrix WState WState ℕ), toZ2Mat (1 : Matrix WState WState ℕ)) =
            ((List.finRange n).map (fun pos => stepNatMat (raw pos))).foldl
              (fun st M => (boolMatMul st.1 (toBoolMat M), st.2 * toZ2Mat M))
              (toBoolMat (1 : Matrix WState WState ℕ), toZ2Mat (1 : Matrix WState WState ℕ)) := by
          rw [List.foldl_map]
        rw [hmap, foldl_pair_spec, foldl_mul_eq_mul_prod, one_mul, map_finRange_eq_ofFn]
      rw [hfold_pair]
      have htrace_eq : Matrix.trace (List.ofFn (fun i : Fin n => stepNatMat (raw i))).prod = total raw := by
        obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
        exact trace_stepNatMat_eq_total t w raw
      dsimp only [outS]
      rw [← htrace_eq]
      apply Prod.ext
      · exact trace_pos_iff_exists_bool (List.ofFn (fun i : Fin n => stepNatMat (raw i))).prod
      · rw [testBit_zero_eq_decide_zmod2]
        have htr : Matrix.trace (toZ2Mat (List.ofFn (fun i : Fin n => stepNatMat (raw i))).prod) =
            ((Matrix.trace (List.ofFn (fun i : Fin n => stepNatMat (raw i))).prod : ℕ) : ZMod 2) := by
          simp only [Matrix.trace, Matrix.diag, toZ2Mat, Matrix.map_apply, Nat.cast_sum]
        rw [htr]

lemma length_filter_finRange {R : ℕ} (p : Fin R → Bool) :
    ((List.finRange R).filter p).length =
      ((Finset.univ : Finset (Fin R)).filter (fun c => p c = true)).card := by
  have hnd : ((List.finRange R).filter p).Nodup := (List.nodup_finRange R).filter p
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext c
  simp [List.mem_finRange]

def hdist {M : ℕ} (u x : Fin M → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin M)).filter (fun a => u a ≠ x a)).card

lemma hdist_cons {M : ℕ} (u : Fin (M + 1) → Bool) (b : Bool) (xs : Fin M → Bool) :
    hdist u (Fin.cons b xs) = (if u 0 ≠ b then 1 else 0) + hdist (Fin.tail u) xs := by
  unfold hdist
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  rfl

lemma sum_pow_hdist {M : ℕ} (q : ℚ) (u : Fin M → Bool) :
    ∑ x : Fin M → Bool, q ^ hdist u x = (1 + q) ^ M := by
  induction M with
  | zero =>
    have huniq : ∀ x : Fin 0 → Bool, hdist u x = 0 := by
      intro x
      simp [hdist]
    simp [huniq]
  | succ M ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (M + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
    have hstep : ∀ b : Bool,
        ∑ xs : Fin M → Bool, q ^ hdist u (Fin.cons b xs) =
          q ^ (if u 0 ≠ b then 1 else 0) * (1 + q) ^ M := by
      intro b
      simp_rw [hdist_cons, pow_add, ← Finset.mul_sum, ih]
    simp_rw [Fin.consEquiv_apply, hstep, ← Finset.sum_mul]
    rw [pow_succ']
    congr 1
    cases u 0 <;> simp [Fintype.sum_bool] <;> ring

lemma bernoulli_nat (δ : ℚ) (hδ : 0 ≤ δ) : ∀ n : ℕ, 1 + (n : ℚ) * δ ≤ (1 + δ) ^ n := by
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h1 : 0 ≤ 1 + δ := by linarith
    have h2 : (1 + (n : ℚ) * δ) * (1 + δ) ≤ (1 + δ) ^ n * (1 + δ) :=
      mul_le_mul_of_nonneg_right ih h1
    have h3 : 0 ≤ (n : ℚ) * (δ * δ) := mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hδ hδ)
    rw [pow_succ]
    push_cast
    linarith

lemma neg_bernoulli_mul (δ : ℚ) (hδ : 0 ≤ δ) : ∀ n : ℕ, (1 - (n : ℚ) * δ) * (1 + δ) ^ n ≤ 1 := by
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    by_cases hneg : 1 - ((n + 1 : ℕ) : ℚ) * δ ≤ 0
    · have hpos : 0 ≤ (1 + δ) ^ (n + 1) := pow_nonneg (by linarith) _
      exact le_trans (mul_nonpos_of_nonpos_of_nonneg hneg hpos) (by norm_num)
    · have hstep : (1 - ((n + 1 : ℕ) : ℚ) * δ) * (1 + δ) ≤ 1 - (n : ℚ) * δ := by
        have hsq : 0 ≤ ((n + 1 : ℕ) : ℚ) * (δ * δ) :=
          mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hδ hδ)
        push_cast at hsq ⊢
        linarith
      have hpow : 0 ≤ (1 + δ) ^ n := pow_nonneg (by linarith) _
      calc (1 - ((n + 1 : ℕ) : ℚ) * δ) * (1 + δ) ^ (n + 1)
          = ((1 - ((n + 1 : ℕ) : ℚ) * δ) * (1 + δ)) * (1 + δ) ^ n := by rw [pow_succ]; ring
        _ ≤ (1 - (n : ℚ) * δ) * (1 + δ) ^ n := mul_le_mul_of_nonneg_right hstep hpow
        _ ≤ 1 := ih

lemma bernoulli_zpow (δ : ℚ) (hδ : 0 ≤ δ) (k : ℤ) : 1 + (k : ℚ) * δ ≤ (1 + δ) ^ k := by
  cases k with
  | ofNat n =>
    simpa using bernoulli_nat δ hδ n
  | negSucc m =>
    have hpos : 0 < (1 + δ) ^ (m + 1) := pow_pos (by linarith) _
    rw [zpow_negSucc, inv_eq_one_div, le_div_iff₀ hpos]
    have h := neg_bernoulli_mul δ hδ (m + 1)
    rw [Int.cast_negSucc]
    push_cast at h ⊢
    linarith

lemma coding_bound {M S : ℕ} (msg : (Fin M → Bool) → Fin S) (pred : Fin S → (Fin M → Bool))
    (herr : 3 * ∑ x : Fin M → Bool, hdist (pred (msg x)) x ≤ M * 2 ^ M) :
    2 ^ M ≤ S ^ 15 := by
  let d : (Fin M → Bool) → ℕ := fun x => hdist (pred (msg x)) x
  have hcardB : (Finset.univ : Finset (Fin M → Bool)).card = 2 ^ M := by
    simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hzpow_eq : ∀ x : Fin M → Bool,
      (5 / 4 : ℚ) ^ ((M : ℤ) - 3 * (d x : ℤ)) = (5 / 4 : ℚ) ^ M * (64 / 125 : ℚ) ^ (d x) := by
    intro x
    rw [zpow_sub₀ (by norm_num), zpow_natCast, div_eq_mul_inv]
    congr 1
    rw [show (3 : ℤ) * (d x : ℤ) = ((3 * d x : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul, ← inv_pow]
    norm_num
  have hterm : ∀ x : Fin M → Bool,
      1 + ((M : ℚ) - 3 * (d x : ℚ)) * (1 / 4) ≤ (5 / 4 : ℚ) ^ M * (64 / 125 : ℚ) ^ (d x) := by
    intro x
    have hb := bernoulli_zpow (1 / 4 : ℚ) (by norm_num) ((M : ℤ) - 3 * (d x : ℤ))
    have h54 : (1 + 1 / 4 : ℚ) = 5 / 4 := by norm_num
    rw [h54, hzpow_eq x] at hb
    push_cast at hb
    exact hb
  have hsum_lb : (2 : ℚ) ^ M ≤ (5 / 4 : ℚ) ^ M * ∑ x : Fin M → Bool, (64 / 125 : ℚ) ^ (d x) := by
    have hsum1 : ∑ x : Fin M → Bool, (1 + ((M : ℚ) - 3 * (d x : ℚ)) * (1 / 4)) ≤
        ∑ x : Fin M → Bool, (5 / 4 : ℚ) ^ M * (64 / 125 : ℚ) ^ (d x) :=
      Finset.sum_le_sum (fun x _ => hterm x)
    rw [← Finset.mul_sum] at hsum1
    have herrQ : 3 * ∑ x : Fin M → Bool, (d x : ℚ) ≤ (M : ℚ) * (2 : ℚ) ^ M := by
      exact_mod_cast herr
    have hlhs : ∑ x : Fin M → Bool, (1 + ((M : ℚ) - 3 * (d x : ℚ)) * (1 / 4)) =
        (2 : ℚ) ^ M + ((M : ℚ) * (2 : ℚ) ^ M - 3 * ∑ x : Fin M → Bool, (d x : ℚ)) * (1 / 4) := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
        Finset.sum_const, hcardB, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
      push_cast
      ring
    linarith
  have hsum_ub : ∑ x : Fin M → Bool, (64 / 125 : ℚ) ^ (d x) ≤ (S : ℚ) * (189 / 125 : ℚ) ^ M := by
    calc ∑ x : Fin M → Bool, (64 / 125 : ℚ) ^ (d x)
        ≤ ∑ x : Fin M → Bool, ∑ m : Fin S, (64 / 125 : ℚ) ^ hdist (pred m) x := by
          refine Finset.sum_le_sum (fun x _ => ?_)
          exact Finset.single_le_sum (f := fun m : Fin S => (64 / 125 : ℚ) ^ hdist (pred m) x)
            (fun m _ => pow_nonneg (by norm_num) _) (Finset.mem_univ (msg x))
      _ = ∑ m : Fin S, ∑ x : Fin M → Bool, (64 / 125 : ℚ) ^ hdist (pred m) x := Finset.sum_comm
      _ = ∑ _m : Fin S, (1 + 64 / 125 : ℚ) ^ M := by
          refine Finset.sum_congr rfl (fun m _ => sum_pow_hdist (64 / 125 : ℚ) (pred m))
      _ = (S : ℚ) * (189 / 125 : ℚ) ^ M := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hcomb : (2 : ℚ) ^ M ≤ (5 / 4 : ℚ) ^ M * ((S : ℚ) * (189 / 125 : ℚ) ^ M) :=
    le_trans hsum_lb (mul_le_mul_of_nonneg_left hsum_ub (pow_nonneg (by norm_num) M))
  have h200Q : ((200 ^ M : ℕ) : ℚ) ≤ ((S * 189 ^ M : ℕ) : ℚ) := by
    have hmul := mul_le_mul_of_nonneg_left hcomb (pow_nonneg (by norm_num : (0 : ℚ) ≤ 100) M)
    have hl : (100 : ℚ) ^ M * (2 : ℚ) ^ M = ((200 ^ M : ℕ) : ℚ) := by
      rw [← mul_pow]
      push_cast
      norm_num
    have hr : (100 : ℚ) ^ M * ((5 / 4 : ℚ) ^ M * ((S : ℚ) * (189 / 125 : ℚ) ^ M)) =
        ((S * 189 ^ M : ℕ) : ℚ) := by
      have h1 : (100 : ℚ) ^ M * ((5 / 4 : ℚ) ^ M * ((S : ℚ) * (189 / 125 : ℚ) ^ M)) =
          (S : ℚ) * (((100 : ℚ) * (5 / 4) * (189 / 125)) ^ M) := by
        rw [mul_pow, mul_pow]
        ring
      rw [h1]
      have h189 : (100 : ℚ) * (5 / 4) * (189 / 125) = 189 := by norm_num
      rw [h189]
      push_cast
      rfl
    linarith
  have h200 : 200 ^ M ≤ S * 189 ^ M := by exact_mod_cast h200Q
  have hpow15 : (200 ^ M) ^ 15 ≤ (S * 189 ^ M) ^ 15 := Nat.pow_le_pow_left h200 15
  have hnum : 2 * 189 ^ 15 ≤ 200 ^ 15 := by norm_num
  have h2M : 2 ^ M * (189 ^ 15) ^ M ≤ S ^ 15 * (189 ^ 15) ^ M := by
    calc 2 ^ M * (189 ^ 15) ^ M
        = (2 * 189 ^ 15) ^ M := (mul_pow _ _ _).symm
      _ ≤ (200 ^ 15) ^ M := Nat.pow_le_pow_left hnum M
      _ = (200 ^ M) ^ 15 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (S * 189 ^ M) ^ 15 := hpow15
      _ = S ^ 15 * (189 ^ 15) ^ M := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm M 15]
  exact Nat.le_of_mul_le_mul_right h2M (by positivity)

lemma conj2 (n w : ℕ) (hn : 0 < n) (hw : 0 < w) :
    let D := 2 ^ w
    let B := min (2 ^ n) (min (n * D) (D * D))
    let cut := max 1 (min (n - 1) (max w (n - w)))
    let Pat := Fin (w + 1) → Bool
    let Row := Pat → Bool
    let Tab := Fin n → Row
    let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
    let total := fun (table : Tab) =>
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ∀ i : Fin n, table i (fun j => x (loc (i.val + j.val))) = true)).card
    ∀ (S R : Nat), 0 < R →
      ∀ (send : Fin R → Tab → Fin S) (answer : Fin R → Fin S → Tab → Bool),
        (∀ left right : Tab,
          let C := total (fun i => if i.val < cut then left i else right i)
          C ≤ 1 → 2 * R ≤ 3 * ((List.finRange R).filter (fun coin =>
            answer coin (send coin left) right == decide (C = 1))).length) →
        2 ^ B ≤ S ^ 960 := by
  intro D B cut Pat Row Tab loc total S R hR send answer hproto
  obtain ⟨M, base, port, query, hBM, _hport_inj, _hport_cut, hcount⟩ :=
    PEqualNP.Outside.L_lib_871 n w hn hw
  let enabled : (Fin M → Bool) → Finset (Fin M) :=
    fun x => Finset.univ.filter (fun b => x b = true)
  let leftTab : (Fin M → Bool) → Tab :=
    fun x i pat => base i pat || decide ((i, pat) ∈ (enabled x).image port)
  have hpair : ∀ (x : Fin M → Bool) (addr : Fin M),
      3 * ((Finset.univ : Finset (Fin R)).filter (fun coin =>
        answer coin (send coin (leftTab x)) (query addr) ≠ x addr)).card ≤ R := by
    intro x addr
    have htab_eq : (fun i : Fin n => if i.val < cut then leftTab x i else query addr i) =
        fun i pat => if i.val < cut then
          (base i pat || decide ((i, pat) ∈ (enabled x).image port)) else query addr i pat := by
      funext i pat
      split_ifs <;> rfl
    have hC : total (fun i => if i.val < cut then leftTab x i else query addr i) =
        if x addr = true then 1 else 0 := by
      rw [htab_eq]
      have hc : total (fun i pat => if i.val < cut then
          (base i pat || decide ((i, pat) ∈ (enabled x).image port)) else query addr i pat) =
          if addr ∈ enabled x then 1 else 0 := hcount (enabled x) addr
      have hmem : addr ∈ enabled x ↔ x addr = true := by
        simp [enabled]
      rw [hc]
      by_cases hx : x addr = true
      · have hm : addr ∈ enabled x := hmem.mpr hx
        simp [hx, hm]
      · have hm : addr ∉ enabled x := fun h => hx (hmem.mp h)
        simp [hx, hm]
    have hCle1 : total (fun i => if i.val < cut then leftTab x i else query addr i) ≤ 1 := by
      rw [hC]
      split_ifs <;> omega
    have hdec : decide (total (fun i => if i.val < cut then leftTab x i else query addr i) = 1) = x addr := by
      rw [hC]
      cases x addr <;> simp
    have hp := hproto (leftTab x) (query addr) hCle1
    rw [hdec, length_filter_finRange] at hp
    have hgood_eq :
        ((Finset.univ : Finset (Fin R)).filter (fun coin =>
          (answer coin (send coin (leftTab x)) (query addr) == x addr) = true)).card =
        ((Finset.univ : Finset (Fin R)).filter (fun coin =>
          answer coin (send coin (leftTab x)) (query addr) = x addr)).card := by
      apply congrArg Finset.card
      ext coin
      simp [beq_iff_eq]
    rw [hgood_eq] at hp
    have hpart :
        ((Finset.univ : Finset (Fin R)).filter (fun coin =>
          answer coin (send coin (leftTab x)) (query addr) = x addr)).card +
        ((Finset.univ : Finset (Fin R)).filter (fun coin =>
          answer coin (send coin (leftTab x)) (query addr) ≠ x addr)).card = R := by
      simp only [Finset.card_filter, ← Finset.sum_add_distrib]
      have h1 : ∀ coin : Fin R,
          (if answer coin (send coin (leftTab x)) (query addr) = x addr then 1 else 0) +
          (if answer coin (send coin (leftTab x)) (query addr) ≠ x addr then 1 else 0) = 1 := by
        intro coin
        by_cases h : answer coin (send coin (leftTab x)) (query addr) = x addr <;> simp [h]
      rw [Finset.sum_congr rfl (fun coin _ => h1 coin)]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    omega
  let err : Fin R → ℕ := fun coin =>
    ∑ x : Fin M → Bool, hdist (fun addr => answer coin (send coin (leftTab x)) (query addr)) x
  have hsum_err : 3 * ∑ coin : Fin R, err coin ≤ R * (M * 2 ^ M) := by
    have hswap : ∑ coin : Fin R, err coin =
        ∑ x : Fin M → Bool, ∑ addr : Fin M,
          ((Finset.univ : Finset (Fin R)).filter (fun coin =>
            answer coin (send coin (leftTab x)) (query addr) ≠ x addr)).card := by
      simp only [err, hdist, Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_comm]
    rw [hswap, Finset.mul_sum]
    calc ∑ x : Fin M → Bool, 3 * ∑ addr : Fin M,
            ((Finset.univ : Finset (Fin R)).filter (fun coin =>
              answer coin (send coin (leftTab x)) (query addr) ≠ x addr)).card
        = ∑ x : Fin M → Bool, ∑ addr : Fin M,
            3 * ((Finset.univ : Finset (Fin R)).filter (fun coin =>
              answer coin (send coin (leftTab x)) (query addr) ≠ x addr)).card := by
          refine Finset.sum_congr rfl (fun x _ => Finset.mul_sum _ _ _)
      _ ≤ ∑ _x : Fin M → Bool, ∑ _addr : Fin M, R := by
          refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun addr _ => hpair x addr))
      _ = R * (M * 2 ^ M) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, smul_eq_mul]
          ring
  have hne : (Finset.univ : Finset (Fin R)).Nonempty := ⟨⟨0, hR⟩, Finset.mem_univ _⟩
  obtain ⟨coin0, _, hmin⟩ := Finset.exists_min_image Finset.univ err hne
  have herr0 : 3 * err coin0 ≤ M * 2 ^ M := by
    have hle : R * err coin0 ≤ ∑ coin : Fin R, err coin := by
      calc R * err coin0
          = ∑ _coin : Fin R, err coin0 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ ∑ coin : Fin R, err coin := Finset.sum_le_sum (fun coin _ => hmin coin (Finset.mem_univ _))
    have hmul : R * (3 * err coin0) ≤ R * (M * 2 ^ M) := by
      calc R * (3 * err coin0) = 3 * (R * err coin0) := by ring
        _ ≤ 3 * ∑ coin : Fin R, err coin := Nat.mul_le_mul_left 3 hle
        _ ≤ R * (M * 2 ^ M) := hsum_err
    exact Nat.le_of_mul_le_mul_left hmul hR
  have h2M : 2 ^ M ≤ S ^ 15 :=
    coding_bound (fun x => send coin0 (leftTab x)) (fun m addr => answer coin0 m (query addr)) herr0
  calc 2 ^ B ≤ 2 ^ (64 * M) := Nat.pow_le_pow_right (by omega) hBM
    _ = (2 ^ M) ^ 64 := by rw [← pow_mul, mul_comm]
    _ ≤ (S ^ 15) ^ 64 := Nat.pow_le_pow_left h2M 64
    _ = S ^ 960 := by rw [← pow_mul]

end PEqualNP.Outside.L_clb_121_aux

theorem PEqualNP.Outside.L_clb_121 : (∀ (n w : Nat) (hn : 0 < n), 0 < w →
  let D := 2^w
  let B := min (2^n) (min (n*D) (D*D))
  let cut := max 1 (min (n-1) (max w (n-w)))
  let Pat := Fin (w+1) → Bool
  let Row := Pat → Bool
  let Tab := Fin n → Row
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let total := fun (table : Tab) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      ∀ i : Fin n, table i (fun j => x (loc (i.val+j.val))) = true)).card
  (∃ (start : Fin (2^(2*B))) (step : Fin n → Fin (2^(2*B)) → Row → Fin (2^(2*B)))
      (out : Fin (2^(2*B)) → Bool × Bool), ∀ raw : Tab,
      out ((List.finRange n).foldl (fun st pos => step pos st (raw pos)) start) =
        (decide (0 < total raw), (total raw).testBit 0)) ∧
    ∀ (S R : Nat), 0 < R →
      ∀ (send : Fin R → Tab → Fin S) (answer : Fin R → Fin S → Tab → Bool),
        (∀ left right : Tab,
          let C := total (fun i => if i.val < cut then left i else right i)
          C ≤ 1 → 2*R ≤ 3*((List.finRange R).filter (fun coin =>
            answer coin (send coin left) right == decide (C = 1))).length) →
        2^B ≤ S^960) := by
  intro n w hn hw
  exact ⟨PEqualNP.Outside.L_clb_121_aux.conj1 n w hn hw,
    PEqualNP.Outside.L_clb_121_aux.conj2 n w hn hw⟩
