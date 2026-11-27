import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_377

namespace PEqualNP.Outside.L_clb_089_aux

private abbrev Row := Nat → Bool

private theorem ite_eq_of_iff {α : Type*} {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) (a b : α) : (if P then a else b) = (if Q then a else b) := by
  by_cases hp : P
  · simp [hp, h.mp hp]
  · have hq : ¬ Q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

private def patAt (w n word site : Nat) : Nat :=
  (List.range (w + 1)).foldl (fun (acc bit : Nat) =>
    acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0

private def totalCount (w n : Nat) (rows : Nat → Row) : Nat :=
  ((List.range (2 ^ n)).filter (fun word => (List.range n).all (fun site =>
    rows site (patAt w n word site)))).length

private def runAlg (p n S : Nat) (start : Fin S)
    (step : Nat → Nat → Fin S → Row → Fin S) (table : Nat → Row) : Fin S :=
  (List.range p).foldl (fun prev passId =>
    (List.range n).foldl (fun state siteId => step passId siteId state (table siteId)) prev) start

private def succeedsProp (w n p m S R a b : Nat) : Prop :=
  ∃ (init : Fin R → Fin S) (update : Fin R → Nat → Nat → Fin S → Row → Fin S)
    (output : Fin R → Fin S → Nat), ∀ input : Nat → Row,
      a * R ≤ b * ((List.finRange R).filter (fun coin =>
        output coin (runAlg p n S (init coin) (update coin) input) ==
          (totalCount w n input) % m)).length

private def nextSt {w : Nat} (state : Fin w → Bool) (b : Bool) (j : Fin w) : Bool :=
  if h : j.val + 1 < w then state ⟨j.val + 1, h⟩ else b

private def stateToNat {w : Nat} (st : Fin w → Bool) : Nat :=
  (List.range w).foldl (fun acc bit =>
    acc ||| ((if h : bit < w then st ⟨bit, h⟩ else false).toNat <<< bit)) 0

private def patVal {w : Nat} (st : Fin w → Bool) (b : Bool) : Nat :=
  stateToNat st ||| (b.toNat <<< w)

private def stepMat (w : Nat) (row : Row) : Matrix (Fin w → Bool) (Fin w → Bool) Nat :=
  Matrix.of (fun p q =>
    (Finset.univ.filter (fun bit : Bool =>
      row (patVal p bit) = true ∧ nextSt p bit = q)).card)

private def rowOfTest {w : Nat} (f : (Fin w → Bool) → Bool → Bool) : Row :=
  fun pat => f (fun j => pat.testBit j.val) (pat.testBit w)

private theorem foldl_bits_spec (f : Nat → Bool) :
    ∀ (k b : Nat),
      ((List.range k).foldl (fun (acc bit : Nat) => acc ||| ((f bit).toNat <<< bit)) 0).testBit b =
      if b < k then f b else false := by
  intro k
  induction k with
  | zero => intro b; simp
  | succ k ih =>
    intro b
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_or, ih b, Nat.testBit_shiftLeft]
    by_cases hbk : b < k
    · have hlt : b < k + 1 := by omega
      have hge : ¬ (k ≤ b) := by omega
      simp [hbk, hlt, hge]
    · by_cases hbe : b = k
      · subst hbe
        simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_add_one, le_refl,
          decide_true, Nat.sub_self, Bool.true_and, Bool.false_or]
        cases f b <;> decide
      · have hgt : ¬ (b < k + 1) := by omega
        have hpos : b - k ≠ 0 := by omega
        have hzero : (f k).toNat.testBit (b - k) = false := by
          cases f k
          · simp
          · simp only [Bool.toNat_true, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
            have hdiv0 : 1 / 2 ^ (b - k) = 0 := Nat.div_eq_of_lt (Nat.one_lt_two_pow hpos)
            simp [hdiv0]
        simp [hbk, hgt, hzero]

private theorem stateToNat_testBit {w : Nat} (st : Fin w → Bool) (b : Nat) :
    (stateToNat st).testBit b = if h : b < w then st ⟨b, h⟩ else false := by
  unfold stateToNat
  rw [foldl_bits_spec (fun bit => if h : bit < w then st ⟨bit, h⟩ else false) w b]
  by_cases h : b < w <;> simp [h]

private theorem stateToNat_lt {w : Nat} (st : Fin w → Bool) : stateToNat st < 2 ^ w := by
  by_contra h
  push Not at h
  have hne : stateToNat st / 2 ^ w ≠ 0 := by
    have : 0 < stateToNat st / 2 ^ w := Nat.div_pos h (by positivity)
    omega
  obtain ⟨k, hk⟩ : ∃ k, (stateToNat st / 2 ^ w).testBit k = true := by
    have hlog := Nat.testBit_log2 (n := stateToNat st / 2 ^ w) hne
    exact ⟨Nat.log2 (stateToNat st / 2 ^ w), hlog⟩
  have hbit : (stateToNat st).testBit (w + k) = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, pow_add, ← Nat.div_div_eq_div_mul]
    rw [← Nat.testBit_eq_decide_div_mod_eq]
    exact hk
  rw [stateToNat_testBit] at hbit
  have hnot : ¬ (w + k < w) := by omega
  simp [hnot] at hbit

private theorem patVal_testBit {w : Nat} (st : Fin w → Bool) (bit : Bool) (j : Nat) :
    (patVal st bit).testBit j =
      if h : j < w then st ⟨j, h⟩ else if j = w then bit else false := by
  unfold patVal
  rw [Nat.testBit_or, stateToNat_testBit, Nat.testBit_shiftLeft]
  by_cases hj : j < w
  · have hge : ¬ (w ≤ j) := by omega
    simp [hj, hge]
  · by_cases heq : j = w
    · subst heq
      simp only [lt_self_iff_false, ↓reduceDIte, ↓reduceIte, le_refl, decide_true,
        Nat.sub_self, Bool.true_and, Bool.false_or]
      cases bit <;> decide
    · have hpos : j - w ≠ 0 := by omega
      have hzero : bit.toNat.testBit (j - w) = false := by
        cases bit
        · simp
        · simp only [Bool.toNat_true, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
          have hdiv0 : 1 / 2 ^ (j - w) = 0 := Nat.div_eq_of_lt (Nat.one_lt_two_pow hpos)
          simp [hdiv0]
      simp [hj, heq, hzero]

private theorem rowOfTest_patVal {w : Nat} (f : (Fin w → Bool) → Bool → Bool)
    (st : Fin w → Bool) (bit : Bool) :
    rowOfTest f (patVal st bit) = f st bit := by
  unfold rowOfTest
  have h1 : (fun j : Fin w => (patVal st bit).testBit j.val) = st := by
    funext j
    rw [patVal_testBit]
    simp [j.isLt]
  have h2 : (patVal st bit).testBit w = bit := by
    rw [patVal_testBit]
    simp
  rw [h1, h2]

private theorem stepMat_rowOfTest {w : Nat} (f : (Fin w → Bool) → Bool → Bool) :
    stepMat w (rowOfTest f) =
      Matrix.of (fun p q =>
        (Finset.univ.filter (fun bit : Bool => f p bit = true ∧ nextSt p bit = q)).card) := by
  ext p q
  simp only [stepMat, Matrix.of_apply, rowOfTest_patVal]

private theorem list_filter_length_eq_finset_card (N : Nat) (p : Nat → Bool) :
    ((List.range N).filter p).length =
      ((Finset.univ : Finset (Fin N)).filter (fun x => p x.val = true)).card := by
  have h1 : ((List.range N).filter p).length = ((Finset.range N).filter (fun x => p x = true)).card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter p)]
    congr 1
    ext x
    simp [List.mem_range, Finset.mem_filter, Finset.mem_range]
  rw [h1]
  refine Finset.card_bij (fun x hx => ⟨x, Finset.mem_range.mp (Finset.mem_filter.mp hx).1⟩) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hx).2
  · intro x1 _ x2 _ h
    exact congrArg Fin.val h
  · intro x hx
    refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.isLt, (Finset.mem_filter.mp hx).2⟩, rfl⟩

private theorem finRange_filter_length_eq_finset_card (N : Nat) (p : Fin N → Bool) :
    ((List.finRange N).filter p).length =
      ((Finset.univ : Finset (Fin N)).filter (fun x => p x = true)).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange N).filter p)]
  congr 1
  ext x
  simp [List.mem_finRange, Finset.mem_filter]

private theorem totalCount_eq_trace (w n : Nat) (hn : 0 < n) (rows : Nat → Row) :
    totalCount w n rows =
      Matrix.trace (List.ofFn (fun i : Fin n => stepMat w (rows i.val))).prod := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  have hlib := PEqualNP.Outside.L_lib_377 t w (fun i st b => rows i.val (patVal st b))
  dsimp only at hlib
  have hstep : (fun i : Fin (t + 1) => stepMat w (rows i.val)) =
      (fun i : Fin (t + 1) =>
        (Matrix.of (fun p q : Fin w → Bool =>
          (Finset.univ.filter (fun bit : Bool =>
            rows i.val (patVal p bit) = true ∧
              (fun j : Fin w => if h : j.val + 1 < w then p ⟨j.val + 1, h⟩ else bit) = q)).card) :
          Matrix (Fin w → Bool) (Fin w → Bool) ℕ)) := by
    funext i
    rfl
  rw [hstep, hlib]
  unfold totalCount
  rw [list_filter_length_eq_finset_card (2 ^ (t + 1))]
  refine Finset.card_bij
    (fun (word : Fin (2 ^ (t + 1))) _ => fun (a : Fin (t + 1)) => word.val.testBit a.val) ?_ ?_ ?_
  · intro word hword
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hword ⊢
    rw [List.all_eq_true] at hword
    intro a
    have ha := hword a.val (List.mem_range.mpr a.isLt)
    have hpat : patVal (fun pos : Fin w => word.val.testBit (Fin.ofNat (t + 1) (a.val + pos.val)).val)
        (word.val.testBit (Fin.ofNat (t + 1) (a.val + w)).val) = patAt w (t + 1) word.val a.val := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [patVal_testBit, patAt, foldl_bits_spec]
      by_cases h1 : j < w
      · have h2 : j < w + 1 := by omega
        simp only [h1, ↓reduceDIte, h2, ↓reduceIte, Fin.val_ofNat]
      · by_cases h2 : j = w
        · subst h2
          simp only [lt_self_iff_false, ↓reduceDIte, ↓reduceIte, Nat.lt_add_one, Fin.val_ofNat]
        · have h3 : ¬ (j < w + 1) := by omega
          simp [h1, h2, h3]
    rw [hpat]
    exact ha
  · intro w1 _ w2 _ h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < t + 1
    · exact congrFun h ⟨j, hj⟩
    · have h1 : w1.val.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le w1.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      have h2 : w2.val.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le w2.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [h1, h2]
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine ⟨⟨stateToNat v, stateToNat_lt v⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [List.all_eq_true]
      intro site hsite
      have hsite' : site < t + 1 := List.mem_range.mp hsite
      have ha := hv ⟨site, hsite'⟩
      have hpat : patAt w (t + 1) (stateToNat v) site =
          patVal (fun pos : Fin w => v (Fin.ofNat (t + 1) (site + pos.val)))
            (v (Fin.ofNat (t + 1) (site + w))) := by
        apply Nat.eq_of_testBit_eq
        intro j
        rw [patAt, foldl_bits_spec, patVal_testBit]
        by_cases h1 : j < w
        · have h2 : j < w + 1 := by omega
          simp only [h1, ↓reduceDIte, h2, ↓reduceIte, stateToNat_testBit]
          have hmod : (site + j) % (t + 1) < t + 1 := Nat.mod_lt _ (by omega)
          simp only [hmod, ↓reduceDIte]
          rfl
        · by_cases h2 : j = w
          · rw [h2]
            simp only [lt_self_iff_false, ↓reduceDIte, ↓reduceIte, Nat.lt_add_one, stateToNat_testBit]
            have hmod : (site + w) % (t + 1) < t + 1 := Nat.mod_lt _ (by omega)
            simp only [hmod, ↓reduceDIte]
            rfl
          · have h3 : ¬ (j < w + 1) := by omega
            simp [h1, h2, h3]
      rw [hpat]
      exact ha
    · funext a
      rw [stateToNat_testBit]
      simp [a.isLt]

private theorem prefixProd_succ (w : Nat) (input : Nat → Row) (m : Nat) :
    (List.ofFn (fun i : Fin (m + 1) => stepMat w (input i.val))).prod =
      (List.ofFn (fun i : Fin m => stepMat w (input i.val))).prod * stepMat w (input m) := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  rfl

private theorem list_ofFn_add_prod {α : Type*} [Monoid α] (a b : Nat) (f : Fin (a + b) → α) :
    (List.ofFn f).prod =
      (List.ofFn (fun i : Fin a => f ⟨i.val, by omega⟩)).prod *
      (List.ofFn (fun j : Fin b => f ⟨a + j.val, by omega⟩)).prod := by
  rw [← List.prod_append]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    split_ifs with hlt
    · simp
    · congr 1
      apply Fin.ext
      dsimp only
      omega

private theorem achieve_part (d n p k j : Nat) (hp : 0 < p) (hn : 0 < n) (hjk : j ≤ k) :
    let w := d + 2
    let D := 2 ^ w
    let Q := 2 ^ k
    succeedsProp w n p Q (2 ^ (j * (D * ((D + p - 1) / p) + 1))) (2 ^ (k - j)) (2 ^ j) Q := by
  intro w D Q
  let B := (D + p - 1) / p
  let Mj := 2 ^ j
  have hMj : 0 < Mj := by dsimp [Mj]; positivity
  let State := Fin Mj × (Fin B → (Fin w → Bool) → Fin Mj)
  have hcardSt : Fintype.card State = 2 ^ (j * (D * B + 1)) := by
    simp only [State, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
      Mj, D]
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  let enc : State ≃ Fin (2 ^ (j * (D * B + 1))) := Fintype.equivFinOfCardEq hcardSt
  have hcardW : Fintype.card (Fin w → Bool) = D := by simp [D]
  let enumSt : Fin D ≃ (Fin w → Bool) := (Fintype.equivFinOfCardEq hcardW).symm
  let foldDiag : Fin Mj → (Fin B → (Fin w → Bool) → Fin Mj) → Nat → Fin Mj :=
    fun acc vec prevPass =>
      ⟨(acc.val + ∑ b : Fin B,
        if h : prevPass * B + b.val < D then
          (vec b (enumSt ⟨prevPass * B + b.val, h⟩)).val
        else 0) % Mj, Nat.mod_lt _ hMj⟩
  let stepSt : Nat → Nat → State → Row → State := fun passId siteId st row =>
    if siteId = 0 then
      let acc' : Fin Mj := if passId = 0 then ⟨0, hMj⟩ else foldDiag st.1 st.2 (passId - 1)
      let vec' : Fin B → (Fin w → Bool) → Fin Mj := fun b q =>
        if h : passId * B + b.val < D then
          ⟨(stepMat w row (enumSt ⟨passId * B + b.val, h⟩) q) % Mj, Nat.mod_lt _ hMj⟩
        else ⟨0, hMj⟩
      (acc', vec')
    else
      (st.1, fun b q =>
        ⟨(∑ s : Fin w → Bool, (st.2 b s).val * stepMat w row s q) % Mj, Nat.mod_lt _ hMj⟩)
  let initSt : State := (⟨0, hMj⟩, fun _ _ => ⟨0, hMj⟩)
  let initAlg : Fin (2 ^ (k - j)) → Fin (2 ^ (j * (D * B + 1))) := fun _ => enc initSt
  let updAlg : Fin (2 ^ (k - j)) → Nat → Nat → Fin (2 ^ (j * (D * B + 1))) → Row →
      Fin (2 ^ (j * (D * B + 1))) :=
    fun _ passId siteId s row => enc (stepSt passId siteId (enc.symm s) row)
  let outAlg : Fin (2 ^ (k - j)) → Fin (2 ^ (j * (D * B + 1))) → Nat := fun coin s =>
    let st := enc.symm s
    (foldDiag st.1 st.2 (p - 1)).val + Mj * coin.val
  refine ⟨initAlg, updAlg, outAlg, ?_⟩
  intro input
  have hrun_conj : ∀ r,
      (List.range r).foldl (fun prev passId =>
        (List.range n).foldl (fun state siteId =>
          enc (stepSt passId siteId (enc.symm state) (input siteId))) prev) (enc initSt) =
      enc ((List.range r).foldl (fun prev passId =>
        (List.range n).foldl (fun state siteId =>
          stepSt passId siteId state (input siteId)) prev) initSt) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      have hinner : ∀ m (s0 : State),
          (List.range m).foldl (fun state siteId =>
            enc (stepSt r siteId (enc.symm state) (input siteId))) (enc s0) =
          enc ((List.range m).foldl (fun state siteId =>
            stepSt r siteId state (input siteId)) s0) := by
        intro m s0
        induction m with
        | zero => simp
        | succ m ihm =>
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
            List.foldl_append, List.foldl_cons, List.foldl_nil, ihm, Equiv.symm_apply_apply]
      exact hinner n _
  let P : Nat → Matrix (Fin w → Bool) (Fin w → Bool) Nat :=
    fun m => (List.ofFn (fun i : Fin m => stepMat w (input i.val))).prod
  have hpass : ∀ passId (s0 : State) (m : Nat), 0 < m →
      let res := (List.range m).foldl (fun state siteId => stepSt passId siteId state (input siteId)) s0
      res.1 = (if passId = 0 then ⟨0, hMj⟩ else foldDiag s0.1 s0.2 (passId - 1)) ∧
      ∀ (b : Fin B) (q : Fin w → Bool),
        (res.2 b q).val =
          (if h : passId * B + b.val < D then
            P m (enumSt ⟨passId * B + b.val, h⟩) q
          else 0) % Mj := by
    intro passId s0 m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    induction m' with
    | zero =>
      dsimp only
      rw [List.range_succ, List.range_zero, List.nil_append, List.foldl_cons, List.foldl_nil]
      refine ⟨by simp [stepSt], ?_⟩
      intro b q
      simp only [stepSt, ↓reduceIte]
      split_ifs with h
      · dsimp only [P]
        have hP1 : (List.ofFn (fun i : Fin 1 => stepMat w (input i.val))).prod =
            stepMat w (input 0) := by
          simp
        rw [hP1]
      · simp
    | succ m' ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      dsimp only
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set prev := (List.range (m' + 1)).foldl
        (fun state siteId => stepSt passId siteId state (input siteId)) s0
      have hne : m' + 1 ≠ 0 := by omega
      refine ⟨by simp only [stepSt, hne, ↓reduceIte]; exact ih1, ?_⟩
      intro b q
      simp only [stepSt, hne, ↓reduceIte]
      have hsum_mod : (∑ s : Fin w → Bool, (prev.2 b s).val * stepMat w (input (m' + 1)) s q) % Mj =
          (∑ s : Fin w → Bool,
            (if h : passId * B + b.val < D then P (m' + 1) (enumSt ⟨passId * B + b.val, h⟩) s else 0) *
              stepMat w (input (m' + 1)) s q) % Mj := by
        conv_lhs => rw [Finset.sum_nat_mod]
        conv_rhs => rw [Finset.sum_nat_mod]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        rw [ih2 b s]
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [hsum_mod]
      split_ifs with h
      · have hPsucc : P (m' + 2) (enumSt ⟨passId * B + b.val, h⟩) q =
            ∑ s : Fin w → Bool,
              P (m' + 1) (enumSt ⟨passId * B + b.val, h⟩) s * stepMat w (input (m' + 1)) s q := by
          dsimp only [P]
          rw [prefixProd_succ, Matrix.mul_apply]
        rw [hPsucc]
      · simp
  let diagSum : Nat → Nat := fun lim =>
    ∑ idx ∈ Finset.range (min D lim),
      if h : idx < D then P n (enumSt ⟨idx, h⟩) (enumSt ⟨idx, h⟩) else 0
  have hdiag_step : ∀ r,
      diagSum (r * B) +
        (∑ b : Fin B,
          if h : r * B + b.val < D then
            P n (enumSt ⟨r * B + b.val, h⟩) (enumSt ⟨r * B + b.val, h⟩)
          else 0) =
      diagSum ((r + 1) * B) := by
    intro r
    dsimp only [diagSum]
    have hsplit : Finset.range (min D ((r + 1) * B)) =
        Finset.range (min D (r * B)) ∪
          (Finset.Ico (min D (r * B)) (min D ((r + 1) * B))) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      have : min D (r * B) ≤ min D ((r + 1) * B) :=
        min_le_min_left D (Nat.mul_le_mul_right B (by omega))
      omega
    have hdisj : Disjoint (Finset.range (min D (r * B)))
        (Finset.Ico (min D (r * B)) (min D ((r + 1) * B))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    congr 1
    have h1 : (∑ b : Fin B,
          if h : r * B + b.val < D then
            P n (enumSt ⟨r * B + b.val, h⟩) (enumSt ⟨r * B + b.val, h⟩)
          else 0) =
        ∑ idx ∈ Finset.Ico (r * B) ((r + 1) * B),
          if h : idx < D then P n (enumSt ⟨idx, h⟩) (enumSt ⟨idx, h⟩) else 0 := by
      refine Finset.sum_bij (fun (b : Fin B) _ => r * B + b.val) ?_ ?_ ?_ ?_
      · intro b _
        simp only [Finset.mem_Ico]
        have hb := b.isLt
        rw [Nat.add_mul, one_mul]
        omega
      · intro b1 _ b2 _ h
        apply Fin.ext
        omega
      · intro idx hidx
        simp only [Finset.mem_Ico] at hidx
        rw [Nat.add_mul, one_mul] at hidx
        exact ⟨⟨idx - r * B, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
      · intro b _
        rfl
    rw [h1]
    symm
    have hleB : r * B ≤ (r + 1) * B := Nat.mul_le_mul_right B (by omega)
    apply Finset.sum_subset_zero_on_sdiff
    · intro x hx
      simp only [Finset.mem_Ico] at hx ⊢
      have h1 : min D (r * B) ≤ r * B := min_le_right _ _
      have h2 : min D ((r + 1) * B) ≤ (r + 1) * B := min_le_right _ _
      omega
    · intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_Ico] at hx
      have hge : ¬ (x < D) := by omega
      simp [hge]
    · intro x _
      rfl
  have houter : ∀ r, 0 < r →
      let st := (List.range r).foldl (fun prev passId =>
        (List.range n).foldl (fun state siteId =>
          stepSt passId siteId state (input siteId)) prev) initSt
      st.1.val = diagSum ((r - 1) * B) % Mj ∧
      ∀ (b : Fin B) (q : Fin w → Bool),
        (st.2 b q).val =
          (if h : (r - 1) * B + b.val < D then
            P n (enumSt ⟨(r - 1) * B + b.val, h⟩) q
          else 0) % Mj := by
    intro r hr
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    induction r' with
    | zero =>
      dsimp only
      rw [List.range_succ, List.range_zero, List.nil_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨hp1, hp2⟩ := hpass 0 initSt n hn
      refine ⟨?_, ?_⟩
      · simp only [hp1, ↓reduceIte, Nat.sub_self, zero_mul, diagSum, Nat.min_zero,
          Finset.range_zero, Finset.sum_empty, Nat.zero_mod]
      · intro b q
        simpa using hp2 b q
    | succ r' ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      dsimp only
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set prev := (List.range (r' + 1)).foldl (fun prev passId =>
        (List.range n).foldl (fun state siteId =>
          stepSt passId siteId state (input siteId)) prev) initSt
      obtain ⟨hp1, hp2⟩ := hpass (r' + 1) prev n hn
      refine ⟨?_, ?_⟩
      · rw [hp1]
        have hne : r' + 1 ≠ 0 := by omega
        simp only [hne, ↓reduceIte, Nat.add_sub_cancel, foldDiag]
        have hsum_eq : (∑ b : Fin B,
              if h : r' * B + b.val < D then
                (prev.2 b (enumSt ⟨r' * B + b.val, h⟩)).val
              else 0) % Mj =
            (∑ b : Fin B,
              if h : r' * B + b.val < D then
                P n (enumSt ⟨r' * B + b.val, h⟩) (enumSt ⟨r' * B + b.val, h⟩)
              else 0) % Mj := by
          conv_lhs => rw [Finset.sum_nat_mod]
          conv_rhs => rw [Finset.sum_nat_mod]
          congr 1
          apply Finset.sum_congr rfl
          intro b _
          split_ifs with h
          · rw [ih2 b (enumSt ⟨r' * B + b.val, h⟩)]
            simp only [Nat.add_sub_cancel, h, ↓reduceDIte, Nat.mod_mod]
          · simp
        rw [Nat.add_mod, ih1, Nat.add_sub_cancel, Nat.mod_mod, hsum_eq, ← Nat.add_mod, hdiag_step r']
      · intro b q
        simpa using hp2 b q
  obtain ⟨ho1, ho2⟩ := houter p hp
  set finalSt := (List.range p).foldl (fun prev passId =>
    (List.range n).foldl (fun state siteId =>
      stepSt passId siteId state (input siteId)) prev) initSt
  have hlow : (foldDiag finalSt.1 finalSt.2 (p - 1)).val = (totalCount w n input) % Mj := by
    dsimp only [foldDiag]
    have hsum_eq : (∑ b : Fin B,
          if h : (p - 1) * B + b.val < D then
            (finalSt.2 b (enumSt ⟨(p - 1) * B + b.val, h⟩)).val
          else 0) % Mj =
        (∑ b : Fin B,
          if h : (p - 1) * B + b.val < D then
            P n (enumSt ⟨(p - 1) * B + b.val, h⟩) (enumSt ⟨(p - 1) * B + b.val, h⟩)
          else 0) % Mj := by
      conv_lhs => rw [Finset.sum_nat_mod]
      conv_rhs => rw [Finset.sum_nat_mod]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      split_ifs with h
      · rw [ho2 b (enumSt ⟨(p - 1) * B + b.val, h⟩)]
        simp only [h, ↓reduceDIte, Nat.mod_mod]
      · simp
    rw [Nat.add_mod, ho1, Nat.mod_mod, hsum_eq, ← Nat.add_mod, hdiag_step (p - 1)]
    have hp1 : p - 1 + 1 = p := by omega
    rw [hp1]
    have hpB : D ≤ p * B := by
      dsimp only [B]
      have hdiv := Nat.div_add_mod (D + p - 1) p
      have hmod : (D + p - 1) % p < p := Nat.mod_lt _ hp
      omega
    have hmin : min D (p * B) = D := Nat.min_eq_left hpB
    have htr : diagSum (p * B) = Matrix.trace (P n) := by
      dsimp only [diagSum, Matrix.trace, Matrix.diag]
      rw [hmin]
      have h1 : (∑ idx ∈ Finset.range D, if h : idx < D then P n (enumSt ⟨idx, h⟩) (enumSt ⟨idx, h⟩) else 0) =
          ∑ idx : Fin D, P n (enumSt idx) (enumSt idx) := by
        symm
        refine Finset.sum_bij (fun (idx : Fin D) _ => idx.val)
          (fun idx _ => Finset.mem_range.mpr idx.isLt)
          (fun a _ b _ h => Fin.ext h)
          (fun x hx => ⟨⟨x, Finset.mem_range.mp hx⟩, Finset.mem_univ _, rfl⟩)
          (fun idx _ => by simp [idx.isLt])
      rw [h1]
      exact Equiv.sum_comp enumSt (fun s => P n s s)
    rw [htr, totalCount_eq_trace w n hn input]
  have hQpow : Mj * 2 ^ (k - j) = Q := by
    dsimp only [Mj, Q]
    rw [← pow_add, Nat.add_sub_of_le hjk]
  have hcoin_lt : (totalCount w n input % Q) / Mj < 2 ^ (k - j) := by
    have hltQ : totalCount w n input % Q < Q := Nat.mod_lt _ (by dsimp [Q]; positivity)
    have hltQ' : totalCount w n input % Q < Mj * 2 ^ (k - j) := hQpow.symm ▸ hltQ
    exact (Nat.div_lt_iff_lt_mul hMj).mpr (by rw [mul_comm]; exact hltQ')
  let coin0 : Fin (2 ^ (k - j)) := ⟨(totalCount w n input % Q) / Mj, hcoin_lt⟩
  have hhit : outAlg coin0 (runAlg p n (2 ^ (j * (D * B + 1))) (initAlg coin0) (updAlg coin0) input) =
      totalCount w n input % Q := by
    dsimp only [outAlg, runAlg, initAlg, updAlg]
    rw [hrun_conj p, Equiv.symm_apply_apply, hlow]
    have hdvd : Mj ∣ Q := ⟨2 ^ (k - j), hQpow.symm⟩
    have hmod_mod : totalCount w n input % Mj = (totalCount w n input % Q) % Mj := by
      rw [Nat.mod_mod_of_dvd _ hdvd]
    rw [hmod_mod]
    have hdm := Nat.div_add_mod (totalCount w n input % Q) Mj
    dsimp only [coin0]
    omega
  rw [finRange_filter_length_eq_finset_card]
  have hmem : coin0 ∈ (Finset.univ : Finset (Fin (2 ^ (k - j)))).filter (fun coin =>
      (outAlg coin (runAlg p n (2 ^ (j * (D * B + 1))) (initAlg coin) (updAlg coin) input) ==
        totalCount w n input % Q) = true) := by
    simp [hhit]
  have hpos : 1 ≤ ((Finset.univ : Finset (Fin (2 ^ (k - j)))).filter (fun coin =>
      (outAlg coin (runAlg p n (2 ^ (j * (D * B + 1))) (initAlg coin) (updAlg coin) input) ==
        totalCount w n input % Q) = true)).card := Finset.one_le_card.mpr ⟨coin0, hmem⟩
  calc
    2 ^ j * 2 ^ (k - j) = Q * 1 := by rw [mul_one]; exact hQpow
    _ ≤ Q * ((Finset.univ : Finset (Fin (2 ^ (k - j)))).filter (fun coin =>
        (outAlg coin (runAlg p n (2 ^ (j * (D * B + 1))) (initAlg coin) (updAlg coin) input) ==
          totalCount w n input % Q) = true)).card := Nat.mul_le_mul_left Q hpos

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private def z2b (x : ZMod 2) : Bool := decide (x = 1)

private theorem b2z_z2b (x : ZMod 2) : b2z (z2b x) = x := by
  fin_cases x <;> rfl

private theorem z2b_b2z (b : Bool) : z2b (b2z b) = b := by
  cases b <;> rfl

private theorem z2b_add (x y : ZMod 2) : z2b (x + y) = xor (z2b x) (z2b y) := by
  fin_cases x <;> fin_cases y <;> rfl

private theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> rfl

private theorem exists_primitive_lfsr (w : Nat) (hw : 0 < w) :
    ∃ (taps : Fin w → ZMod 2),
      let L : (Fin w → ZMod 2) → (Fin w → ZMod 2) := fun s j =>
        if h : j.val + 1 < w then s ⟨j.val + 1, h⟩ else ∑ i : Fin w, taps i * s i
      (∀ u v, L (u + v) = L u + L v) ∧
      (∀ s, L^[2 ^ w - 1] s = s) ∧
      (∀ v : Fin w → ZMod 2, v ≠ 0 →
        ∃ t < 2 ^ w - 1, L^[t] (fun j => if j.val = w - 1 then 1 else 0) = v) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 w
  letI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = 2 ^ w := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 w (by omega)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = 2 ^ w - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units, hcardF]
  let α : F := g.val
  have hα_ne : α ≠ 0 := g.ne_zero
  have hα_pow_one : α ^ (2 ^ w - 1) = 1 := by
    have h1 : g ^ (2 ^ w - 1) = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
    exact congrArg Units.val h1
  have hα_gen : ∀ x : F, x ≠ 0 → ∃ m < 2 ^ w - 1, α ^ m = x := by
    intro x hx
    let u : Fˣ := Units.mk0 x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
    have hord_pos : (0 : ℤ) < (orderOf g : ℤ) := by
      have : 0 < 2 ^ w - 1 := by
        have : 2 ≤ 2 ^ w := Nat.le_self_pow (by omega) 2
        omega
      omega
    let m : Nat := (k % (orderOf g : ℤ)).toNat
    have hm_nonneg : 0 ≤ k % (orderOf g : ℤ) := Int.emod_nonneg k (ne_of_gt hord_pos)
    have hm_cast : (m : ℤ) = k % (orderOf g : ℤ) := Int.toNat_of_nonneg hm_nonneg
    have hm_lt : m < 2 ^ w - 1 := by
      rw [← hord]
      have hlt : k % (orderOf g : ℤ) < (orderOf g : ℤ) := Int.emod_lt_of_pos k hord_pos
      omega
    have hpow : g ^ m = u := by
      rw [← zpow_natCast, hm_cast, zpow_mod_orderOf, hk]
    exact ⟨m, hm_lt, congrArg Units.val hpow⟩
  have hchar2 : ∀ x : F, x + x = 0 := by
    intro x
    have h2 : (2 : F) = 0 := by
      have h2z : (2 : ZMod 2) = 0 := rfl
      calc (2 : F) = algebraMap (ZMod 2) F (2 : ZMod 2) := (map_ofNat (algebraMap (ZMod 2) F) 2).symm
        _ = 0 := by rw [h2z, map_zero]
    calc x + x = (2 : F) * x := by ring
      _ = 0 := by rw [h2, zero_mul]
  have hneg_eq : ∀ x : F, -x = x := by
    intro x
    have := hchar2 x
    exact neg_eq_iff_add_eq_zero.mpr this
  have hz2_one : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
    intro x hx
    fin_cases x
    · exact absurd rfl hx
    · rfl
  let evalPow : ∀ m, (Fin m → ZMod 2) → F :=
    fun m v => ∑ i : Fin m, algebraMap (ZMod 2) F (v i) * α ^ i.val
  have heval_add : ∀ m (u v : Fin m → ZMod 2), evalPow m (u + v) = evalPow m u + evalPow m v := by
    intro m u v
    dsimp only [evalPow]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [Pi.add_apply, map_add, add_mul]
  have hcard_lt : Fintype.card F < Fintype.card (Fin (w + 1) → ZMod 2) := by
    rw [hcardF]
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt (evalPow (w + 1)) hcard_lt
  let c : Fin (w + 1) → ZMod 2 := fun i => a i - b i
  have hc_ne : c ≠ 0 := by
    intro h0
    apply hab
    funext i
    have hi := congrFun h0 i
    exact sub_eq_zero.mp hi
  have hc_sum : evalPow (w + 1) c = 0 := by
    have h1 : evalPow (w + 1) c = evalPow (w + 1) a - evalPow (w + 1) b := by
      dsimp only [evalPow, c]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp [map_sub, sub_mul]
    rw [h1, hfab, sub_self]
  have htop_ne : c ⟨w, Nat.lt_succ_self w⟩ ≠ 0 := by
    intro htop0
    let S : Finset (Fin w) := Finset.univ.filter (fun i : Fin w => c i.castSucc ≠ 0)
    have hSne : S.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hc_ne
      funext i
      by_cases hi : i.val < w
      · have hnot : (⟨i.val, hi⟩ : Fin w) ∉ S := by rw [hempty]; simp
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnot
        exact hnot
      · have hilt : i.val < w + 1 := i.isLt
        have heq : i = ⟨w, Nat.lt_succ_self w⟩ := by apply Fin.ext; dsimp only; omega
        rw [heq]
        exact htop0
    let m : Fin w := S.max' hSne
    have hm_mem : m ∈ S := Finset.max'_mem S hSne
    have hm_ne : c m.castSucc ≠ 0 := (Finset.mem_filter.mp hm_mem).2
    have hm_one : c m.castSucc = 1 := hz2_one _ hm_ne
    have hm_max : ∀ i : Fin (w + 1), m.val < i.val → c i = 0 := by
      intro i hi
      by_cases hiw : i.val < w
      · by_contra hci
        have hle : (⟨i.val, hiw⟩ : Fin w) ≤ m :=
          Finset.le_max' S ⟨i.val, hiw⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩)
        exact not_lt_of_ge hle hi
      · have hilt : i.val < w + 1 := i.isLt
        have heq : i = ⟨w, Nat.lt_succ_self w⟩ := by apply Fin.ext; dsimp only; omega
        rw [heq]
        exact htop0
    have hαm : α ^ m.val = evalPow m.val (fun i => c ⟨i.val, by omega⟩) := by
      have h0 : evalPow (w + 1) c =
          algebraMap (ZMod 2) F (c m.castSucc) * α ^ m.val +
            ∑ i : Fin m.val, algebraMap (ZMod 2) F (c ⟨i.val, by omega⟩) * α ^ i.val := by
        dsimp only [evalPow]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m.castSucc)]
        congr 1
        let emb : Fin m.val → Fin (w + 1) := fun i => ⟨i.val, by omega⟩
        calc (∑ i ∈ Finset.univ.erase m.castSucc, algebraMap (ZMod 2) F (c i) * α ^ i.val)
            = ∑ i ∈ (Finset.univ : Finset (Fin m.val)).image emb,
                algebraMap (ZMod 2) F (c i) * α ^ i.val := by
              symm
              apply Finset.sum_subset_zero_on_sdiff
              · intro x hx
                simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
                obtain ⟨i, rfl⟩ := hx
                simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff, emb]
                exact ne_of_lt i.isLt
              · intro x hx
                simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
                  Finset.mem_image, true_and, not_exists, emb] at hx
                have hgt : m.val < x.val := by
                  by_contra hle
                  push Not at hle
                  have hlt : x.val < m.val := lt_of_le_of_ne hle (fun he => hx.1 (Fin.ext he))
                  exact hx.2 ⟨x.val, hlt⟩ rfl
                rw [hm_max x hgt, map_zero, zero_mul]
              · intro _ _; rfl
          _ = ∑ i : Fin m.val, algebraMap (ZMod 2) F (c ⟨i.val, by omega⟩) * α ^ i.val := by
              rw [Finset.sum_image]
              intro i _ j _ hij
              have hv : (emb i).val = (emb j).val := congrArg Fin.val hij
              exact Fin.ext hv
      rw [hc_sum, hm_one, map_one, one_mul] at h0
      have hsub := eq_neg_of_add_eq_zero_left h0.symm
      rw [hneg_eq] at hsub
      exact hsub
    have hm_pos : 0 < m.val := by
      by_contra hm0
      have hm0' : m.val = 0 := by omega
      have h1 : α ^ m.val = 1 := by rw [hm0', pow_zero]
      have h2 : evalPow m.val (fun i => c ⟨i.val, by omega⟩) = 0 := by
        dsimp only [evalPow]
        apply Finset.sum_eq_zero
        intro i _
        exfalso
        have := i.isLt
        omega
      rw [h1, h2] at hαm
      exact one_ne_zero hαm
    let img : Finset F := Finset.univ.image (evalPow m.val)
    have himg_add : ∀ x ∈ img, ∀ y ∈ img, x + y ∈ img := by
      intro x hx y hy
      simp only [img, Finset.mem_image, Finset.mem_univ, true_and] at hx hy ⊢
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, heval_add m.val u v⟩
    have himg_mul : ∀ x ∈ img, α * x ∈ img := by
      intro x hx
      simp only [img, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨v, rfl⟩ := hx
      have hsplit : α * evalPow m.val v =
          evalPow m.val (fun i => if h : 0 < i.val then v ⟨i.val - 1, by omega⟩ else 0) +
            algebraMap (ZMod 2) F (v ⟨m.val - 1, by omega⟩) * α ^ m.val := by
        dsimp only [evalPow]
        rw [Finset.mul_sum]
        have hstep1 : ∀ i : Fin m.val,
            α * (algebraMap (ZMod 2) F (v i) * α ^ i.val) =
              algebraMap (ZMod 2) F (v i) * α ^ (i.val + 1) := by
          intro i; ring
        simp_rw [hstep1]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨m.val - 1, by omega⟩ : Fin m.val))]
        have htop_eq : m.val - 1 + 1 = m.val := by omega
        rw [htop_eq, add_comm]
        congr 1
        symm
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hm_pos⟩ : Fin m.val))]
        simp only [lt_self_iff_false, ↓reduceDIte, map_zero, zero_mul, zero_add]
        refine Finset.sum_bij (fun (i : Fin m.val) hi => ⟨i.val - 1, by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi
          omega⟩) ?_ ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi ⊢
          omega
        · intro i1 hi1 i2 hi2 h
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi1 hi2
          have h' : i1.val - 1 = i2.val - 1 := congrArg Fin.val h
          exact Fin.ext (by omega)
        · intro j hj
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hj
          have hjlt : j.val < m.val := j.isLt
          refine ⟨⟨j.val + 1, by omega⟩, ?_, by apply Fin.ext; dsimp only; omega⟩
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff]
          omega
        · intro i hi
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi
          have hpos : 0 < i.val := by omega
          simp only [hpos, ↓reduceDIte]
          have hsub : i.val - 1 + 1 = i.val := by omega
          rw [hsub]
      rw [hsplit]
      apply himg_add
      · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
      · generalize hzv : v ⟨m.val - 1, by omega⟩ = z
        fin_cases z
        · change algebraMap (ZMod 2) F 0 * α ^ m.val ∈ img
          rw [map_zero, zero_mul]
          refine Finset.mem_image.mpr ⟨0, Finset.mem_univ _, ?_⟩
          simp [evalPow]
        · change algebraMap (ZMod 2) F 1 * α ^ m.val ∈ img
          rw [map_one, one_mul, hαm]
          exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    have himg_pow : ∀ t : Nat, α ^ t ∈ img := by
      intro t
      induction t with
      | zero =>
        rw [pow_zero]
        refine Finset.mem_image.mpr ⟨fun i => if i.val = 0 then 1 else 0, Finset.mem_univ _, ?_⟩
        dsimp only [evalPow]
        rw [Finset.sum_eq_single (⟨0, hm_pos⟩ : Fin m.val)]
        · simp
        · intro i _ hi
          have : i.val ≠ 0 := fun h0 => hi (Fin.ext h0)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      | succ t iht =>
        rw [pow_succ']
        exact himg_mul _ iht
    have himg_all : ∀ x : F, x ∈ img := by
      intro x
      by_cases hx : x = 0
      · subst hx
        refine Finset.mem_image.mpr ⟨0, Finset.mem_univ _, ?_⟩
        simp [evalPow]
      · obtain ⟨t, _, rfl⟩ := hα_gen x hx
        exact himg_pow t
    have hcard_le : Fintype.card F ≤ img.card := by
      have : (Finset.univ : Finset F) ⊆ img := fun x _ => himg_all x
      exact Finset.card_le_card this
    have himg_card : img.card ≤ 2 ^ m.val := by
      calc img.card ≤ (Finset.univ : Finset (Fin m.val → ZMod 2)).card := Finset.card_image_le
        _ = 2 ^ m.val := by simp
    have hlt_pow : 2 ^ m.val < 2 ^ w := Nat.pow_lt_pow_right (by omega) m.isLt
    omega
  have htop_one : c ⟨w, Nat.lt_succ_self w⟩ = 1 := hz2_one _ htop_ne
  let taps : Fin w → ZMod 2 := fun i => c i.castSucc
  have hαw : α ^ w = evalPow w taps := by
    have h1 : evalPow (w + 1) c = evalPow w taps + algebraMap (ZMod 2) F (c ⟨w, Nat.lt_succ_self w⟩) * α ^ w := by
      dsimp only [evalPow, taps]
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [hc_sum, htop_one, map_one, one_mul] at h1
    have hsub := eq_neg_of_add_eq_zero_left h1.symm
    rw [hneg_eq] at hsub
    exact hsub.symm
  have heval_surj : Function.Surjective (evalPow w) := by
    let img : Finset F := Finset.univ.image (evalPow w)
    have himg_add : ∀ x ∈ img, ∀ y ∈ img, x + y ∈ img := by
      intro x hx y hy
      simp only [img, Finset.mem_image, Finset.mem_univ, true_and] at hx hy ⊢
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, heval_add w u v⟩
    have himg_mul : ∀ x ∈ img, α * x ∈ img := by
      intro x hx
      simp only [img, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨v, rfl⟩ := hx
      have hsplit : α * evalPow w v =
          evalPow w (fun i => if h : 0 < i.val then v ⟨i.val - 1, by omega⟩ else 0) +
            algebraMap (ZMod 2) F (v ⟨w - 1, by omega⟩) * α ^ w := by
        dsimp only [evalPow]
        rw [Finset.mul_sum]
        have hstep1 : ∀ i : Fin w,
            α * (algebraMap (ZMod 2) F (v i) * α ^ i.val) =
              algebraMap (ZMod 2) F (v i) * α ^ (i.val + 1) := by
          intro i; ring
        simp_rw [hstep1]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨w - 1, by omega⟩ : Fin w))]
        have htop_eq : w - 1 + 1 = w := by omega
        rw [htop_eq, add_comm]
        congr 1
        symm
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hw⟩ : Fin w))]
        simp only [lt_self_iff_false, ↓reduceDIte, map_zero, zero_mul, zero_add]
        refine Finset.sum_bij (fun (i : Fin w) hi => ⟨i.val - 1, by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi
          omega⟩) ?_ ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi ⊢
          omega
        · intro i1 hi1 i2 hi2 h
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi1 hi2
          have h' : i1.val - 1 = i2.val - 1 := congrArg Fin.val h
          exact Fin.ext (by omega)
        · intro j hj
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hj
          have hjlt : j.val < w := j.isLt
          refine ⟨⟨j.val + 1, by omega⟩, ?_, by apply Fin.ext; dsimp only; omega⟩
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff]
          omega
        · intro i hi
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi
          have hpos : 0 < i.val := by omega
          simp only [hpos, ↓reduceDIte]
          have hsub : i.val - 1 + 1 = i.val := by omega
          rw [hsub]
      rw [hsplit]
      apply himg_add
      · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
      · generalize hzv : v ⟨w - 1, by omega⟩ = z
        fin_cases z
        · change algebraMap (ZMod 2) F 0 * α ^ w ∈ img
          rw [map_zero, zero_mul]
          refine Finset.mem_image.mpr ⟨0, Finset.mem_univ _, ?_⟩
          simp [evalPow]
        · change algebraMap (ZMod 2) F 1 * α ^ w ∈ img
          rw [map_one, one_mul, hαw]
          exact Finset.mem_image.mpr ⟨taps, Finset.mem_univ _, rfl⟩
    have himg_pow : ∀ t : Nat, α ^ t ∈ img := by
      intro t
      induction t with
      | zero =>
        rw [pow_zero]
        refine Finset.mem_image.mpr ⟨fun i => if i.val = 0 then 1 else 0, Finset.mem_univ _, ?_⟩
        dsimp only [evalPow]
        rw [Finset.sum_eq_single (⟨0, hw⟩ : Fin w)]
        · simp
        · intro i _ hi
          have : i.val ≠ 0 := fun h0 => hi (Fin.ext h0)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      | succ t iht =>
        rw [pow_succ']
        exact himg_mul _ iht
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by simp [evalPow, hx]⟩
    · obtain ⟨t, _, rfl⟩ := hα_gen x hx
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp (himg_pow t)
      exact ⟨v, hv⟩
  have hcard_eq : Fintype.card (Fin w → ZMod 2) = Fintype.card F := by
    rw [hcardF]; simp
  have heval_bij : Function.Bijective (evalPow w) :=
    (Fintype.bijective_iff_surjective_and_card (evalPow w)).mpr ⟨heval_surj, hcard_eq⟩
  let eF : (Fin w → ZMod 2) ≃ F := Equiv.ofBijective (evalPow w) heval_bij
  let lam : F → ZMod 2 := fun x => eF.symm x ⟨0, hw⟩
  have hlam_add : ∀ x y : F, lam (x + y) = lam x + lam y := by
    intro x y
    dsimp only [lam]
    have hsym : eF.symm (x + y) = eF.symm x + eF.symm y := by
      apply eF.injective
      change eF (eF.symm (x + y)) = evalPow w (eF.symm x + eF.symm y)
      rw [Equiv.apply_symm_apply, heval_add]
      exact congrArg₂ (· + ·) (eF.apply_symm_apply x).symm (eF.apply_symm_apply y).symm
    rw [hsym, Pi.add_apply]
  have hlam_sum : ∀ (s : Finset (Fin w)) (f : Fin w → F), lam (∑ i ∈ s, f i) = ∑ i ∈ s, lam (f i) := by
    intro s f
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      dsimp only [lam]
      have h0 : eF.symm 0 = 0 := by
        apply eF.injective
        simp [eF, evalPow]
      rw [h0]
      rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hlam_add, ih]
  have hlam_zero : lam 0 = 0 := by
    have := hlam_add 0 0
    rw [add_zero] at this
    have h2 := congrArg (fun z => z - lam 0) this
    simpa using h2.symm
  have hlam_smul : ∀ (a : ZMod 2) (x : F), lam (algebraMap (ZMod 2) F a * x) = a * lam x := by
    intro a x
    fin_cases a
    · change lam (algebraMap (ZMod 2) F 0 * x) = 0 * lam x
      rw [map_zero, zero_mul, zero_mul, hlam_zero]
    · change lam (algebraMap (ZMod 2) F 1 * x) = 1 * lam x
      rw [map_one, one_mul, one_mul]
  have hlam_one : lam 1 = 1 := by
    dsimp only [lam]
    have h1 : eF (fun i => if i.val = 0 then 1 else 0) = 1 := by
      dsimp only [eF, Equiv.ofBijective_apply, evalPow]
      rw [Finset.sum_eq_single (⟨0, hw⟩ : Fin w)]
      · simp
      · intro i _ hi
        have : i.val ≠ 0 := fun h0 => hi (Fin.ext h0)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hsym : eF.symm 1 = fun i => if i.val = 0 then 1 else 0 := by
      rw [← h1, Equiv.symm_apply_apply]
    rw [hsym]
    simp
  let L : (Fin w → ZMod 2) → (Fin w → ZMod 2) := fun s j =>
    if h : j.val + 1 < w then s ⟨j.val + 1, h⟩ else ∑ i : Fin w, taps i * s i
  let psi : F → (Fin w → ZMod 2) := fun x j => lam (α ^ j.val * x)
  have hpsi_step : ∀ x : F, psi (α * x) = L (psi x) := by
    intro x
    funext j
    dsimp only [psi, L]
    split_ifs with hj
    · congr 1; ring
    · have hjlt : j.val < w := j.isLt
      have hjw : j.val + 1 = w := by omega
      have hmul : α ^ j.val * (α * x) = α ^ w * x := by
        calc α ^ j.val * (α * x) = (α ^ j.val * α) * x := by ring
          _ = α ^ (j.val + 1) * x := by rw [pow_succ]
          _ = α ^ w * x := by rw [hjw]
      rw [hmul, hαw]
      dsimp only [evalPow]
      rw [Finset.sum_mul]
      have hls := hlam_sum (Finset.univ : Finset (Fin w))
        (fun i : Fin w => algebraMap (ZMod 2) F (taps i) * α ^ i.val * x)
      rw [hls]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, hlam_smul]
  have hpsi_iter : ∀ t (x : F), L^[t] (psi x) = psi (α ^ t * x) := by
    intro t
    induction t with
    | zero => intro x; simp
    | succ t ih =>
      intro x
      rw [Function.iterate_succ_apply, ← hpsi_step, ih]
      congr 1; ring
  have hpsi_inj : Function.Injective psi := by
    intro x y hxy
    by_contra hne
    have hdiff_ne : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hdiff_zero : psi (x - y) = 0 := by
      funext j
      dsimp only [psi]
      have hsub : α ^ j.val * (x - y) = α ^ j.val * x + α ^ j.val * y := by
        rw [mul_sub, sub_eq_add_neg, hneg_eq]
      rw [hsub, hlam_add]
      have hj := congrFun hxy j
      dsimp only [psi] at hj
      rw [hj]
      generalize hz : lam (α ^ j.val * y) = z
      fin_cases z <;> rfl
    obtain ⟨t, _, ht⟩ := hα_gen (x - y)⁻¹ (inv_ne_zero hdiff_ne)
    have hL0 : ∀ m, L^[m] 0 = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ihm =>
        rw [Function.iterate_succ_apply', ihm]
        funext j
        simp [L]
    have h1 := hpsi_iter t (x - y)
    rw [hdiff_zero, hL0, ht, inv_mul_cancel₀ hdiff_ne] at h1
    have h00 := congrFun h1 ⟨0, hw⟩
    dsimp only [psi] at h00
    rw [pow_zero, one_mul, hlam_one] at h00
    exact zero_ne_one h00
  have hpsi_bij : Function.Bijective psi :=
    (Fintype.bijective_iff_injective_and_card psi).mpr ⟨hpsi_inj, hcard_eq.symm⟩
  let ePsi : F ≃ (Fin w → ZMod 2) := Equiv.ofBijective psi hpsi_bij
  refine ⟨taps, ?_, ?_, ?_⟩
  · intro u v
    funext j
    dsimp only [L, Pi.add_apply]
    split_ifs with hj
    · rfl
    · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · intro s
    obtain ⟨x, rfl⟩ := ePsi.surjective s
    change L^[2 ^ w - 1] (psi x) = psi x
    rw [hpsi_iter, hα_pow_one, one_mul]
  · intro v hv
    let eTop : Fin w → ZMod 2 := fun j => if j.val = w - 1 then 1 else 0
    have heTop_ne : eTop ≠ 0 := by
      intro h0
      have := congrFun h0 ⟨w - 1, by omega⟩
      simp [eTop] at this
    let x0 : F := ePsi.symm eTop
    let xv : F := ePsi.symm v
    have hpsi0 : psi 0 = 0 := by
      funext j
      dsimp only [psi]
      rw [mul_zero, hlam_zero]
      rfl
    have hx0_ne : x0 ≠ 0 := by
      intro hx0
      apply heTop_ne
      calc eTop = psi x0 := (ePsi.apply_symm_apply eTop).symm
        _ = 0 := by rw [hx0, hpsi0]
    have hxv_ne : xv ≠ 0 := by
      intro hxv
      apply hv
      calc v = psi xv := (ePsi.apply_symm_apply v).symm
        _ = 0 := by rw [hxv, hpsi0]
    obtain ⟨t, ht, hαt⟩ := hα_gen (xv * x0⁻¹) (mul_ne_zero hxv_ne (inv_ne_zero hx0_ne))
    refine ⟨t, ht, ?_⟩
    have h1 : eTop = psi x0 := (ePsi.apply_symm_apply eTop).symm
    have h2 : v = psi xv := (ePsi.apply_symm_apply v).symm
    change L^[t] eTop = v
    rw [h1, hpsi_iter, hαt, mul_assoc, inv_mul_cancel₀ hx0_ne, mul_one, ← h2]

private def mkSt {d : Nat} (x : Fin d → Bool) (t0 t1 : Bool) : Fin (d + 2) → Bool :=
  fun j => if h : j.val < d then x ⟨j.val, h⟩ else if j.val = d then t0 else t1

private def payOf {d : Nat} (s : Fin (d + 2) → Bool) : Fin d → Bool :=
  fun i => s ⟨i.val, by omega⟩

private def t0Of {d : Nat} (s : Fin (d + 2) → Bool) : Bool := s ⟨d, by omega⟩

private def t1Of {d : Nat} (s : Fin (d + 2) → Bool) : Bool := s ⟨d + 1, by omega⟩

private theorem mkSt_eta {d : Nat} (s : Fin (d + 2) → Bool) :
    mkSt (payOf s) (t0Of s) (t1Of s) = s := by
  funext j
  dsimp only [mkSt, payOf, t0Of, t1Of]
  have hjlt : j.val < d + 2 := j.isLt
  split_ifs with h1 h2
  · rfl
  · congr 1; apply Fin.ext; exact h2.symm
  · congr 1; apply Fin.ext; dsimp only; omega

private theorem payOf_mkSt {d : Nat} (x : Fin d → Bool) (t0 t1 : Bool) :
    payOf (mkSt x t0 t1) = x := by
  funext i; simp [payOf, mkSt, i.isLt]

private theorem t0Of_mkSt {d : Nat} (x : Fin d → Bool) (t0 t1 : Bool) :
    t0Of (mkSt x t0 t1) = t0 := by
  simp [t0Of, mkSt]

private theorem t1Of_mkSt {d : Nat} (x : Fin d → Bool) (t0 t1 : Bool) :
    t1Of (mkSt x t0 t1) = t1 := by
  simp [t1Of, mkSt]

private def midSt {w : Nat} (p s : Fin w → Bool) (m i : Nat) : Fin w → Bool :=
  fun j =>
    if h1 : i + j.val < w then p ⟨i + j.val, h1⟩
    else if h2 : w - m + (i + j.val - w) < w then s ⟨w - m + (i + j.val - w), h2⟩
    else false

private theorem prod_prefix_w_steps {w : Nat} (R : Nat → Row) (m : Nat) (hm : m ≤ w) :
    ∀ p s : Fin w → Bool,
      (List.ofFn (fun i : Fin m => stepMat w (R i.val))).prod p s =
        if (∀ j : Fin w, ∀ hj : m + j.val < w, s j = p ⟨m + j.val, hj⟩) ∧
           (∀ i : Nat, ∀ hi : i < m, R i (patVal (midSt p s m i) (s ⟨w - m + i, by omega⟩)) = true)
        then 1 else 0 := by
  induction m with
  | zero =>
    intro p s
    simp only [List.ofFn_zero, List.prod_nil, Matrix.one_apply, Nat.zero_add,
      not_lt_zero', IsEmpty.forall_iff, implies_true, and_true]
    exact ite_eq_of_iff ⟨fun h j _ => by rw [h], fun h => by funext j; exact (h j j.isLt).symm⟩ 1 0
  | succ m ih =>
    intro p s
    rw [prefixProd_succ, Matrix.mul_apply]
    have hw_pos : 0 < w := by omega
    have hstep_eval : ∀ r : Fin w → Bool,
        stepMat w (R m) r s =
          if R m (patVal r (s ⟨w - 1, by omega⟩)) = true ∧
             (∀ j : Fin w, ∀ hj : j.val + 1 < w, r ⟨j.val + 1, hj⟩ = s j)
          then 1 else 0 := by
      intro r
      simp only [stepMat, Matrix.of_apply]
      split_ifs with h
      · rw [Finset.card_eq_one]
        refine ⟨s ⟨w - 1, by omega⟩, ?_⟩
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro ⟨_, hnxt⟩
          have := congrFun hnxt ⟨w - 1, by omega⟩
          simp only [nextSt] at this
          have hnot : ¬ (w - 1 + 1 < w) := by omega
          simp only [hnot, ↓reduceDIte] at this
          exact this
        · intro hb
          subst hb
          refine ⟨h.1, ?_⟩
          funext j
          dsimp only [nextSt]
          split_ifs with hj
          · exact h.2 j hj
          · congr 1
            have hjlt : j.val < w := j.isLt
            apply Fin.ext; dsimp only; omega
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro b _ ⟨hr, hnxt⟩
        apply h
        have hb : b = s ⟨w - 1, by omega⟩ := by
          have := congrFun hnxt ⟨w - 1, by omega⟩
          simp only [nextSt] at this
          have hnot : ¬ (w - 1 + 1 < w) := by omega
          simp only [hnot, ↓reduceDIte] at this
          exact this
        subst hb
        refine ⟨hr, ?_⟩
        intro j hj
        have := congrFun hnxt j
        simp only [nextSt, hj, ↓reduceDIte] at this
        exact this
    let r0 : Fin w → Bool := fun j =>
      if h : j.val = 0 then p ⟨m, by omega⟩ else s ⟨j.val - 1, by omega⟩
    have hr0_unique : ∀ r : Fin w → Bool,
        (∀ j : Fin w, ∀ hj : m + j.val < w, r j = p ⟨m + j.val, hj⟩) →
        (∀ j : Fin w, ∀ hj : j.val + 1 < w, r ⟨j.val + 1, hj⟩ = s j) →
        r = r0 := by
      intro r h1 h2
      funext j
      dsimp only [r0]
      have hjlt : j.val < w := j.isLt
      split_ifs with hj0
      · have heq : j = ⟨0, hw_pos⟩ := Fin.ext hj0
        rw [heq]
        exact h1 ⟨0, hw_pos⟩ (by omega)
      · have hlt : j.val - 1 + 1 < w := by omega
        have heq : j = ⟨j.val - 1 + 1, hlt⟩ := Fin.ext (by dsimp only; omega)
        rw [heq]
        exact h2 ⟨j.val - 1, by omega⟩ hlt
    have hr0_mid : ∀ i < m, midSt p r0 m i = midSt p s (m + 1) i := by
      intro i hi
      funext j
      dsimp only [midSt, r0]
      have hjlt : j.val < w := j.isLt
      by_cases h1 : i + j.val < w
      · simp [h1]
      · have ha : w - m + (i + j.val - w) < w := by omega
        have hb : w - (m + 1) + (i + j.val - w) < w := by omega
        have hne : w - m + (i + j.val - w) ≠ 0 := by omega
        simp only [h1, ha, hb, hne, ↓reduceDIte]
        congr 1; apply Fin.ext; dsimp only; omega
    have hr0_eq_mid : (∀ j : Fin w, ∀ hj : m + 1 + j.val < w, s j = p ⟨m + 1 + j.val, hj⟩) →
        r0 = midSt p s (m + 1) m := by
      intro hs
      funext j
      dsimp only [r0, midSt]
      have hjlt : j.val < w := j.isLt
      by_cases hj0 : j.val = 0
      · have h1 : m + 0 < w := by omega
        simp only [hj0, ↓reduceDIte, h1]
        rfl
      · by_cases h1 : m + j.val < w
        · simp only [hj0, h1, ↓reduceDIte]
          have h1' : m + 1 + (j.val - 1) < w := by omega
          rw [hs ⟨j.val - 1, by omega⟩ h1']
          congr 1; apply Fin.ext; dsimp only; omega
        · have hb : w - (m + 1) + (m + j.val - w) < w := by omega
          simp only [hj0, h1, hb, ↓reduceDIte]
          congr 1; apply Fin.ext; dsimp only; omega
    have hsum : (∑ r : Fin w → Bool,
          (List.ofFn (fun i : Fin m => stepMat w (R i.val))).prod p r * stepMat w (R m) r s) =
        (List.ofFn (fun i : Fin m => stepMat w (R i.val))).prod p r0 * stepMat w (R m) r0 s := by
      rw [Finset.sum_eq_single r0]
      · intro r _ hr
        rw [ih (by omega) p r, hstep_eval r]
        split_ifs with h1 h2
        · exfalso; exact hr (hr0_unique r h1.1 h2.2)
        · simp
        · simp
        · simp
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, ih (by omega) p r0, hstep_eval r0]
    have heqv : ((∀ j : Fin w, ∀ hj : m + j.val < w, r0 j = p ⟨m + j.val, hj⟩) ∧
          (∀ i : Nat, ∀ hi : i < m, R i (patVal (midSt p r0 m i) (r0 ⟨w - m + i, by omega⟩)) = true)) ∧
          (R m (patVal r0 (s ⟨w - 1, by omega⟩)) = true ∧
          (∀ j : Fin w, ∀ hj : j.val + 1 < w, r0 ⟨j.val + 1, hj⟩ = s j)) ↔
        (∀ j : Fin w, ∀ hj : m + 1 + j.val < w, s j = p ⟨m + 1 + j.val, hj⟩) ∧
          (∀ i : Nat, ∀ hi : i < m + 1, R i (patVal (midSt p s (m + 1) i) (s ⟨w - (m + 1) + i, by omega⟩)) = true) := by
      constructor
      · intro ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩
        have hs_pref : ∀ j : Fin w, ∀ hj : m + 1 + j.val < w, s j = p ⟨m + 1 + j.val, hj⟩ := by
          intro j hj
          have hjlt : j.val < w := j.isLt
          have h1 := ha1 ⟨j.val + 1, by omega⟩ (by dsimp only; omega)
          have h2 := hb2 j (by omega)
          rw [← h2, h1]
          congr 1; apply Fin.ext; dsimp only; omega
        refine ⟨hs_pref, ?_⟩
        intro i hi
        by_cases him : i < m
        · have h := ha2 i him
          rw [hr0_mid i him] at h
          have hne : w - m + i ≠ 0 := by omega
          have hr0i : r0 ⟨w - m + i, by omega⟩ = s ⟨w - (m + 1) + i, by omega⟩ := by
            dsimp only [r0]
            simp only [hne, ↓reduceDIte]
            congr 1; apply Fin.ext; dsimp only; omega
          rw [hr0i] at h
          exact h
        · have hieq : i = m := by omega
          subst hieq
          rw [← hr0_eq_mid hs_pref]
          have hidx : (⟨w - (i + 1) + i, by omega⟩ : Fin w) = ⟨w - 1, by omega⟩ := by
            apply Fin.ext; dsimp only; omega
          rw [hidx]
          exact hb1
      · intro ⟨hc1, hc2⟩
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · intro j hj
          dsimp only [r0]
          have hjlt : j.val < w := j.isLt
          by_cases hj0 : j.val = 0
          · simp only [hj0, ↓reduceDIte]
            rfl
          · simp only [hj0, ↓reduceDIte]
            have h := hc1 ⟨j.val - 1, by omega⟩ (by dsimp only; omega)
            rw [h]
            congr 1; apply Fin.ext; dsimp only; omega
        · intro i hi
          rw [hr0_mid i hi]
          have hne : w - m + i ≠ 0 := by omega
          have hr0i : r0 ⟨w - m + i, by omega⟩ = s ⟨w - (m + 1) + i, by omega⟩ := by
            dsimp only [r0]
            simp only [hne, ↓reduceDIte]
            congr 1; apply Fin.ext; dsimp only; omega
          rw [hr0i]
          exact hc2 i (by omega)
        · rw [hr0_eq_mid hc1]
          have h := hc2 m (Nat.lt_succ_self m)
          have hidx : (⟨w - (m + 1) + m, by omega⟩ : Fin w) = ⟨w - 1, by omega⟩ := by
            apply Fin.ext; dsimp only; omega
          rw [hidx] at h
          exact h
        · intro j hj
          dsimp only [r0]
          have hne : j.val + 1 ≠ 0 := by omega
          simp only [hne, ↓reduceDIte, Nat.add_sub_cancel]
    have hmul_ite : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
        (if P then (1 : Nat) else 0) * (if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
      intro P Q _ _; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
    rw [hmul_ite]
    exact ite_eq_of_iff heqv 1 0

private def shiftSt {w : Nat} (p q : Fin w → Bool) (i : Nat) : Fin w → Bool :=
  fun j =>
    if h1 : i + j.val < w then p ⟨i + j.val, h1⟩
    else if h2 : i + j.val - w < w then q ⟨i + j.val - w, h2⟩
    else false

private theorem prod_w_steps {w : Nat} (R : Nat → Row) (p q : Fin w → Bool) :
    (List.ofFn (fun i : Fin w => stepMat w (R i.val))).prod p q =
      if ∀ i : Fin w, R i.val (patVal (shiftSt p q i.val) (q i)) = true then 1 else 0 := by
  rw [prod_prefix_w_steps R w (le_refl w) p q]
  have h1 : ∀ j : Fin w, ∀ hj : w + j.val < w, q j = p ⟨w + j.val, hj⟩ := by
    intro j hj; omega
  have h2 : (∀ i : Nat, ∀ hi : i < w, R i (patVal (midSt p q w i) (q ⟨w - w + i, by omega⟩)) = true) ↔
      (∀ i : Fin w, R i.val (patVal (shiftSt p q i.val) (q i)) = true) := by
    constructor
    · intro h i
      have hilt : i.val < w := i.isLt
      have hi := h i.val hilt
      have hmid : midSt p q w i.val = shiftSt p q i.val := by
        funext j; simp [midSt, shiftSt]
      have hidx : (⟨w - w + i.val, by omega⟩ : Fin w) = i := by apply Fin.ext; dsimp only; omega
      rw [hmid, hidx] at hi
      exact hi
    · intro h i hi
      have hmid : midSt p q w i = shiftSt p q i := by
        funext j; simp [midSt, shiftSt]
      have hidx : (⟨w - w + i, by omega⟩ : Fin w) = ⟨i, hi⟩ := by apply Fin.ext; dsimp only; omega
      rw [hmid, hidx]
      exact h ⟨i, hi⟩
  exact ite_eq_of_iff ⟨fun ⟨_, ha⟩ => h2.mp ha, fun hb => ⟨h1, h2.mpr hb⟩⟩ 1 0

private def splitRow (d : Nat) (isBob : Bool) (i : Nat) : Row :=
  if i = 0 then
    rowOfTest (fun (s : Fin (d + 2) → Bool) (b : Bool) => (t0Of s == false) && (b == s ⟨0, by omega⟩))
  else if i < d then
    rowOfTest (fun (s : Fin (d + 2) → Bool) (b : Bool) => b == s ⟨0, by omega⟩)
  else if i = d then
    rowOfTest (fun (s : Fin (d + 2) → Bool) (b : Bool) =>
      (s ⟨0, by omega⟩ == false) &&
        (if s ⟨1, by omega⟩ = !isBob then true else b == false))
  else
    rowOfTest (fun (s : Fin (d + 2) → Bool) (b : Bool) => b == s ⟨0, by omega⟩)

private theorem splitMat_spec (d : Nat) (hd : 0 < d) (isBob : Bool) (p q : Fin (d + 2) → Bool) :
    (List.ofFn (fun i : Fin (d + 2) => stepMat (d + 2) (splitRow d isBob i.val))).prod p q =
      if t0Of p = false ∧ payOf q = payOf p ∧ t1Of q = t1Of p ∧
          (t1Of p = !isBob ∨ t0Of q = false)
      then 1 else 0 := by
  rw [prod_w_steps]
  have heqv : (∀ i : Fin (d + 2), splitRow d isBob i.val (patVal (shiftSt p q i.val) (q i)) = true) ↔
      (t0Of p = false ∧ payOf q = payOf p ∧ t1Of q = t1Of p ∧ (t1Of p = !isBob ∨ t0Of q = false)) := by
    constructor
    · intro h
      have h0 := h ⟨0, by omega⟩
      simp only [splitRow, ↓reduceIte, rowOfTest_patVal, Bool.and_eq_true, beq_iff_eq] at h0
      have hsh0 : shiftSt p q 0 = p := by
        funext j; simp [shiftSt, j.isLt]
      rw [hsh0] at h0
      have hpay : payOf q = payOf p := by
        funext j
        by_cases hj0 : j.val = 0
        · have : j = ⟨0, hd⟩ := Fin.ext hj0
          rw [this]; exact h0.2
        · have hj := h ⟨j.val, by omega⟩
          have hne : j.val ≠ 0 := hj0
          have hlt : j.val < d := j.isLt
          simp only [splitRow, hne, ↓reduceIte, hlt, rowOfTest_patVal, beq_iff_eq] at hj
          dsimp only [payOf]
          rw [hj]
          have hlt2 : j.val + 0 < d + 2 := by omega
          dsimp only [shiftSt]
          simp only [hlt2, ↓reduceDIte]
          rfl
      have hd_step := h ⟨d, by omega⟩
      have hd_ne0 : d ≠ 0 := by omega
      simp only [splitRow, hd_ne0, ↓reduceIte, lt_self_iff_false, rowOfTest_patVal,
        Bool.and_eq_true, beq_iff_eq] at hd_step
      have hsh_d0 : shiftSt p q d ⟨0, by omega⟩ = t0Of p := by
        simp [shiftSt, t0Of]
      have hsh_d1 : shiftSt p q d ⟨1, by omega⟩ = t1Of p := by
        simp [shiftSt, t1Of]
      rw [hsh_d0, hsh_d1] at hd_step
      have hd1_step := h ⟨d + 1, by omega⟩
      have hd1_ne0 : d + 1 ≠ 0 := by omega
      have hd1_nlt : ¬ (d + 1 < d) := by omega
      have hd1_ned : d + 1 ≠ d := by omega
      simp only [splitRow, hd1_ne0, ↓reduceIte, hd1_nlt, hd1_ned, rowOfTest_patVal,
        beq_iff_eq] at hd1_step
      have hsh_d10 : shiftSt p q (d + 1) ⟨0, by omega⟩ = t1Of p := by
        simp [shiftSt, t1Of]
      rw [hsh_d10] at hd1_step
      refine ⟨h0.1, hpay, hd1_step, ?_⟩
      by_cases ht1 : t1Of p = !isBob
      · exact Or.inl ht1
      · simp only [ht1, ↓reduceIte, beq_iff_eq] at hd_step
        exact Or.inr hd_step.2
    · intro ⟨ht0, hpay, ht1, hcond⟩ i
      by_cases hi0 : i.val = 0
      · have heq : i = ⟨0, by omega⟩ := Fin.ext hi0
        rw [heq]
        simp only [splitRow, ↓reduceIte, rowOfTest_patVal, Bool.and_eq_true, beq_iff_eq]
        have hsh0 : shiftSt p q 0 = p := by funext j; simp [shiftSt, j.isLt]
        rw [hsh0]
        exact ⟨ht0, congrFun hpay ⟨0, hd⟩⟩
      · by_cases hid : i.val < d
        · simp only [splitRow, hi0, ↓reduceIte, hid, rowOfTest_patVal, beq_iff_eq]
          have hsh : shiftSt p q i.val ⟨0, by omega⟩ = p ⟨i.val, by omega⟩ := by
            simp [shiftSt, hid]
          rw [hsh]
          exact congrFun hpay ⟨i.val, hid⟩
        · by_cases hied : i.val = d
          · have heq : i = ⟨d, by omega⟩ := Fin.ext hied
            rw [heq]
            have hd_ne0 : d ≠ 0 := by omega
            simp only [splitRow, hd_ne0, ↓reduceIte, lt_self_iff_false, rowOfTest_patVal,
              Bool.and_eq_true, beq_iff_eq]
            have hsh_d0 : shiftSt p q d ⟨0, by omega⟩ = t0Of p := by simp [shiftSt, t0Of]
            have hsh_d1 : shiftSt p q d ⟨1, by omega⟩ = t1Of p := by simp [shiftSt, t1Of]
            rw [hsh_d0, hsh_d1]
            refine ⟨ht0, ?_⟩
            split_ifs with h1
            · rfl
            · rcases hcond with hc | hc
              · exact absurd hc h1
              · simp only [beq_iff_eq]; exact hc
          · have hilt : i.val < d + 2 := i.isLt
            have heq : i = ⟨d + 1, by omega⟩ := by apply Fin.ext; dsimp only; omega
            rw [heq]
            have hd1_ne0 : d + 1 ≠ 0 := by omega
            have hd1_nlt : ¬ (d + 1 < d) := by omega
            have hd1_ned : d + 1 ≠ d := by omega
            simp only [splitRow, hd1_ne0, ↓reduceIte, hd1_nlt, hd1_ned, rowOfTest_patVal,
              beq_iff_eq]
            have hsh_d10 : shiftSt p q (d + 1) ⟨0, by omega⟩ = t1Of p := by simp [shiftSt, t1Of]
            rw [hsh_d10]
            exact ht1
  exact ite_eq_of_iff heqv 1 0

private def mergeRow (d : Nat) (isBob : Bool) (i : Nat) : Row :=
  if i = 0 then
    rowOfTest (fun (s : Fin (d + 2) → Bool) (b : Bool) =>
      (!(t0Of s && (t1Of s == isBob))) && (b == s ⟨0, by omega⟩))
  else if i < d then
    rowOfTest (fun (s : Fin (d + 2) → Bool) (b : Bool) => b == s ⟨0, by omega⟩)
  else if i = d then
    rowOfTest (fun (_ : Fin (d + 2) → Bool) (b : Bool) => b == false)
  else
    rowOfTest (fun (s : Fin (d + 2) → Bool) (b : Bool) => b == s ⟨0, by omega⟩)

private theorem mergeMat_spec (d : Nat) (hd : 0 < d) (isBob : Bool) (p q : Fin (d + 2) → Bool) :
    (List.ofFn (fun i : Fin (d + 2) => stepMat (d + 2) (mergeRow d isBob i.val))).prod p q =
      if ¬ (t0Of p = true ∧ t1Of p = isBob) ∧ payOf q = payOf p ∧
          t0Of q = false ∧ t1Of q = t1Of p
      then 1 else 0 := by
  rw [prod_w_steps]
  have heqv : (∀ i : Fin (d + 2), mergeRow d isBob i.val (patVal (shiftSt p q i.val) (q i)) = true) ↔
      (¬ (t0Of p = true ∧ t1Of p = isBob) ∧ payOf q = payOf p ∧ t0Of q = false ∧ t1Of q = t1Of p) := by
    constructor
    · intro h
      have h0 := h ⟨0, by omega⟩
      simp only [mergeRow, ↓reduceIte, rowOfTest_patVal, Bool.and_eq_true, Bool.not_eq_true',
        Bool.and_eq_false_iff, beq_eq_false_iff_ne, beq_iff_eq] at h0
      have hsh0 : shiftSt p q 0 = p := by funext j; simp [shiftSt, j.isLt]
      rw [hsh0] at h0
      have hnotdead : ¬ (t0Of p = true ∧ t1Of p = isBob) := by
        intro ⟨ha, hb⟩
        rcases h0.1 with hfa | hfb
        · rw [ha] at hfa; exact Bool.noConfusion hfa
        · exact hfb hb
      have hpay : payOf q = payOf p := by
        funext j
        by_cases hj0 : j.val = 0
        · have : j = ⟨0, hd⟩ := Fin.ext hj0
          rw [this]; exact h0.2
        · have hj := h ⟨j.val, by omega⟩
          have hlt : j.val < d := j.isLt
          simp only [mergeRow, hj0, ↓reduceIte, hlt, rowOfTest_patVal, beq_iff_eq] at hj
          dsimp only [payOf]
          rw [hj]
          have hlt2 : j.val + 0 < d + 2 := by omega
          dsimp only [shiftSt]
          simp only [hlt2, ↓reduceDIte]
          rfl
      have hd_step := h ⟨d, by omega⟩
      have hd_ne0 : d ≠ 0 := by omega
      simp only [mergeRow, hd_ne0, ↓reduceIte, lt_self_iff_false, rowOfTest_patVal, beq_iff_eq] at hd_step
      have hd1_step := h ⟨d + 1, by omega⟩
      have hd1_ne0 : d + 1 ≠ 0 := by omega
      have hd1_nlt : ¬ (d + 1 < d) := by omega
      have hd1_ned : d + 1 ≠ d := by omega
      simp only [mergeRow, hd1_ne0, ↓reduceIte, hd1_nlt, hd1_ned, rowOfTest_patVal, beq_iff_eq] at hd1_step
      have hsh_d10 : shiftSt p q (d + 1) ⟨0, by omega⟩ = t1Of p := by simp [shiftSt, t1Of]
      rw [hsh_d10] at hd1_step
      exact ⟨hnotdead, hpay, hd_step, hd1_step⟩
    · intro ⟨hnd, hpay, ht0q, ht1q⟩ i
      by_cases hi0 : i.val = 0
      · have heq : i = ⟨0, by omega⟩ := Fin.ext hi0
        rw [heq]
        simp only [mergeRow, ↓reduceIte, rowOfTest_patVal, Bool.and_eq_true, Bool.not_eq_true',
          Bool.and_eq_false_iff, beq_eq_false_iff_ne, beq_iff_eq]
        have hsh0 : shiftSt p q 0 = p := by funext j; simp [shiftSt, j.isLt]
        rw [hsh0]
        refine ⟨?_, congrFun hpay ⟨0, hd⟩⟩
        cases ht0 : t0Of p
        · exact Or.inl rfl
        · right
          intro h1
          exact hnd ⟨ht0, h1⟩
      · by_cases hid : i.val < d
        · simp only [mergeRow, hi0, ↓reduceIte, hid, rowOfTest_patVal, beq_iff_eq]
          have hsh : shiftSt p q i.val ⟨0, by omega⟩ = p ⟨i.val, by omega⟩ := by
            simp [shiftSt, hid]
          rw [hsh]
          exact congrFun hpay ⟨i.val, hid⟩
        · by_cases hied : i.val = d
          · have heq : i = ⟨d, by omega⟩ := Fin.ext hied
            rw [heq]
            have hd_ne0 : d ≠ 0 := by omega
            simp only [mergeRow, hd_ne0, ↓reduceIte, lt_self_iff_false, rowOfTest_patVal, beq_iff_eq]
            exact ht0q
          · have hilt : i.val < d + 2 := i.isLt
            have heq : i = ⟨d + 1, by omega⟩ := by apply Fin.ext; dsimp only; omega
            rw [heq]
            have hd1_ne0 : d + 1 ≠ 0 := by omega
            have hd1_nlt : ¬ (d + 1 < d) := by omega
            have hd1_ned : d + 1 ≠ d := by omega
            simp only [mergeRow, hd1_ne0, ↓reduceIte, hd1_nlt, hd1_ned, rowOfTest_patVal, beq_iff_eq]
            have hsh_d10 : shiftSt p q (d + 1) ⟨0, by omega⟩ = t1Of p := by simp [shiftSt, t1Of]
            rw [hsh_d10]
            exact ht1q
  exact ite_eq_of_iff heqv 1 0

private def aliceGuardRow (d : Nat) (i : Nat) : Row :=
  if i = 0 then
    rowOfTest (fun (s : Fin (d + 2) → Bool) (b : Bool) =>
      (t0Of s == false) && (t1Of s == true) && (b == s ⟨0, by omega⟩))
  else
    rowOfTest (fun (s : Fin (d + 2) → Bool) (b : Bool) => b == s ⟨0, by omega⟩)

private theorem aliceGuard_spec (d : Nat) (p q : Fin (d + 2) → Bool) :
    (List.ofFn (fun i : Fin (d + 2) => stepMat (d + 2) (aliceGuardRow d i.val))).prod p q =
      if q = p ∧ t0Of p = false ∧ t1Of p = true then 1 else 0 := by
  rw [prod_w_steps]
  have heqv : (∀ i : Fin (d + 2), aliceGuardRow d i.val (patVal (shiftSt p q i.val) (q i)) = true) ↔
      (q = p ∧ t0Of p = false ∧ t1Of p = true) := by
    constructor
    · intro h
      have h0 := h ⟨0, by omega⟩
      simp only [aliceGuardRow, ↓reduceIte, rowOfTest_patVal, Bool.and_eq_true, beq_iff_eq] at h0
      have hsh0 : shiftSt p q 0 = p := by funext j; simp [shiftSt, j.isLt]
      rw [hsh0] at h0
      refine ⟨?_, h0.1.1, h0.1.2⟩
      funext i
      by_cases hi0 : i.val = 0
      · have heq : i = ⟨0, by omega⟩ := Fin.ext hi0
        rw [heq]; exact h0.2
      · have hi := h i
        simp only [aliceGuardRow, hi0, ↓reduceIte, rowOfTest_patVal, beq_iff_eq] at hi
        rw [hi]
        simp [shiftSt, i.isLt]
    · intro ⟨hqp, ht0, ht1⟩ i
      subst hqp
      by_cases hi0 : i.val = 0
      · have heq : i = ⟨0, by omega⟩ := Fin.ext hi0
        rw [heq]
        simp only [aliceGuardRow, ↓reduceIte, rowOfTest_patVal, Bool.and_eq_true, beq_iff_eq]
        have hsh0 : shiftSt q q 0 = q := by funext j; simp [shiftSt, j.isLt]
        rw [hsh0]
        exact ⟨⟨ht0, ht1⟩, rfl⟩
      · simp only [aliceGuardRow, hi0, ↓reduceIte, rowOfTest_patVal, beq_iff_eq]
        simp [shiftSt, i.isLt]
  exact ite_eq_of_iff heqv 1 0

private def bxor {w : Nat} (u v : Fin w → Bool) : Fin w → Bool :=
  fun j => xor (u j) (v j)

private def eTopB (w : Nat) : Fin w → Bool :=
  fun j => decide (j.val = w - 1)

private def fbBit {w : Nat} (taps : Fin w → ZMod 2) (s : Fin w → Bool) : Bool :=
  z2b (∑ i : Fin w, taps i * b2z (s i))

private def lfsrStep {w : Nat} (taps : Fin w → ZMod 2) (s : Fin w → Bool) : Fin w → Bool :=
  nextSt s (fbBit taps s)

private def lfsrRow (d : Nat) (taps : Fin (d + 2) → ZMod 2) (isBob : Bool)
    (bm : (Fin d → Bool) → (Fin d → Bool) → Bool) (t : Nat) : Row :=
  let Llen := 2 ^ (d + 2) - 1
  let L := lfsrStep taps
  let delta := L^[Llen - 1 - t] (eTopB (d + 2))
  rowOfTest (fun s bit =>
    (bit == fbBit taps s) ||
      (let u := L^[Llen - t] s
       let v := bxor u delta
       (t0Of u == false) && (t1Of u == isBob) &&
         (t0Of v == false) && (t1Of v == !isBob) && bm (payOf u) (payOf v)))

private theorem lfsrMat_spec (d : Nat) (taps : Fin (d + 2) → ZMod 2)
    (hlin : ∀ u v : Fin (d + 2) → ZMod 2,
      (fun j : Fin (d + 2) => if h : j.val + 1 < d + 2 then (u + v) ⟨j.val + 1, h⟩ else ∑ i, taps i * (u + v) i) =
      (fun j : Fin (d + 2) => if h : j.val + 1 < d + 2 then u ⟨j.val + 1, h⟩ else ∑ i, taps i * u i) +
      (fun j : Fin (d + 2) => if h : j.val + 1 < d + 2 then v ⟨j.val + 1, h⟩ else ∑ i, taps i * v i))
    (hper : ∀ s : Fin (d + 2) → ZMod 2,
      (fun (s : Fin (d + 2) → ZMod 2) (j : Fin (d + 2)) =>
        if h : j.val + 1 < d + 2 then s ⟨j.val + 1, h⟩ else ∑ i, taps i * s i)^[2 ^ (d + 2) - 1] s = s)
    (hgen : ∀ v : Fin (d + 2) → ZMod 2, v ≠ 0 →
      ∃ t < 2 ^ (d + 2) - 1,
        (fun (s : Fin (d + 2) → ZMod 2) (j : Fin (d + 2)) =>
          if h : j.val + 1 < d + 2 then s ⟨j.val + 1, h⟩ else ∑ i, taps i * s i)^[t]
            (fun j => if j.val = d + 1 then 1 else 0) = v)
    (isBob : Bool) (bm : (Fin d → Bool) → (Fin d → Bool) → Bool)
    (p q : Fin (d + 2) → Bool) :
    (List.ofFn (fun t : Fin (2 ^ (d + 2) - 1) =>
      stepMat (d + 2) (lfsrRow d taps isBob bm t.val))).prod p q =
      if q = p then 1
      else if t0Of p = false ∧ t1Of p = isBob ∧ t0Of q = false ∧ t1Of q = !isBob ∧
          bm (payOf p) (payOf q) = true then 1
      else 0 := by
  let w := d + 2
  let Llen := 2 ^ w - 1
  have hLlen_pos : 0 < Llen := by
    have : 4 ≤ 2 ^ w := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  let Lz : (Fin w → ZMod 2) → (Fin w → ZMod 2) := fun s j =>
    if h : j.val + 1 < w then s ⟨j.val + 1, h⟩ else ∑ i : Fin w, taps i * s i
  let Lb : (Fin w → Bool) → (Fin w → Bool) := lfsrStep taps
  let toZ : (Fin w → Bool) → (Fin w → ZMod 2) := fun s j => b2z (s j)
  let toB : (Fin w → ZMod 2) → (Fin w → Bool) := fun s j => z2b (s j)
  have htoZ_toB : ∀ z, toZ (toB z) = z := fun z => by funext j; exact b2z_z2b (z j)
  have htoB_toZ : ∀ s, toB (toZ s) = s := fun s => by funext j; exact z2b_b2z (s j)
  have hLb_conj : ∀ s, toZ (Lb s) = Lz (toZ s) := by
    intro s
    funext j
    dsimp only [toZ, Lb, lfsrStep, nextSt, fbBit, Lz]
    split_ifs with hj
    · rfl
    · exact b2z_z2b _
  have hLb_iter_conj : ∀ m s, toZ (Lb^[m] s) = Lz^[m] (toZ s) := by
    intro m
    induction m with
    | zero => intro s; rfl
    | succ m ih =>
      intro s
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hLb_conj]
  have hLb_lin : ∀ u v, Lb (bxor u v) = bxor (Lb u) (Lb v) := by
    intro u v
    rw [← htoB_toZ (Lb (bxor u v)), ← htoB_toZ (bxor (Lb u) (Lb v))]
    congr 1
    have hbx : ∀ a b, toZ (bxor a b) = toZ a + toZ b := by
      intro a b; funext j; exact b2z_xor (a j) (b j)
    rw [hLb_conj, hbx]
    dsimp only [Lz, w]
    rw [hlin]
    change Lz (toZ u) + Lz (toZ v) = toZ (bxor (Lb u) (Lb v))
    rw [← hLb_conj, ← hLb_conj, ← hbx]
  have hLb_iter_lin : ∀ m u v, Lb^[m] (bxor u v) = bxor (Lb^[m] u) (Lb^[m] v) := by
    intro m
    induction m with
    | zero => intro u v; rfl
    | succ m ih =>
      intro u v
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        hLb_lin, ih]
  have hLb_per : ∀ s, Lb^[Llen] s = s := by
    intro s
    rw [← htoB_toZ (Lb^[Llen] s), hLb_iter_conj, hper, htoB_toZ]
  have hLb_inv_left : ∀ m ≤ Llen, ∀ s, Lb^[Llen - m] (Lb^[m] s) = s := by
    intro m hm s
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hm]
    exact hLb_per s
  have hLb_inv_right : ∀ m ≤ Llen, ∀ s, Lb^[m] (Lb^[Llen - m] s) = s := by
    intro m hm s
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hm]
    exact hLb_per s
  have hLb_inj : Function.Injective Lb := by
    intro s1 s2 h
    have := congrArg (fun x => Lb^[Llen - 1] x) h
    have h1 : Lb^[Llen - 1] (Lb s1) = s1 := by
      rw [← Function.iterate_succ_apply Lb (Llen - 1) s1, Nat.succ_eq_add_one,
        Nat.sub_add_cancel hLlen_pos]
      exact hLb_per s1
    have h2 : Lb^[Llen - 1] (Lb s2) = s2 := by
      rw [← Function.iterate_succ_apply Lb (Llen - 1) s2, Nat.succ_eq_add_one,
        Nat.sub_add_cancel hLlen_pos]
      exact hLb_per s2
    rw [h1, h2] at this
    exact this
  have hbxor_self : ∀ u : Fin w → Bool, bxor u u = (fun _ => false) := by
    intro u; funext j; simp [bxor]
  have hbxor_comm : ∀ u v : Fin w → Bool, bxor u v = bxor v u := by
    intro u v; funext j; simp [bxor, Bool.xor_comm]
  have hbxor_assoc : ∀ a b c : Fin w → Bool, bxor (bxor a b) c = bxor a (bxor b c) := by
    intro a b c; funext j; simp [bxor, Bool.xor_assoc]
  have hbxor_false : ∀ u : Fin w → Bool, bxor u (fun _ => false) = u := by
    intro u; funext j; simp [bxor]
  have hbxor_eq_false_iff : ∀ u v : Fin w → Bool, bxor u v = (fun _ => false) ↔ u = v := by
    intro u v
    constructor
    · intro h
      funext j
      have := congrFun h j
      dsimp only [bxor] at this
      cases hu : u j <;> cases hv : v j <;> simp_all
    · intro h; subst h; exact hbxor_self u
  have heTop_ne : eTopB w ≠ (fun _ => false) := by
    intro h
    have := congrFun h ⟨w - 1, by omega⟩
    simp [eTopB] at this
  have hflip_eq : ∀ s : Fin w → Bool, nextSt s (!(fbBit taps s)) = bxor (Lb s) (eTopB w) := by
    intro s
    funext j
    dsimp only [nextSt, Lb, lfsrStep, bxor, eTopB]
    by_cases hj : j.val + 1 < w
    · have hne : j.val ≠ w - 1 := by omega
      simp [hj, hne]
    · simp only [hj, ↓reduceDIte]
      have heq : j.val = w - 1 := by omega
      simp only [heq, decide_true]
      cases fbBit taps s <;> decide
  have hdelta_gen : ∀ v : Fin w → Bool, v ≠ (fun _ => false) →
      ∃ t < Llen, Lb^[Llen - 1 - t] (eTopB w) = v := by
    intro v hv
    have hvz : toZ v ≠ 0 := by
      intro h0
      apply hv
      funext j
      have := congrFun h0 j
      dsimp only [toZ, b2z] at this
      cases h : v j
      · rfl
      · simp [h] at this
    obtain ⟨m, hm, hzm⟩ := hgen (toZ v) hvz
    have hm_Llen : m < Llen := hm
    refine ⟨Llen - 1 - m, by omega, ?_⟩
    have heq_idx : Llen - 1 - (Llen - 1 - m) = m := by omega
    rw [heq_idx, ← htoB_toZ (Lb^[m] (eTopB w)), hLb_iter_conj]
    have heTopZ : toZ (eTopB w) = (fun j : Fin w => if j.val = d + 1 then 1 else 0) := by
      funext j
      dsimp only [toZ, eTopB, b2z]
      have hw1 : w - 1 = d + 1 := by omega
      by_cases h : j.val = d + 1 <;> simp [h, hw1]
    rw [heTopZ, hzm, htoB_toZ]
  have hdelta_inj : ∀ t1 < Llen, ∀ t2 < Llen,
      Lb^[Llen - 1 - t1] (eTopB w) = Lb^[Llen - 1 - t2] (eTopB w) → t1 = t2 := by
    let Snon : Finset (Fin w → Bool) := Finset.univ.filter (fun v => v ≠ (fun _ => false))
    have hcard_Snon : Snon.card = Llen := by
      have h1 : Snon = Finset.univ.erase (fun _ => false) := by
        ext v; simp [Snon]
      rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin]
    let f : Fin Llen → {v : Fin w → Bool // v ∈ Snon} := fun t =>
      ⟨Lb^[Llen - 1 - t.val] (eTopB w), by
        simp only [Snon, Finset.mem_filter, Finset.mem_univ, true_and]
        intro h0
        have hLb0 : ∀ m, Lb^[m] (fun _ => false) = (fun _ => false) := by
          intro m
          have h := hLb_iter_lin m (fun _ => false) (fun _ => false)
          rw [hbxor_self, hbxor_self] at h
          exact h
        have hback := congrArg (fun x => Lb^[t.val + 1] x) h0
        rw [hLb0, ← Function.iterate_add_apply] at hback
        have hsum : t.val + 1 + (Llen - 1 - t.val) = Llen := by omega
        rw [hsum, hLb_per] at hback
        exact heTop_ne hback⟩
    have hsurj : Function.Surjective f := by
      intro ⟨v, hv⟩
      simp only [Snon, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      obtain ⟨t, ht, htv⟩ := hdelta_gen v hv
      exact ⟨⟨t, ht⟩, Subtype.ext htv⟩
    have hcard_eq : Fintype.card (Fin Llen) = Fintype.card {v : Fin w → Bool // v ∈ Snon} := by
      rw [Fintype.card_fin, Fintype.card_coe, hcard_Snon]
    have hinj := ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hcard_eq⟩).1
    intro t1 ht1 t2 ht2 h
    have := hinj (show f ⟨t1, ht1⟩ = f ⟨t2, ht2⟩ from Subtype.ext h)
    exact congrArg Fin.val this
  have hpart : ∀ m ≤ Llen, ∀ s : Fin w → Bool,
      (List.ofFn (fun t : Fin m => stepMat w (lfsrRow d taps isBob bm t.val))).prod p s =
        if s = Lb^[m] p then 1
        else if t0Of p = false ∧ t1Of p = isBob ∧
            t0Of (Lb^[Llen - m] s) = false ∧ t1Of (Lb^[Llen - m] s) = !isBob ∧
            (∃ t < m, bxor p (Lb^[Llen - m] s) = Lb^[Llen - 1 - t] (eTopB w)) ∧
            bm (payOf p) (payOf (Lb^[Llen - m] s)) = true then 1
        else 0 := by
    intro m
    induction m with
    | zero =>
      intro _ s
      simp only [List.ofFn_zero, List.prod_nil, Matrix.one_apply, Function.iterate_zero, id_eq,
        not_lt_zero', false_and, exists_false, and_false, ↓reduceIte]
      by_cases h1 : p = s
      · subst h1; simp
      · have h2 : s ≠ p := fun h => h1 h.symm
        simp [h1, h2]
    | succ m ih =>
      intro hm s
      rw [prefixProd_succ, Matrix.mul_apply]
      let rNorm : Fin w → Bool := Lb^[Llen - 1] s
      let rFlip : Fin w → Bool := Lb^[Llen - 1] (bxor s (eTopB w))
      have hLb_back : ∀ x : Fin w → Bool, Lb (Lb^[Llen - 1] x) = x := by
        intro x
        rw [← Function.iterate_succ_apply' Lb (Llen - 1) x, Nat.succ_eq_add_one,
          Nat.sub_add_cancel hLlen_pos]
        exact hLb_per x
      have hrNorm_step : Lb rNorm = s := hLb_back s
      have hLb_rFlip : Lb rFlip = bxor s (eTopB w) := hLb_back (bxor s (eTopB w))
      have hrFlip_step : nextSt rFlip (!(fbBit taps rFlip)) = s := by
        rw [hflip_eq, hLb_rFlip, hbxor_assoc, hbxor_self, hbxor_false]
      have hstep_r : ∀ r : Fin w → Bool,
          stepMat w (lfsrRow d taps isBob bm m) r s =
            (if r = rNorm then 1 else 0) +
            (if r = rFlip ∧
                (t0Of (Lb^[Llen - m] r) = false ∧ t1Of (Lb^[Llen - m] r) = isBob ∧
                 t0Of (bxor (Lb^[Llen - m] r) (Lb^[Llen - 1 - m] (eTopB w))) = false ∧
                 t1Of (bxor (Lb^[Llen - m] r) (Lb^[Llen - 1 - m] (eTopB w))) = !isBob ∧
                 bm (payOf (Lb^[Llen - m] r))
                   (payOf (bxor (Lb^[Llen - m] r) (Lb^[Llen - 1 - m] (eTopB w)))) = true)
              then 1 else 0) := by
        intro r
        dsimp only [lfsrRow]
        rw [stepMat_rowOfTest]
        simp only [Matrix.of_apply]
        have hsplit_bool : ∀ (P : Bool → Prop) [DecidablePred P],
            (Finset.univ.filter P).card =
              (if P (fbBit taps r) then 1 else 0) + (if P (!(fbBit taps r)) then 1 else 0) := by
          intro P _
          rw [Finset.card_filter, Fintype.sum_bool]
          cases fbBit taps r
          · simp only [Bool.not_false, add_comm]
          · simp only [Bool.not_true]
        rw [hsplit_bool]
        congr 1
        · have h1 : nextSt r (fbBit taps r) = s ↔ r = rNorm := by
            constructor
            · intro h; apply hLb_inj; exact h.trans hrNorm_step.symm
            · intro h; subst h; exact hrNorm_step
          simp only [beq_self_eq_true, Bool.true_or, true_and, h1]
        · have hne_bit : ∀ b : Bool, ((!b) == b) = false := by
            intro b; cases b <;> decide
          have h2 : nextSt r (!(fbBit taps r)) = s ↔ r = rFlip := by
            constructor
            · intro h
              rw [hflip_eq] at h
              apply hLb_inj
              rw [hLb_rFlip, ← h, hbxor_assoc, hbxor_self, hbxor_false]
            · intro h; subst h; exact hrFlip_step
          simp only [hne_bit, Bool.false_or, Bool.and_eq_true, beq_iff_eq, h2, and_assoc]
          exact ite_eq_of_iff
            ⟨fun ⟨ha, hb, hc, hd', he, hr'⟩ => ⟨hr', ha, hb, hc, hd', he⟩,
             fun ⟨hr', ha, hb, hc, hd', he⟩ => ⟨ha, hb, hc, hd', he, hr'⟩⟩ 1 0
      let P_m := (List.ofFn (fun t : Fin m => stepMat w (lfsrRow d taps isBob bm t.val))).prod
      have hsum_two : (∑ r : Fin w → Bool, P_m p r * stepMat w (lfsrRow d taps isBob bm m) r s) =
          P_m p rNorm +
          (if t0Of (Lb^[Llen - m] rFlip) = false ∧ t1Of (Lb^[Llen - m] rFlip) = isBob ∧
              t0Of (bxor (Lb^[Llen - m] rFlip) (Lb^[Llen - 1 - m] (eTopB w))) = false ∧
              t1Of (bxor (Lb^[Llen - m] rFlip) (Lb^[Llen - 1 - m] (eTopB w))) = !isBob ∧
              bm (payOf (Lb^[Llen - m] rFlip))
                (payOf (bxor (Lb^[Llen - m] rFlip) (Lb^[Llen - 1 - m] (eTopB w)))) = true
           then P_m p rFlip else 0) := by
        simp_rw [hstep_r, mul_add, Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_eq_single rNorm]
          · simp only [↓reduceIte, mul_one]
          · intro r _ hr; simp only [hr, ↓reduceIte, mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [Finset.sum_eq_single rFlip]
          · have htr : ∀ (Q : Prop) [Decidable Q],
                P_m p rFlip * (if rFlip = rFlip ∧ Q then 1 else 0) = if Q then P_m p rFlip else 0 := by
              intro Q _; by_cases hQ : Q <;> simp [hQ]
            exact htr _
          · intro r _ hr
            have hc' : ¬ (r = rFlip ∧ t0Of (Lb^[Llen - m] r) = false ∧ t1Of (Lb^[Llen - m] r) = isBob ∧
                t0Of (bxor (Lb^[Llen - m] r) (Lb^[Llen - 1 - m] (eTopB w))) = false ∧
                t1Of (bxor (Lb^[Llen - m] r) (Lb^[Llen - 1 - m] (eTopB w))) = !isBob ∧
                bm (payOf (Lb^[Llen - m] r))
                  (payOf (bxor (Lb^[Llen - m] r) (Lb^[Llen - 1 - m] (eTopB w)))) = true) :=
              fun h => hr h.1
            simp only [hc', ↓reduceIte, mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum_two]
      have hNorm_inv : Lb^[Llen - m] rNorm = Lb^[Llen - (m + 1)] s := by
        dsimp only [rNorm]
        rw [← Function.iterate_add_apply]
        have h1 : Llen - m + (Llen - 1) = Llen + (Llen - (m + 1)) := by omega
        rw [h1, Function.iterate_add_apply, hLb_per]
      have hFlip_inv : bxor (Lb^[Llen - m] rFlip) (Lb^[Llen - 1 - m] (eTopB w)) =
          Lb^[Llen - (m + 1)] s := by
        dsimp only [rFlip]
        rw [← Function.iterate_add_apply]
        have h1 : Llen - m + (Llen - 1) = Llen + (Llen - (m + 1)) := by omega
        rw [h1, Function.iterate_add_apply, hLb_per, hLb_iter_lin, hbxor_assoc]
        have h2 : Llen - (m + 1) = Llen - 1 - m := by omega
        rw [h2, hbxor_self, hbxor_false]
      have hrNorm_eq_iff : rNorm = Lb^[m] p ↔ s = Lb^[m + 1] p := by
        constructor
        · intro h
          rw [← hrNorm_step, h, ← Function.iterate_succ_apply' Lb m p]
        · intro h
          apply hLb_inj
          rw [hrNorm_step, h, Function.iterate_succ_apply' Lb m p]
      have hrFlip_eq_iff : rFlip = Lb^[m] p ↔
          bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - m] (eTopB w) := by
        constructor
        · intro h
          have h1 : Lb^[Llen - m] rFlip = p := by
            rw [h]; exact hLb_inv_left m (by omega) p
          rw [← hFlip_inv, h1, ← hbxor_assoc, hbxor_self, hbxor_comm, hbxor_false]
        · intro h
          have h1 : Lb^[Llen - m] rFlip = p := by
            have h2 := congrArg (fun x => bxor x (Lb^[Llen - 1 - m] (eTopB w))) hFlip_inv
            rw [hbxor_assoc, hbxor_self, hbxor_false] at h2
            rw [h2, ← h, ← hbxor_assoc, hbxor_comm (Lb^[Llen - (m + 1)] s) p, hbxor_assoc,
              hbxor_self, hbxor_false]
          have h3 := congrArg (fun x => Lb^[m] x) h1
          rw [hLb_inv_right m (by omega)] at h3
          exact h3
      have hPm_norm := ih (by omega) rNorm
      have hPm_flip := ih (by omega) rFlip
      dsimp only [P_m] at hsum_two ⊢
      simp only [hPm_norm, hPm_flip, hNorm_inv, hFlip_inv, hrNorm_eq_iff, hrFlip_eq_iff]
      have hnotis : ¬ (isBob = !isBob) := by cases isBob <;> decide
      have hflip_simp : (if t0Of (Lb^[Llen - m] rFlip) = false ∧ t1Of (Lb^[Llen - m] rFlip) = isBob ∧
          t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
          bm (payOf (Lb^[Llen - m] rFlip)) (payOf (Lb^[Llen - (m + 1)] s)) = true
        then if bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - m] (eTopB w) then 1
             else if t0Of p = false ∧ t1Of p = isBob ∧
                 t0Of (Lb^[Llen - m] rFlip) = false ∧ t1Of (Lb^[Llen - m] rFlip) = !isBob ∧
                 (∃ t < m, bxor p (Lb^[Llen - m] rFlip) = Lb^[Llen - 1 - t] (eTopB w)) ∧
                 bm (payOf p) (payOf (Lb^[Llen - m] rFlip)) = true then 1 else 0
        else 0) =
        if t0Of p = false ∧ t1Of p = isBob ∧
           t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
           bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - m] (eTopB w) ∧
           bm (payOf p) (payOf (Lb^[Llen - (m + 1)] s)) = true then 1 else 0 := by
        by_cases ha : t0Of (Lb^[Llen - m] rFlip) = false ∧ t1Of (Lb^[Llen - m] rFlip) = isBob ∧
            t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
            bm (payOf (Lb^[Llen - m] rFlip)) (payOf (Lb^[Llen - (m + 1)] s)) = true
        · rw [if_pos ha]
          by_cases hb : bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - m] (eTopB w)
          · have hp_eq : Lb^[Llen - m] rFlip = p := by
              have h1 := hrFlip_eq_iff.mpr hb
              rw [h1]; exact hLb_inv_left m (by omega) p
            have hd : t0Of p = false ∧ t1Of p = isBob ∧
                t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
                bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - m] (eTopB w) ∧
                bm (payOf p) (payOf (Lb^[Llen - (m + 1)] s)) = true := by
              rw [hp_eq] at ha
              exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, hb, ha.2.2.2.2⟩
            rw [if_pos hb, if_pos hd]
          · have hnotc : ¬ (t0Of p = false ∧ t1Of p = isBob ∧
                t0Of (Lb^[Llen - m] rFlip) = false ∧ t1Of (Lb^[Llen - m] rFlip) = !isBob ∧
                (∃ t < m, bxor p (Lb^[Llen - m] rFlip) = Lb^[Llen - 1 - t] (eTopB w)) ∧
                bm (payOf p) (payOf (Lb^[Llen - m] rFlip)) = true) := by
              intro hc; exact hnotis (ha.2.1.symm.trans hc.2.2.2.1)
            have hnotd : ¬ (t0Of p = false ∧ t1Of p = isBob ∧
                t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
                bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - m] (eTopB w) ∧
                bm (payOf p) (payOf (Lb^[Llen - (m + 1)] s)) = true) :=
              fun hd => hb hd.2.2.2.2.1
            rw [if_neg hb, if_neg hnotc, if_neg hnotd]
        · rw [if_neg ha]
          have hnotd : ¬ (t0Of p = false ∧ t1Of p = isBob ∧
              t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
              bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - m] (eTopB w) ∧
              bm (payOf p) (payOf (Lb^[Llen - (m + 1)] s)) = true) := by
            intro hd
            have hp_eq : Lb^[Llen - m] rFlip = p := by
              have h1 := hrFlip_eq_iff.mpr hd.2.2.2.2.1
              rw [h1]; exact hLb_inv_left m (by omega) p
            apply ha
            rw [hp_eq]
            exact ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.2⟩
          rw [if_neg hnotd]
      rw [hflip_simp]
      by_cases hdiag : s = Lb^[m + 1] p
      · have hnotflip : ¬ (bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - m] (eTopB w)) := by
          rw [hdiag, hLb_inv_left (m + 1) hm, hbxor_self]
          intro h0
          have hback := congrArg (fun x => Lb^[m + 1] x) h0
          have hLb0 : Lb^[m + 1] (fun _ => false) = (fun _ => false) := by
            have h := hLb_iter_lin (m + 1) (fun _ => false) (fun _ => false)
            rw [hbxor_self, hbxor_self] at h; exact h
          rw [hLb0, ← Function.iterate_add_apply] at hback
          have hsum : m + 1 + (Llen - 1 - m) = Llen := by omega
          rw [hsum, hLb_per] at hback
          exact heTop_ne hback.symm
        have hnotd : ¬ (t0Of p = false ∧ t1Of p = isBob ∧
            t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
            bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - m] (eTopB w) ∧
            bm (payOf p) (payOf (Lb^[Llen - (m + 1)] s)) = true) :=
          fun hd => hnotflip hd.2.2.2.2.1
        simp only [hnotd, ↓reduceIte, add_zero]
        simp only [hdiag, ↓reduceIte]
      · simp only [hdiag, ↓reduceIte]
        by_cases hcond_lt : t0Of p = false ∧ t1Of p = isBob ∧
            t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
            (∃ t < m, bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - t] (eTopB w)) ∧
            bm (payOf p) (payOf (Lb^[Llen - (m + 1)] s)) = true
        · have hnotm : ¬ (t0Of p = false ∧ t1Of p = isBob ∧
              t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
              bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - m] (eTopB w) ∧
              bm (payOf p) (payOf (Lb^[Llen - (m + 1)] s)) = true) := by
            intro hm_cond
            obtain ⟨t, ht, hteq⟩ := hcond_lt.2.2.2.2.1
            have := hdelta_inj t (by omega) m (by omega) (hteq.symm.trans hm_cond.2.2.2.2.1)
            omega
          have hcond_succ : t0Of p = false ∧ t1Of p = isBob ∧
              t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
              (∃ t < m + 1, bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - t] (eTopB w)) ∧
              bm (payOf p) (payOf (Lb^[Llen - (m + 1)] s)) = true := by
            obtain ⟨t, ht, hteq⟩ := hcond_lt.2.2.2.2.1
            exact ⟨hcond_lt.1, hcond_lt.2.1, hcond_lt.2.2.1, hcond_lt.2.2.2.1,
              ⟨t, by omega, hteq⟩, hcond_lt.2.2.2.2.2⟩
          rw [if_pos hcond_lt, if_neg hnotm, if_pos hcond_succ]
        · by_cases hcond_m : t0Of p = false ∧ t1Of p = isBob ∧
              t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
              bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - m] (eTopB w) ∧
              bm (payOf p) (payOf (Lb^[Llen - (m + 1)] s)) = true
          · have hcond_succ : t0Of p = false ∧ t1Of p = isBob ∧
                t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
                (∃ t < m + 1, bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - t] (eTopB w)) ∧
                bm (payOf p) (payOf (Lb^[Llen - (m + 1)] s)) = true :=
              ⟨hcond_m.1, hcond_m.2.1, hcond_m.2.2.1, hcond_m.2.2.2.1,
                ⟨m, Nat.lt_succ_self m, hcond_m.2.2.2.2.1⟩, hcond_m.2.2.2.2.2⟩
            rw [if_neg hcond_lt, if_pos hcond_m, if_pos hcond_succ]
          · have hnot_succ : ¬ (t0Of p = false ∧ t1Of p = isBob ∧
                t0Of (Lb^[Llen - (m + 1)] s) = false ∧ t1Of (Lb^[Llen - (m + 1)] s) = !isBob ∧
                (∃ t < m + 1, bxor p (Lb^[Llen - (m + 1)] s) = Lb^[Llen - 1 - t] (eTopB w)) ∧
                bm (payOf p) (payOf (Lb^[Llen - (m + 1)] s)) = true) := by
              intro ⟨a1, a2, a3, a4, ⟨t, ht, hteq⟩, a5⟩
              by_cases htm : t < m
              · exact hcond_lt ⟨a1, a2, a3, a4, ⟨t, htm, hteq⟩, a5⟩
              · have hte : t = m := by omega
                subst hte
                exact hcond_m ⟨a1, a2, a3, a4, hteq, a5⟩
            simp only [hcond_lt, hcond_m, hnot_succ, ↓reduceIte, add_zero]
  have hfin := hpart Llen (le_refl Llen) q
  simp only [Nat.sub_self, Function.iterate_zero, id_eq, hLb_per] at hfin
  rw [hfin]
  by_cases hqp : q = p
  · simp [hqp]
  · simp only [hqp, ↓reduceIte]
    have hne : bxor p q ≠ (fun _ => false) := by
      intro h0
      exact hqp ((hbxor_eq_false_iff p q).mp h0).symm
    have hex : ∃ t < Llen, bxor p q = Lb^[Llen - 1 - t] (eTopB w) := by
      obtain ⟨t, ht, htv⟩ := hdelta_gen (bxor p q) hne
      exact ⟨t, ht, htv.symm⟩
    simp [hex]

private def layerLen (d : Nat) : Nat := 2 * (d + 2) + (2 ^ (d + 2) - 1)

private def layerRow (d : Nat) (taps : Fin (d + 2) → ZMod 2) (isBob : Bool)
    (bm : (Fin d → Bool) → (Fin d → Bool) → Bool) (i : Nat) : Row :=
  let w := d + 2
  let Llen := 2 ^ w - 1
  if i < w then splitRow d isBob i
  else if i < w + Llen then lfsrRow d taps isBob bm (i - w)
  else mergeRow d isBob (i - (w + Llen))

private theorem layerMat_spec (d : Nat) (hd : 0 < d) (taps : Fin (d + 2) → ZMod 2)
    (hlin : ∀ u v : Fin (d + 2) → ZMod 2,
      (fun j : Fin (d + 2) => if h : j.val + 1 < d + 2 then (u + v) ⟨j.val + 1, h⟩ else ∑ i, taps i * (u + v) i) =
      (fun j : Fin (d + 2) => if h : j.val + 1 < d + 2 then u ⟨j.val + 1, h⟩ else ∑ i, taps i * u i) +
      (fun j : Fin (d + 2) => if h : j.val + 1 < d + 2 then v ⟨j.val + 1, h⟩ else ∑ i, taps i * v i))
    (hper : ∀ s : Fin (d + 2) → ZMod 2,
      (fun (s : Fin (d + 2) → ZMod 2) (j : Fin (d + 2)) =>
        if h : j.val + 1 < d + 2 then s ⟨j.val + 1, h⟩ else ∑ i, taps i * s i)^[2 ^ (d + 2) - 1] s = s)
    (hgen : ∀ v : Fin (d + 2) → ZMod 2, v ≠ 0 →
      ∃ t < 2 ^ (d + 2) - 1,
        (fun (s : Fin (d + 2) → ZMod 2) (j : Fin (d + 2)) =>
          if h : j.val + 1 < d + 2 then s ⟨j.val + 1, h⟩ else ∑ i, taps i * s i)^[t]
            (fun j => if j.val = d + 1 then 1 else 0) = v)
    (isBob : Bool) (bm : (Fin d → Bool) → (Fin d → Bool) → Bool)
    (p q : Fin (d + 2) → Bool) :
    (List.ofFn (fun i : Fin (layerLen d) =>
      stepMat (d + 2) (layerRow d taps isBob bm i.val))).prod p q =
      if t0Of p = false ∧ t0Of q = false then
        if t1Of p = isBob ∧ t1Of q = isBob then (if payOf q = payOf p then 1 else 0)
        else if t1Of p = isBob ∧ t1Of q = !isBob then (if bm (payOf p) (payOf q) = true then 1 else 0)
        else if t1Of p = !isBob ∧ t1Of q = !isBob then (if payOf q = payOf p then 2 else 0)
        else 0
      else 0 := by
  let w := d + 2
  let Llen := 2 ^ w - 1
  have hlen : layerLen d = (w + Llen) + w := by dsimp [layerLen, w, Llen]; omega
  let SMat := (List.ofFn (fun i : Fin w => stepMat w (splitRow d isBob i.val))).prod
  let LMat := (List.ofFn (fun t : Fin Llen => stepMat w (lfsrRow d taps isBob bm t.val))).prod
  let MMat := (List.ofFn (fun i : Fin w => stepMat w (mergeRow d isBob i.val))).prod
  have hprod : (List.ofFn (fun i : Fin (layerLen d) =>
        stepMat w (layerRow d taps isBob bm i.val))).prod = SMat * LMat * MMat := by
    have heq1 : (List.ofFn (fun i : Fin (layerLen d) =>
          stepMat w (layerRow d taps isBob bm i.val))).prod =
        (List.ofFn (fun i : Fin ((w + Llen) + w) =>
          stepMat w (layerRow d taps isBob bm i.val))).prod := by
      congr 1
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2; simp only [List.getElem_ofFn]
    rw [heq1, list_ofFn_add_prod (w + Llen) w, list_ofFn_add_prod w Llen]
    congr 1
    · congr 1
      · congr 2; funext i; simp [layerRow, i.isLt, w]
      · congr 2; funext t
        have h1 : ¬ (w + t.val < w) := by omega
        have h2 : w + t.val < w + Llen := by omega
        simp [layerRow, h1, h2, w, Llen]
    · congr 2; funext i
      have h1 : ¬ (w + Llen + i.val < w) := by omega
      have h2 : ¬ (w + Llen + i.val < w + Llen) := by omega
      simp [layerRow, h1, h2, w, Llen]
  rw [hprod, Matrix.mul_apply]
  have hS_eq : ∀ a b, SMat a b =
      if t0Of a = false ∧ payOf b = payOf a ∧ t1Of b = t1Of a ∧ (t1Of a = !isBob ∨ t0Of b = false)
      then 1 else 0 := splitMat_spec d hd isBob
  have hL_eq : ∀ a b, LMat a b =
      if b = a then 1
      else if t0Of a = false ∧ t1Of a = isBob ∧ t0Of b = false ∧ t1Of b = !isBob ∧
          bm (payOf a) (payOf b) = true then 1 else 0 :=
    lfsrMat_spec d taps hlin hper hgen isBob bm
  have hM_eq : ∀ a b, MMat a b =
      if ¬ (t0Of a = true ∧ t1Of a = isBob) ∧ payOf b = payOf a ∧ t0Of b = false ∧ t1Of b = t1Of a
      then 1 else 0 := mergeMat_spec d hd isBob
  have hSL : ∀ s : Fin w → Bool, (SMat * LMat) p s =
      if t0Of p = false then
        if t1Of p = isBob then
          if s = p then 1
          else if t0Of s = false ∧ t1Of s = !isBob ∧ bm (payOf p) (payOf s) = true then 1
          else 0
        else
          if payOf s = payOf p ∧ t1Of s = !isBob then 1 else 0
      else 0 := by
    intro s
    rw [Matrix.mul_apply]
    by_cases ht0p : t0Of p = false
    · by_cases ht1p : t1Of p = isBob
      · have hne : t1Of p ≠ !isBob := by rw [ht1p]; cases isBob <;> decide
        rw [Finset.sum_eq_single p]
        · rw [hS_eq p p, hL_eq p s]
          simp [ht0p, ht1p]
        · intro r _ hr
          rw [hS_eq p r]
          have hfalse : ¬ (t0Of p = false ∧ payOf r = payOf p ∧ t1Of r = t1Of p ∧
              (t1Of p = !isBob ∨ t0Of r = false)) := by
            intro ⟨_, hpay, ht1, hcond⟩
            apply hr
            rw [← mkSt_eta r, ← mkSt_eta p, hpay, ht1]
            rcases hcond with hc | hc
            · exact absurd hc hne
            · rw [hc, ht0p]
          simp [hfalse]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have ht1p' : t1Of p = !isBob := by
          cases h1 : t1Of p <;> cases isBob <;> simp_all
        let r0 := mkSt (payOf p) false (!isBob)
        let r1 := mkSt (payOf p) true (!isBob)
        have hr01 : r0 ≠ r1 := by
          intro h; have := congrArg t0Of h; simp [r0, r1, t0Of_mkSt] at this
        have hsum2 : (∑ r : Fin w → Bool, SMat p r * LMat r s) =
            SMat p r0 * LMat r0 s + SMat p r1 * LMat r1 s := by
          rw [← Finset.sum_subset (s₁ := {r0, r1}) (fun _ _ => Finset.mem_univ _)]
          · rw [Finset.sum_pair hr01]
          · intro r _ hr
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
            rw [hS_eq p r]
            have hfalse : ¬ (t0Of p = false ∧ payOf r = payOf p ∧ t1Of r = t1Of p ∧
                (t1Of p = !isBob ∨ t0Of r = false)) := by
              intro ⟨_, hpay, ht1, _⟩
              cases htr0 : t0Of r
              · apply hr.1; rw [← mkSt_eta r, hpay, htr0, ht1, ht1p']
              · apply hr.2; rw [← mkSt_eta r, hpay, htr0, ht1, ht1p']
            simp [hfalse]
        rw [hsum2, hS_eq p r0, hS_eq p r1, hL_eq r0 s, hL_eq r1 s]
        have hnotis : (!isBob) ≠ isBob := by cases isBob <;> decide
        have hne01 : mkSt (payOf p) false (!isBob) ≠ mkSt (payOf p) true (!isBob) := hr01
        simp only [ht0p, ht1p, ht1p', ↓reduceIte, payOf_mkSt, t0Of_mkSt, t1Of_mkSt, r0, r1,
          hnotis, false_and, and_false, true_and, or_true, one_mul, Bool.true_eq_false]
        by_cases hs : payOf s = payOf p ∧ t1Of s = !isBob
        · simp only [hs, ↓reduceIte]
          cases hts0 : t0Of s
          · have hsr0 : s = mkSt (payOf p) false (!isBob) := by
              rw [← mkSt_eta s, hs.1, hts0, hs.2]
            simp only [hsr0, hne01, hnotis, false_and, and_self, true_or, ↓reduceIte, one_mul, mul_zero, add_zero]
          · have hsr1 : s = mkSt (payOf p) true (!isBob) := by
              rw [← mkSt_eta s, hs.1, hts0, hs.2]
            simp only [hsr1, hne01.symm, hnotis, false_and, and_self, true_or, ↓reduceIte, one_mul, mul_one, zero_add]
        · simp only [hs, ↓reduceIte]
          have hsr0 : s ≠ mkSt (payOf p) false (!isBob) := by
            intro h; apply hs; rw [h]; simp [payOf_mkSt, t1Of_mkSt]
          have hsr1 : s ≠ mkSt (payOf p) true (!isBob) := by
            intro h; apply hs; rw [h]; simp [payOf_mkSt, t1Of_mkSt]
          simp only [hsr0, hsr1, hnotis, false_and, true_or, ↓reduceIte, mul_zero, add_zero]
    · simp only [ht0p, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro r _
      rw [hS_eq p r]
      simp [ht0p]
  simp_rw [hSL]
  by_cases ht0p : t0Of p = false
  · by_cases ht0q : t0Of q = false
    · simp only [ht0p, ht0q, and_self, ↓reduceIte]
      by_cases ht1p : t1Of p = isBob
      · by_cases ht1q : t1Of q = isBob
        · simp only [ht1p, ht1q, and_self, ↓reduceIte]
          rw [Finset.sum_eq_single p]
          · rw [hM_eq p q]
            simp [ht0p, ht0q, ht1p, ht1q]
          · intro s _ hs
            rw [hM_eq s q]
            by_cases hcond : t0Of s = false ∧ t1Of s = !isBob ∧ bm (payOf p) (payOf s) = true
            · have hne : t1Of q ≠ t1Of s := by rw [ht1q, hcond.2.1]; cases isBob <;> decide
              simp [hs, hne]
            · simp [hs, hcond]
          · intro h; exact absurd (Finset.mem_univ _) h
        · have ht1q' : t1Of q = !isBob := by cases h1 : t1Of q <;> cases isBob <;> simp_all
          simp only [ht1p, ht1q, ht1q', and_false, and_self, ↓reduceIte]
          rw [Finset.sum_eq_single q]
          · rw [hM_eq q q]
            have hqp : q ≠ p := by
              intro h; rw [h, ht1p] at ht1q; exact ht1q rfl
            simp [hqp, ht0q, ht1q']
          · intro s _ hs
            rw [hM_eq s q]
            by_cases hsp : s = p
            · subst hsp
              have hne : t1Of q ≠ t1Of s := by rw [ht1q', ht1p]; cases isBob <;> decide
              simp [hne]
            · simp only [hsp, ↓reduceIte]
              have hfalse : ¬ (t0Of s = false ∧ t1Of s = !isBob ∧ bm (payOf p) (payOf s) = true ∧
                  ¬ (t0Of s = true ∧ t1Of s = isBob) ∧ payOf q = payOf s ∧
                  t0Of q = false ∧ t1Of q = t1Of s) := by
                intro ⟨hts0, hts1, _, _, hpay, _, _⟩
                apply hs
                rw [← mkSt_eta s, ← mkSt_eta q, hpay, hts0, ht0q, hts1, ht1q']
              by_cases h1 : t0Of s = false ∧ t1Of s = !isBob ∧ bm (payOf p) (payOf s) = true
              · have h2 : ¬ (¬ (t0Of s = true ∧ t1Of s = isBob) ∧ payOf q = payOf s ∧
                    t0Of q = false ∧ t1Of q = t1Of s) :=
                  fun h2 => hfalse ⟨h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩
                simp only [h2, ↓reduceIte, mul_zero]
              · simp only [h1, ↓reduceIte, zero_mul]
          · intro h; exact absurd (Finset.mem_univ _) h
      · have ht1p' : t1Of p = !isBob := by
          cases h1 : t1Of p <;> cases isBob <;> first | rfl | exact absurd h1 ht1p
        have hnotis : (!isBob) ≠ isBob := by cases isBob <;> decide
        simp only [ht1p, ↓reduceIte]
        by_cases ht1q : t1Of q = !isBob
        · simp only [ht1p', ht1q, hnotis, false_and, and_self, ↓reduceIte]
          let s0 := mkSt (payOf p) false (!isBob)
          let s1 := mkSt (payOf p) true (!isBob)
          have hs01 : s0 ≠ s1 := by
            intro h; have := congrArg t0Of h; simp [s0, s1, t0Of_mkSt] at this
          have hsum2 : (∑ s : Fin w → Bool,
                (if payOf s = payOf p ∧ t1Of s = !isBob then 1 else 0) * MMat s q) =
              MMat s0 q + MMat s1 q := by
            rw [← Finset.sum_subset (s₁ := {s0, s1}) (fun _ _ => Finset.mem_univ _)]
            · rw [Finset.sum_pair hs01]
              simp [s0, s1, payOf_mkSt, t1Of_mkSt]
            · intro s _ hs
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
              have hfalse : ¬ (payOf s = payOf p ∧ t1Of s = !isBob) := by
                intro ⟨hpay, ht1s⟩
                cases hts0 : t0Of s
                · apply hs.1; rw [← mkSt_eta s, hpay, hts0, ht1s]
                · apply hs.2; rw [← mkSt_eta s, hpay, hts0, ht1s]
              simp [hfalse]
          rw [hsum2, hM_eq s0 q, hM_eq s1 q]
          simp only [s0, s1, payOf_mkSt, t0Of_mkSt, t1Of_mkSt, ht0q, ht1q, hnotis,
            Bool.false_eq_true, false_and, and_false, not_false_eq_true, true_and, and_true,
            and_self, ↓reduceIte]
          split_ifs <;> rfl
        · simp only [ht1p', ht1q, hnotis, false_and, and_false, ↓reduceIte]
          apply Finset.sum_eq_zero
          intro s _
          rw [hM_eq s q]
          by_cases h1 : payOf s = payOf p ∧ t1Of s = !isBob
          · have h2 : ¬ (¬ (t0Of s = true ∧ t1Of s = isBob) ∧ payOf q = payOf s ∧
                t0Of q = false ∧ t1Of q = t1Of s) := by
              intro h2; rw [h2.2.2.2, h1.2] at ht1q; exact ht1q rfl
            simp only [h2, ↓reduceIte, mul_zero]
          · simp only [h1, ↓reduceIte, zero_mul]
    · simp only [ht0p, ht0q, and_false, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro s _
      rw [hM_eq s q]
      simp [ht0q]
  · simp [ht0p]

private def kLayersRow (d : Nat) (taps : Fin (d + 2) → ZMod 2) (isBob : Bool) (k : Nat)
    (W : (Fin d → Bool) → (Fin d → Bool) → Nat) (i : Nat) : Row :=
  let L := layerLen d
  let r := k - 1 - i / L
  layerRow d taps isBob (fun x y => (W x y).testBit r) (i % L)

private theorem kLayers_spec (d : Nat) (hd : 0 < d) (taps : Fin (d + 2) → ZMod 2)
    (hlin : ∀ u v : Fin (d + 2) → ZMod 2,
      (fun j : Fin (d + 2) => if h : j.val + 1 < d + 2 then (u + v) ⟨j.val + 1, h⟩ else ∑ i, taps i * (u + v) i) =
      (fun j : Fin (d + 2) => if h : j.val + 1 < d + 2 then u ⟨j.val + 1, h⟩ else ∑ i, taps i * u i) +
      (fun j : Fin (d + 2) => if h : j.val + 1 < d + 2 then v ⟨j.val + 1, h⟩ else ∑ i, taps i * v i))
    (hper : ∀ s : Fin (d + 2) → ZMod 2,
      (fun (s : Fin (d + 2) → ZMod 2) (j : Fin (d + 2)) =>
        if h : j.val + 1 < d + 2 then s ⟨j.val + 1, h⟩ else ∑ i, taps i * s i)^[2 ^ (d + 2) - 1] s = s)
    (hgen : ∀ v : Fin (d + 2) → ZMod 2, v ≠ 0 →
      ∃ t < 2 ^ (d + 2) - 1,
        (fun (s : Fin (d + 2) → ZMod 2) (j : Fin (d + 2)) =>
          if h : j.val + 1 < d + 2 then s ⟨j.val + 1, h⟩ else ∑ i, taps i * s i)^[t]
            (fun j => if j.val = d + 1 then 1 else 0) = v)
    (isBob : Bool) (k : Nat) (hk : 0 < k)
    (W : (Fin d → Bool) → (Fin d → Bool) → Nat)
    (hW : ∀ x y, W x y < 2 ^ k)
    (p q : Fin (d + 2) → Bool) :
    (List.ofFn (fun i : Fin (k * layerLen d) =>
      stepMat (d + 2) (kLayersRow d taps isBob k W i.val))).prod p q =
      if t0Of p = false ∧ t0Of q = false then
        if t1Of p = isBob ∧ t1Of q = isBob then (if payOf q = payOf p then 1 else 0)
        else if t1Of p = isBob ∧ t1Of q = !isBob then W (payOf p) (payOf q)
        else if t1Of p = !isBob ∧ t1Of q = !isBob then (if payOf q = payOf p then 2 ^ k else 0)
        else 0
      else 0 := by
  let w := d + 2
  let L := layerLen d
  have hLpos : 0 < L := by dsimp [L, layerLen]; omega
  have hgen_ind : ∀ m, 0 < m → ∀ (W' : (Fin d → Bool) → (Fin d → Bool) → Nat),
      (∀ x y, W' x y < 2 ^ m) →
      ∀ p q : Fin w → Bool,
        (List.ofFn (fun i : Fin (m * L) =>
          stepMat w (kLayersRow d taps isBob m W' i.val))).prod p q =
        if t0Of p = false ∧ t0Of q = false then
          if t1Of p = isBob ∧ t1Of q = isBob then (if payOf q = payOf p then 1 else 0)
          else if t1Of p = isBob ∧ t1Of q = !isBob then W' (payOf p) (payOf q)
          else if t1Of p = !isBob ∧ t1Of q = !isBob then (if payOf q = payOf p then 2 ^ m else 0)
          else 0
        else 0 := by
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    induction m' with
    | zero =>
      intro W' hW' p q
      have hlen : 1 * L = L := one_mul L
      have heq : (List.ofFn (fun i : Fin (1 * L) =>
            stepMat w (kLayersRow d taps isBob 1 W' i.val))).prod =
          (List.ofFn (fun i : Fin L =>
            stepMat w (layerRow d taps isBob (fun x y => (W' x y).testBit 0) i.val))).prod := by
        congr 1
        apply List.ext_getElem
        · simp [hlen]
        · intro i h1 h2
          simp only [List.getElem_ofFn, kLayersRow, Nat.sub_self, Nat.zero_sub]
          have hlt : i < L := by simp at h2; exact h2
          simp [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, L]
      rw [heq, layerMat_spec d hd taps hlin hper hgen isBob _ p q]
      simp only [Nat.zero_add, pow_one]
      have hbit0 : (if (W' (payOf p) (payOf q)).testBit 0 = true then 1 else 0) = W' (payOf p) (payOf q) := by
        have hlt := hW' (payOf p) (payOf q)
        have hlt2 : W' (payOf p) (payOf q) < 2 := by simpa using hlt
        interval_cases (W' (payOf p) (payOf q)) <;> decide
      rw [hbit0]
    | succ m' ih =>
      intro W' hW' p q
      let Wtop : (Fin d → Bool) → (Fin d → Bool) → Nat := fun x y => W' x y / 2
      have hWtop : ∀ x y, Wtop x y < 2 ^ (m' + 1) := by
        intro x y
        have h := hW' x y
        dsimp only [Wtop]
        rw [pow_succ] at h
        exact Nat.div_lt_of_lt_mul (by linarith)
      have hlen : (m' + 2) * L = (m' + 1) * L + L := by ring
      have heq : (List.ofFn (fun i : Fin ((m' + 2) * L) =>
            stepMat w (kLayersRow d taps isBob (m' + 2) W' i.val))).prod =
          (List.ofFn (fun i : Fin ((m' + 1) * L) =>
            stepMat w (kLayersRow d taps isBob (m' + 1) Wtop i.val))).prod *
          (List.ofFn (fun i : Fin L =>
            stepMat w (layerRow d taps isBob (fun x y => (W' x y).testBit 0) i.val))).prod := by
        have h1 : (List.ofFn (fun i : Fin ((m' + 2) * L) =>
              stepMat w (kLayersRow d taps isBob (m' + 2) W' i.val))).prod =
            (List.ofFn (fun i : Fin ((m' + 1) * L + L) =>
              stepMat w (kLayersRow d taps isBob (m' + 2) W' i.val))).prod := by
          congr 1
          apply List.ext_getElem
          · simp [hlen]
          · intro i h1 h2; simp
        rw [h1, list_ofFn_add_prod ((m' + 1) * L) L]
        congr 1
        · congr 2; funext i
          dsimp only [kLayersRow]
          have hdiv_lt : i.val / L < m' + 1 := (Nat.div_lt_iff_lt_mul hLpos).mpr i.isLt
          have hr_eq : m' + 2 - 1 - i.val / L = (m' + 1 - 1 - i.val / L) + 1 := by omega
          congr 2
          funext x y
          rw [hr_eq]
          dsimp only [Wtop]
          rw [Nat.testBit_succ]
        · congr 2; funext i
          dsimp only [kLayersRow]
          have hdiv : ((m' + 1) * L + i.val) / L = m' + 1 := by
            rw [mul_comm (m' + 1) L, Nat.mul_add_div hLpos, Nat.div_eq_of_lt i.isLt, add_zero]
          have hmod : ((m' + 1) * L + i.val) % L = i.val := by
            rw [mul_comm (m' + 1) L, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
          rw [hdiv, hmod]
          have h0 : m' + 2 - 1 - (m' + 1) = 0 := by omega
          rw [h0]
      rw [heq, Matrix.mul_apply]
      have hih := ih (by omega) Wtop hWtop
      have hlay := layerMat_spec d hd taps hlin hper hgen isBob (fun x y => (W' x y).testBit 0)
      have hstep_eq : ∀ s : Fin w → Bool,
          (List.ofFn (fun i : Fin ((m' + 1) * L) =>
            stepMat w (kLayersRow d taps isBob (m' + 1) Wtop i.val))).prod p s *
          (List.ofFn (fun i : Fin L =>
            stepMat w (layerRow d taps isBob (fun x y => (W' x y).testBit 0) i.val))).prod s q =
          (if t0Of p = false ∧ t0Of s = false then
            if t1Of p = isBob ∧ t1Of s = isBob then if payOf s = payOf p then 1 else 0
            else if t1Of p = isBob ∧ t1Of s = !isBob then Wtop (payOf p) (payOf s)
            else if t1Of p = !isBob ∧ t1Of s = !isBob then if payOf s = payOf p then 2 ^ (m' + 1) else 0
            else 0
          else 0) *
          (if t0Of s = false ∧ t0Of q = false then
            if t1Of s = isBob ∧ t1Of q = isBob then if payOf q = payOf s then 1 else 0
            else if t1Of s = isBob ∧ t1Of q = !isBob then if (W' (payOf s) (payOf q)).testBit 0 = true then 1 else 0
            else if t1Of s = !isBob ∧ t1Of q = !isBob then if payOf q = payOf s then 2 else 0
            else 0
          else 0) := by
        intro s
        rw [hih p s, hlay s q]
      simp_rw [hstep_eq]
      have hnotis : (!isBob) ≠ isBob := by cases isBob <;> decide
      have hnotis' : isBob ≠ (!isBob) := by cases isBob <;> decide
      have hbool_flip : ∀ b : Bool, b ≠ isBob → b = !isBob := by
        intro b hb; cases b <;> cases isBob <;> first | rfl | exact absurd rfl hb
      by_cases ht0p : t0Of p = false
      · by_cases ht0q : t0Of q = false
        · simp only [ht0p, ht0q, and_self, true_and, and_true, ↓reduceIte]
          by_cases ht1p : t1Of p = isBob
          · by_cases ht1q : t1Of q = isBob
            · simp only [ht1p, ht1q, and_self, true_and, and_true, ↓reduceIte]
              rw [Finset.sum_eq_single p]
              · simp only [ht0p, ht1p, and_self, true_and, and_true, ↓reduceIte, one_mul]
              · intro s _ hs
                by_cases hts0 : t0Of s = false
                · simp only [hts0, ↓reduceIte]
                  by_cases hts1 : t1Of s = isBob
                  · have hne : payOf s ≠ payOf p := by
                      intro hp; apply hs; rw [← mkSt_eta s, ← mkSt_eta p, hp, hts0, ht0p, hts1, ht1p]
                    simp only [hts1, hne, ↓reduceIte, zero_mul]
                  · have hts1' : t1Of s = !isBob := hbool_flip _ hts1
                    simp only [hts1, ↓reduceIte]
                    simp only [hts1', hnotis, hnotis', false_and, and_false, ↓reduceIte, mul_zero]
                · simp only [hts0, Bool.true_eq_false, ↓reduceIte, zero_mul]
              · intro h; exact absurd (Finset.mem_univ _) h
            · have ht1q' : t1Of q = !isBob := hbool_flip _ ht1q
              simp only [ht1p, ht1q, and_false, false_and, true_and, and_true, ↓reduceIte]
              simp only [ht1q', ↓reduceIte]
              have hpq : p ≠ q := by
                intro h; rw [h, ht1q'] at ht1p; cases isBob <;> cases ht1p
              rw [← Finset.sum_subset (s₁ := {p, q}) (fun _ _ => Finset.mem_univ _)]
              · rw [Finset.sum_pair hpq]
                simp only [ht0p, ht0q, ht1p, ht1q, and_false, false_and, true_and, and_true, ↓reduceIte]
                simp only [ht1q', hnotis, hnotis', and_false, false_and, ↓reduceIte, one_mul, mul_one]
                dsimp only [Wtop]
                have hbit : (if (W' (payOf p) (payOf q)).testBit 0 = true then 1 else 0) =
                    W' (payOf p) (payOf q) % 2 := by
                  rw [Nat.testBit_zero]
                  have := Nat.mod_lt (W' (payOf p) (payOf q)) (by omega : 0 < 2)
                  interval_cases (W' (payOf p) (payOf q) % 2) <;> decide
                rw [hbit]
                have hdiv := Nat.div_add_mod (W' (payOf p) (payOf q)) 2
                omega
              · intro s _ hs
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
                by_cases hts0 : t0Of s = false
                · simp only [hts0, ↓reduceIte]
                  by_cases hts1 : t1Of s = isBob
                  · have hne : payOf s ≠ payOf p := by
                      intro hp; apply hs.1; rw [← mkSt_eta s, ← mkSt_eta p, hp, hts0, ht0p, hts1, ht1p]
                    simp only [hts1, hne, ↓reduceIte, zero_mul]
                  · have hts1' : t1Of s = !isBob := hbool_flip _ hts1
                    have hne : payOf q ≠ payOf s := by
                      intro hq; apply hs.2; rw [← mkSt_eta s, ← mkSt_eta q, hq, hts0, ht0q, hts1', ht1q']
                    simp only [hts1, ↓reduceIte]
                    simp only [hts1', hne, hnotis, hnotis', and_self, false_and, and_false, ↓reduceIte, mul_zero]
                · simp only [hts0, Bool.true_eq_false, ↓reduceIte, zero_mul]
          · have ht1p' : t1Of p = !isBob := hbool_flip _ ht1p
            simp only [ht1p, false_and, ↓reduceIte]
            by_cases ht1q : t1Of q = !isBob
            · simp only [ht1p', ht1q, and_self, true_and, and_true, ↓reduceIte]
              rw [Finset.sum_eq_single p]
              · simp only [ht0p, ht0q, ht1p, false_and, ↓reduceIte]
                simp only [ht1p', ht1q, hnotis, false_and, and_self, ↓reduceIte, pow_succ]
                split_ifs with h <;> ring
              · intro s _ hs
                by_cases hts0 : t0Of s = false
                · simp only [hts0, ↓reduceIte]
                  by_cases hts1 : t1Of s = !isBob
                  · have hne : payOf s ≠ payOf p := by
                      intro hp; apply hs; rw [← mkSt_eta s, ← mkSt_eta p, hp, hts0, ht0p, hts1, ht1p']
                    simp only [hts1, hne, ht1p', hnotis, false_and, and_self, ↓reduceIte, zero_mul]
                  · simp only [hts1, ht1p', hnotis, false_and, and_false, ↓reduceIte, zero_mul]
                · simp only [hts0, Bool.true_eq_false, ↓reduceIte, zero_mul]
              · intro h; exact absurd (Finset.mem_univ _) h
            · simp only [ht1p', ht1q, false_and, and_false, ↓reduceIte]
              apply Finset.sum_eq_zero
              intro s _
              by_cases hts0 : t0Of s = false
              · simp only [hts0, ↓reduceIte]
                by_cases hts1 : t1Of s = !isBob
                · simp only [ht1p', ht1q, hts1, hnotis, true_and, and_true, false_and, and_false, ↓reduceIte, mul_zero]
                · simp only [ht1p', ht1q, hts1, hnotis, true_and, and_true, false_and, and_false, ↓reduceIte, zero_mul]
              · simp only [hts0, Bool.true_eq_false, ↓reduceIte, zero_mul]
        · simp only [ht0p, ht0q, Bool.true_eq_false, and_false, false_and, ↓reduceIte]
          apply Finset.sum_eq_zero
          intro s _
          simp only [ht0q, Bool.true_eq_false, and_false, ↓reduceIte, mul_zero]
      · simp only [ht0p, Bool.true_eq_false, false_and, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro s _
        simp only [ht0p, Bool.true_eq_false, false_and, ↓reduceIte, zero_mul]
  exact hgen_ind k hk W hW p q

private def padStream (d pad : Nat) (hd : 0 < d) (x : Fin d → Bool) (i : Nat) : Bool :=
  if h1 : i < d then x ⟨i, h1⟩
  else if i < d + 2 then false
  else if i < d + 2 + pad + d then x ⟨(i - (d + 2)) % d, Nat.mod_lt _ hd⟩
  else false

private def padState (d pad : Nat) (hd : 0 < d) (t : Nat) (x : Fin d → Bool) : Fin (d + 2) → Bool :=
  fun j => padStream d pad hd x (t + j.val)

private def rotPay (d pad : Nat) (hd : 0 < d) (x : Fin d → Bool) : Fin d → Bool :=
  fun j => x ⟨(pad + j.val) % d, Nat.mod_lt _ hd⟩

private def rotPayInv (d pad : Nat) (hd : 0 < d) (x : Fin d → Bool) : Fin d → Bool :=
  fun j => x ⟨(d - pad % d + j.val) % d, Nat.mod_lt _ hd⟩

private theorem rotPay_inv (d pad : Nat) (hd : 0 < d) (x : Fin d → Bool) :
    rotPay d pad hd (rotPayInv d pad hd x) = x := by
  funext j
  dsimp only [rotPay, rotPayInv]
  congr 1
  apply Fin.ext
  dsimp only
  have h1 : (d - pad % d + (pad + j.val) % d) % d = (d - pad % d + (pad + j.val)) % d := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1]
  have h2 : d - pad % d + (pad + j.val) = (pad / d + 1) * d + j.val := by
    have hdm := Nat.div_add_mod pad d
    have hlt := Nat.mod_lt pad hd
    have : (pad / d + 1) * d = d * (pad / d) + d := by ring
    omega
  rw [h2, mul_comm (pad / d + 1) d, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]

private theorem rotPayInv_rot (d pad : Nat) (hd : 0 < d) (x : Fin d → Bool) :
    rotPayInv d pad hd (rotPay d pad hd x) = x := by
  funext j
  dsimp only [rotPay, rotPayInv]
  congr 1
  apply Fin.ext
  dsimp only
  have h1 : (pad + (d - pad % d + j.val) % d) % d = (pad + (d - pad % d + j.val)) % d := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1]
  have h2 : pad + (d - pad % d + j.val) = (pad / d + 1) * d + j.val := by
    have hdm := Nat.div_add_mod pad d
    have hlt := Nat.mod_lt pad hd
    have : (pad / d + 1) * d = d * (pad / d) + d := by ring
    omega
  rw [h2, mul_comm (pad / d + 1) d, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]

private theorem padState_zero (d pad : Nat) (hd : 0 < d) (x : Fin d → Bool) :
    padState d pad hd 0 x = mkSt x false false := by
  funext j
  dsimp only [padState, padStream, mkSt]
  simp only [Nat.zero_add]
  by_cases h1 : j.val < d
  · simp [h1]
  · by_cases h2 : j.val = d
    · simp [h1, h2]
    · have hlt : j.val < d + 2 := j.isLt
      simp [h1, h2, hlt]

private theorem padState_end (d pad : Nat) (hd : 0 < d) (x : Fin d → Bool) :
    padState d pad hd (d + 2 + pad) x = mkSt (rotPay d pad hd x) false false := by
  funext j
  dsimp only [padState, padStream, mkSt, rotPay]
  have hn1 : ¬ (d + 2 + pad + j.val < d) := by omega
  have hn2 : ¬ (d + 2 + pad + j.val < d + 2) := by omega
  simp only [hn1, hn2, ↓reduceDIte, ↓reduceIte]
  by_cases h1 : j.val < d
  · have hlt : d + 2 + pad + j.val < d + 2 + pad + d := by omega
    simp only [h1, hlt, ↓reduceDIte, ↓reduceIte]
    congr 1
    apply Fin.ext
    dsimp only
    have hsub : d + 2 + pad + j.val - (d + 2) = pad + j.val := by omega
    rw [hsub]
  · have hn3 : ¬ (d + 2 + pad + j.val < d + 2 + pad + d) := by omega
    simp only [h1, hn3, ↓reduceDIte, ↓reduceIte]
    by_cases h2 : j.val = d <;> simp [h2]

private theorem padState_step (d pad : Nat) (hd : 0 < d) (t : Nat) (x : Fin d → Bool) :
    nextSt (padState d pad hd t x) (padStream d pad hd x (t + (d + 2))) =
      padState d pad hd (t + 1) x := by
  funext j
  dsimp only [nextSt, padState]
  split_ifs with hj
  · congr 1; omega
  · congr 1; omega

private theorem padState_inj (d pad : Nat) (hd : 0 < d) (t : Nat) (ht : t ≤ d + 2 + pad) :
    Function.Injective (padState d pad hd t) := by
  intro x1 x2 h
  funext j
  by_cases h1 : t ≤ j.val
  · have hk : j.val - t < d + 2 := by omega
    have hval := congrFun h ⟨j.val - t, hk⟩
    dsimp only [padState, padStream] at hval
    have hsum : t + (j.val - t) = j.val := by omega
    simp only [hsum, j.isLt, ↓reduceDIte] at hval
    exact hval
  · by_cases h2 : t ≤ d
    · have hk : d + 2 + j.val - t < d + 2 := by omega
      have hval := congrFun h ⟨d + 2 + j.val - t, hk⟩
      dsimp only [padState, padStream] at hval
      have hsum : t + (d + 2 + j.val - t) = d + 2 + j.val := by omega
      have hn1 : ¬ (d + 2 + j.val < d) := by omega
      have hn2 : ¬ (d + 2 + j.val < d + 2) := by omega
      have hlt : d + 2 + j.val < d + 2 + pad + d := by omega
      simp only [hsum, hn1, hn2, hlt, ↓reduceDIte, ↓reduceIte] at hval
      have hmod : (d + 2 + j.val - (d + 2)) % d = j.val := by
        have : d + 2 + j.val - (d + 2) = j.val := by omega
        rw [this, Nat.mod_eq_of_lt j.isLt]
      have hfin : (⟨(d + 2 + j.val - (d + 2)) % d, Nat.mod_lt _ hd⟩ : Fin d) = j := Fin.ext hmod
      rw [hfin] at hval
      exact hval
    · let base := max (d + 2) t
      have hbase_ge : d + 2 ≤ base := le_max_left _ _
      have hbase_t : t ≤ base := le_max_right _ _
      have hbase_upper : base + d ≤ t + (d + 2) := by
        dsimp only [base]
        omega
      have hbase_stream : base + d ≤ d + 2 + pad + d := by
        dsimp only [base]
        omega
      let r := (d + j.val - (base - (d + 2)) % d) % d
      have hr_lt : r < d := Nat.mod_lt _ hd
      have hk : base - t + r < d + 2 := by omega
      have hval := congrFun h ⟨base - t + r, hk⟩
      dsimp only [padState, padStream] at hval
      have hsum : t + (base - t + r) = base + r := by omega
      have hn1 : ¬ (base + r < d) := by omega
      have hn2 : ¬ (base + r < d + 2) := by omega
      have hlt : base + r < d + 2 + pad + d := by omega
      simp only [hsum, hn1, hn2, hlt, ↓reduceDIte, ↓reduceIte] at hval
      have hmod : (base + r - (d + 2)) % d = j.val := by
        have hsub : base + r - (d + 2) = (base - (d + 2)) + r := by omega
        have hr_mod : r % d = (d + j.val - (base - (d + 2)) % d) % d := Nat.mod_mod _ d
        have hadd : (base - (d + 2)) % d + (d + j.val - (base - (d + 2)) % d) = d + j.val := by
          have := Nat.mod_lt (base - (d + 2)) hd
          omega
        calc (base + r - (d + 2)) % d
            = ((base - (d + 2)) % d + r % d) % d := by rw [hsub, Nat.add_mod]
          _ = ((base - (d + 2)) % d + (d + j.val - (base - (d + 2)) % d) % d) % d := by rw [hr_mod]
          _ = ((base - (d + 2)) % d + (d + j.val - (base - (d + 2)) % d)) % d := by
              have hmod_add : ∀ a b : Nat, (a % d + b % d) % d = (a % d + b) % d := fun a b => by
                rw [Nat.add_mod (a % d) b, Nat.mod_mod]
              exact hmod_add _ _
          _ = (d + j.val) % d := by rw [hadd]
          _ = j.val := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt j.isLt]
      have hfin : (⟨(base + r - (d + 2)) % d, Nat.mod_lt _ hd⟩ : Fin d) = j := Fin.ext hmod
      rw [hfin] at hval
      exact hval

private def bobPadRow (d pad : Nat) (hd : 0 < d) (t : Nat) : Row :=
  rowOfTest (fun s b =>
    decide (∃ x : Fin d → Bool, s = padState d pad hd t x ∧ b = padStream d pad hd x (t + (d + 2))))

private theorem bobGuardPad_spec (d pad : Nat) (hd : 0 < d) (p q : Fin (d + 2) → Bool) :
    (List.ofFn (fun t : Fin (d + 2 + pad) =>
      stepMat (d + 2) (bobPadRow d pad hd t.val))).prod p q =
      if ∃ x : Fin d → Bool, p = mkSt x false false ∧ q = mkSt (rotPay d pad hd x) false false
      then 1 else 0 := by
  let w := d + 2
  have hstep1 : ∀ t < w + pad, ∀ r s : Fin w → Bool,
      stepMat w (bobPadRow d pad hd t) r s =
        if ∃ x : Fin d → Bool, r = padState d pad hd t x ∧ s = padState d pad hd (t + 1) x
        then 1 else 0 := by
    intro t ht r s
    dsimp only [bobPadRow]
    rw [stepMat_rowOfTest]
    simp only [Matrix.of_apply, decide_eq_true_eq]
    split_ifs with h
    · obtain ⟨x, rfl, rfl⟩ := h
      rw [Finset.card_eq_one]
      refine ⟨padStream d pad hd x (t + w), ?_⟩
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro ⟨⟨x', hx', hb⟩, _⟩
        have hxeq : x' = x := padState_inj d pad hd t (by omega) hx'.symm
        subst hxeq
        exact hb
      · intro hb
        subst hb
        exact ⟨⟨x, rfl, rfl⟩, padState_step d pad hd t x⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ ⟨⟨x, hx, hb⟩, hnxt⟩
      subst hx; subst hb
      apply h
      refine ⟨x, rfl, ?_⟩
      rw [← hnxt]
      exact padState_step d pad hd t x
  have hpart : ∀ m, 0 < m → m ≤ w + pad → ∀ s : Fin w → Bool,
      (List.ofFn (fun t : Fin m => stepMat w (bobPadRow d pad hd t.val))).prod p s =
        if ∃ x : Fin d → Bool, p = padState d pad hd 0 x ∧ s = padState d pad hd m x
        then 1 else 0 := by
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    induction m' with
    | zero =>
      intro hle s
      have h1 : (List.ofFn (fun t : Fin 1 => stepMat w (bobPadRow d pad hd t.val))).prod =
          stepMat w (bobPadRow d pad hd 0) := by simp
      rw [h1]
      exact hstep1 0 (by omega) p s
    | succ m' ih =>
      intro hle s
      rw [prefixProd_succ, Matrix.mul_apply]
      have hih := ih (by omega) (by omega)
      simp_rw [hih, hstep1 (m' + 1) (by omega)]
      by_cases hex : ∃ x : Fin d → Bool, p = padState d pad hd 0 x ∧ s = padState d pad hd (m' + 2) x
      · obtain ⟨x, rfl, rfl⟩ := hex
        have hex' : ∃ x' : Fin d → Bool, padState d pad hd 0 x = padState d pad hd 0 x' ∧
            padState d pad hd (m' + 2) x = padState d pad hd (m' + 2) x' := ⟨x, rfl, rfl⟩
        simp only [hex', ↓reduceIte]
        rw [Finset.sum_eq_single (padState d pad hd (m' + 1) x)]
        · have h1 : ∃ x', padState d pad hd 0 x = padState d pad hd 0 x' ∧
              padState d pad hd (m' + 1) x = padState d pad hd (m' + 1) x' := ⟨x, rfl, rfl⟩
          have h2 : ∃ x', padState d pad hd (m' + 1) x = padState d pad hd (m' + 1) x' ∧
              padState d pad hd (m' + 2) x = padState d pad hd (m' + 2) x' := ⟨x, rfl, rfl⟩
          simp only [h1, h2, ↓reduceIte, mul_one]
        · intro r _ hr
          have hfalse : ¬ (∃ x', padState d pad hd 0 x = padState d pad hd 0 x' ∧
              r = padState d pad hd (m' + 1) x') := by
            intro ⟨x', hx', hr'⟩
            have hxeq : x = x' := padState_inj d pad hd 0 (by omega) hx'
            subst hxeq
            exact hr hr'
          simp only [hfalse, ↓reduceIte, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp only [hex, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro r _
        by_cases h1 : ∃ x1 : Fin d → Bool, p = padState d pad hd 0 x1 ∧ r = padState d pad hd (m' + 1) x1
        · have h2 : ¬ (∃ x2 : Fin d → Bool, r = padState d pad hd (m' + 1) x2 ∧
              s = padState d pad hd (m' + 2) x2) := by
            intro ⟨x2, hr2, hs2⟩
            obtain ⟨x1, hx1, hr1⟩ := h1
            have hx12 : x1 = x2 := padState_inj d pad hd (m' + 1) (by omega) (hr1.symm.trans hr2)
            subst hx12
            exact hex ⟨x1, hx1, hs2⟩
          simp only [h1, h2, ↓reduceIte, mul_zero]
        · simp only [h1, ↓reduceIte, zero_mul]
  have hfin := hpart (w + pad) (by omega) (le_refl _) q
  rw [hfin]
  have heqv : (∃ x : Fin d → Bool, p = padState d pad hd 0 x ∧ q = padState d pad hd (w + pad) x) ↔
      (∃ x : Fin d → Bool, p = mkSt x false false ∧ q = mkSt (rotPay d pad hd x) false false) := by
    constructor
    · intro ⟨x, hp, hq⟩
      rw [padState_zero] at hp
      rw [padState_end] at hq
      exact ⟨x, hp, hq⟩
    · intro ⟨x, hp, hq⟩
      exact ⟨x, by rw [padState_zero]; exact hp, by rw [padState_end]; exact hq⟩
  by_cases h2 : ∃ x : Fin d → Bool, p = mkSt x false false ∧ q = mkSt (rotPay d pad hd x) false false
  · have h1 := heqv.mpr h2; simp only [h1, h2, ↓reduceIte]
  · have h1 : ¬ (∃ x : Fin d → Bool, p = padState d pad hd 0 x ∧ q = padState d pad hd (w + pad) x) :=
      fun h => h2 (heqv.mp h)
    simp only [h1, h2, ↓reduceIte]

private theorem exists_ip_gadget (d n k : Nat) (hd : 0 < d) (hk : 0 < k)
    (hn : 2 * (k * (2 * (d + 2) + (2 ^ (d + 2) - 1)) + (d + 2)) ≤ n) :
    let w := d + 2
    let M := 4 ^ d
    let Q := 2 ^ k
    let H := k * (2 * w + (2 ^ w - 1)) + w
    ∃ (aliceRows bobRows : (Fin M → Fin Q) → Nat → Row),
      ∀ (A B : Fin M → Fin Q),
        totalCount w n (fun site => if site < H then aliceRows A site else bobRows B (site - H)) =
          ∑ i : Fin M, (A i).val * (B i).val := by
  intro w M Q H
  obtain ⟨taps, hlin, hper, hgen⟩ := exists_primitive_lfsr w (by omega)
  have hcard_pair : Fintype.card ((Fin d → Bool) × (Fin d → Bool)) = M := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, M]
    rw [← mul_pow]
    norm_num
  let pairEquiv : ((Fin d → Bool) × (Fin d → Bool)) ≃ Fin M := Fintype.equivFinOfCardEq hcard_pair
  let pad := n - 2 * H
  have hHn : n = H + (H + pad) := by dsimp [pad, H, w] at hn ⊢; omega
  have hH_eq : H = k * layerLen d + w := by dsimp [H, layerLen, w]
  let aliceRows : (Fin M → Fin Q) → Nat → Row := fun A site =>
    if site < k * layerLen d then
      kLayersRow d taps false k (fun x y => (A (pairEquiv (x, y))).val) site
    else
      aliceGuardRow d (site - k * layerLen d)
  let bobRows : (Fin M → Fin Q) → Nat → Row := fun B site =>
    if site < k * layerLen d then
      kLayersRow d taps true k (fun y x => (B (pairEquiv (rotPay d pad hd x, y))).val) site
    else
      bobPadRow d pad hd (site - k * layerLen d)
  refine ⟨aliceRows, bobRows, ?_⟩
  intro A B
  let rows : Nat → Row := fun site => if site < H then aliceRows A site else bobRows B (site - H)
  have hn_pos : 0 < n := by
    have : 2 * (d + 2) ≤ 2 * (k * (2 * (d + 2) + (2 ^ (d + 2) - 1)) + (d + 2)) := by
      have : 0 ≤ k * (2 * (d + 2) + (2 ^ (d + 2) - 1)) := Nat.zero_le _
      omega
    omega
  rw [totalCount_eq_trace w n hn_pos rows]
  let MA_layers := (List.ofFn (fun i : Fin (k * layerLen d) =>
    stepMat w (kLayersRow d taps false k (fun x y => (A (pairEquiv (x, y))).val) i.val))).prod
  let MA_guard := (List.ofFn (fun i : Fin w => stepMat w (aliceGuardRow d i.val))).prod
  let MB_layers := (List.ofFn (fun i : Fin (k * layerLen d) =>
    stepMat w (kLayersRow d taps true k (fun y x => (B (pairEquiv (rotPay d pad hd x, y))).val) i.val))).prod
  let MB_guard := (List.ofFn (fun i : Fin (w + pad) => stepMat w (bobPadRow d pad hd i.val))).prod
  have hprod_split : (List.ofFn (fun i : Fin n => stepMat w (rows i.val))).prod =
      (MA_layers * MA_guard) * (MB_layers * MB_guard) := by
    have h1 : (List.ofFn (fun i : Fin n => stepMat w (rows i.val))).prod =
        (List.ofFn (fun i : Fin (H + (H + pad)) => stepMat w (rows i.val))).prod := by
      congr 1; exact List.ext_getElem (by simp [hHn]) (fun i h1 h2 => by simp)
    rw [h1, list_ofFn_add_prod H (H + pad)]
    congr 1
    · have h2 : (List.ofFn (fun i : Fin H => stepMat w (rows i.val))).prod =
          (List.ofFn (fun i : Fin (k * layerLen d + w) => stepMat w (rows i.val))).prod := rfl
      rw [h2, list_ofFn_add_prod (k * layerLen d) w]
      congr 1
      · congr 2; funext i
        have hlt1 : i.val < H := by omega
        simp [rows, aliceRows, hlt1, i.isLt]
      · congr 2; funext i
        have hlt1 : k * layerLen d + i.val < H := by omega
        have hnlt : ¬ (k * layerLen d + i.val < k * layerLen d) := by omega
        simp [rows, aliceRows, hlt1, hnlt]
    · have hHp : H + pad = k * layerLen d + (w + pad) := by omega
      have h2 : (List.ofFn (fun i : Fin (H + pad) => stepMat w (rows (H + i.val)))).prod =
          (List.ofFn (fun i : Fin (k * layerLen d + (w + pad)) => stepMat w (rows (H + i.val)))).prod := by
        congr 1; exact List.ext_getElem (by simp [hHp]) (fun i h1 h2 => by simp)
      rw [h2, list_ofFn_add_prod (k * layerLen d) (w + pad)]
      congr 1
      · congr 2; funext i
        have hnlt : ¬ (H + i.val < H) := by omega
        simp [rows, bobRows, hnlt, i.isLt]
      · congr 2; funext i
        have hnlt1 : ¬ (H + (k * layerLen d + i.val) < H) := by omega
        have hnlt2 : ¬ (k * layerLen d + i.val < k * layerLen d) := by omega
        simp [rows, bobRows, hnlt1, hnlt2]
  rw [hprod_split]
  have hMA_l : ∀ p q, MA_layers p q =
      if t0Of p = false ∧ t0Of q = false then
        if t1Of p = false ∧ t1Of q = false then if payOf q = payOf p then 1 else 0
        else if t1Of p = false ∧ t1Of q = !false then (A (pairEquiv (payOf p, payOf q))).val
        else if t1Of p = !false ∧ t1Of q = !false then if payOf q = payOf p then 2 ^ k else 0
        else 0
      else 0 := kLayers_spec d hd taps hlin hper hgen false k hk _ (fun x y => (A _).isLt)
  have hMA_g : ∀ p q, MA_guard p q =
      if q = p ∧ t0Of p = false ∧ t1Of p = true then 1 else 0 := aliceGuard_spec d
  have hMB_l : ∀ p q, MB_layers p q =
      if t0Of p = false ∧ t0Of q = false then
        if t1Of p = true ∧ t1Of q = true then if payOf q = payOf p then 1 else 0
        else if t1Of p = true ∧ t1Of q = !true then (B (pairEquiv (rotPay d pad hd (payOf q), payOf p))).val
        else if t1Of p = !true ∧ t1Of q = !true then if payOf q = payOf p then 2 ^ k else 0
        else 0
      else 0 := kLayers_spec d hd taps hlin hper hgen true k hk _ (fun y x => (B _).isLt)
  have hMB_g : ∀ p q, MB_guard p q =
      if ∃ x : Fin d → Bool, p = mkSt x false false ∧ q = mkSt (rotPay d pad hd x) false false
      then 1 else 0 := bobGuardPad_spec d pad hd
  have hMA : ∀ p q : Fin w → Bool, (MA_layers * MA_guard) p q =
      if t0Of p = false ∧ t0Of q = false ∧ t1Of q = true then
        if t1Of p = false then (A (pairEquiv (payOf p, payOf q))).val
        else if payOf q = payOf p then 2 ^ k else 0
      else 0 := by
    intro p q
    rw [Matrix.mul_apply, Finset.sum_eq_single q]
    · rw [hMA_l p q, hMA_g q q]
      by_cases ht0p : t0Of p = false <;> by_cases ht0q : t0Of q = false <;>
        by_cases ht1p : t1Of p = false <;> by_cases ht1q : t1Of q = true <;>
        simp [ht0p, ht0q, ht1p, ht1q]
    · intro s _ hs
      rw [hMA_g s q]
      have hne : q ≠ s := fun h => hs h.symm
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hMB : ∀ p q : Fin w → Bool, (MB_layers * MB_guard) p q =
      if t0Of p = false ∧ t0Of q = false ∧ t1Of q = false then
        if t1Of p = true then (B (pairEquiv (payOf q, payOf p))).val
        else if payOf q = rotPay d pad hd (payOf p) then 2 ^ k else 0
      else 0 := by
    intro p q
    rw [Matrix.mul_apply]
    by_cases ht0q : t0Of q = false
    · by_cases ht1q : t1Of q = false
      · let s0 : Fin w → Bool := mkSt (rotPayInv d pad hd (payOf q)) false false
        rw [Finset.sum_eq_single s0]
        · rw [hMB_l p s0, hMB_g s0 q]
          have hrot : rotPay d pad hd (rotPayInv d pad hd (payOf q)) = payOf q :=
            rotPay_inv d pad hd (payOf q)
          have hq_mk : q = mkSt (rotPay d pad hd (rotPayInv d pad hd (payOf q))) false false := by
            calc q = mkSt (payOf q) (t0Of q) (t1Of q) := (mkSt_eta q).symm
              _ = mkSt (rotPay d pad hd (rotPayInv d pad hd (payOf q))) false false := by
                rw [hrot, ht0q, ht1q]
          have hguard : ∃ x : Fin d → Bool, s0 = mkSt x false false ∧
              q = mkSt (rotPay d pad hd x) false false :=
            ⟨rotPayInv d pad hd (payOf q), rfl, hq_mk⟩
          simp only [hguard, ↓reduceIte, mul_one, s0, payOf_mkSt, t0Of_mkSt, t1Of_mkSt, hrot,
            ht0q, ht1q, and_self]
          by_cases ht0p : t0Of p = false
          · by_cases ht1p : t1Of p = true
            · simp [ht0p, ht1p]
            · have hpay_iff : rotPayInv d pad hd (payOf q) = payOf p ↔
                  payOf q = rotPay d pad hd (payOf p) := by
                constructor
                · intro h; rw [← h, rotPay_inv]
                · intro h; rw [h, rotPayInv_rot]
              simp [ht0p, ht1p, hpay_iff]
          · simp [ht0p]
        · intro s _ hs
          rw [hMB_g s q]
          have hnot : ¬ (∃ x : Fin d → Bool, s = mkSt x false false ∧
              q = mkSt (rotPay d pad hd x) false false) := by
            intro ⟨x, hsx, hqx⟩
            apply hs
            have hpayq : payOf q = rotPay d pad hd x := by
              simpa [payOf_mkSt] using congrArg payOf hqx
            have hx : x = rotPayInv d pad hd (payOf q) := by
              rw [hpayq, rotPayInv_rot]
            rw [hsx, hx]
          simp [hnot]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp only [ht0q, ht1q, Bool.true_eq_false, and_false, false_and, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro s _
        rw [hMB_g s q]
        have hnot : ¬ (∃ x : Fin d → Bool, s = mkSt x false false ∧
            q = mkSt (rotPay d pad hd x) false false) := by
          intro ⟨x, _, hqx⟩
          have := congrArg t1Of hqx
          rw [t1Of_mkSt] at this
          exact ht1q this
        simp [hnot]
    · simp only [ht0q, Bool.true_eq_false, false_and, and_false, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro s _
      rw [hMB_g s q]
      have hnot : ¬ (∃ x : Fin d → Bool, s = mkSt x false false ∧
          q = mkSt (rotPay d pad hd x) false false) := by
        intro ⟨x, _, hqx⟩
        have := congrArg t0Of hqx
        rw [t0Of_mkSt] at this
        exact ht0q this
      simp [hnot]
  dsimp only [Matrix.trace, Matrix.diag]
  have htr_eq : (∑ p : Fin w → Bool, ((MA_layers * MA_guard) * (MB_layers * MB_guard)) p p) =
      ∑ p : Fin w → Bool, ∑ q : Fin w → Bool,
        (if t0Of p = false ∧ t0Of q = false ∧ t1Of q = true then
          if t1Of p = false then (A (pairEquiv (payOf p, payOf q))).val
          else if payOf q = payOf p then 2 ^ k else 0
        else 0) *
        (if t0Of q = false ∧ t0Of p = false ∧ t1Of p = false then
          if t1Of q = true then (B (pairEquiv (payOf p, payOf q))).val
          else if payOf p = rotPay d pad hd (payOf q) then 2 ^ k else 0
        else 0) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro q _
    rw [hMA p q, hMB q p]
  rw [htr_eq]
  have htrace_simp : (∑ p : Fin w → Bool, ∑ q : Fin w → Bool,
        (if t0Of p = false ∧ t0Of q = false ∧ t1Of q = true then
          if t1Of p = false then (A (pairEquiv (payOf p, payOf q))).val
          else if payOf q = payOf p then 2 ^ k else 0
        else 0) *
        (if t0Of q = false ∧ t0Of p = false ∧ t1Of p = false then
          if t1Of q = true then (B (pairEquiv (payOf p, payOf q))).val
          else if payOf p = rotPay d pad hd (payOf q) then 2 ^ k else 0
        else 0)) =
      ∑ x : Fin d → Bool, ∑ y : Fin d → Bool,
        (A (pairEquiv (x, y))).val * (B (pairEquiv (x, y))).val := by
    have houter : ∀ p : Fin w → Bool,
        (∑ q : Fin w → Bool,
          (if t0Of p = false ∧ t0Of q = false ∧ t1Of q = true then
            if t1Of p = false then (A (pairEquiv (payOf p, payOf q))).val
            else if payOf q = payOf p then 2 ^ k else 0
          else 0) *
          (if t0Of q = false ∧ t0Of p = false ∧ t1Of p = false then
            if t1Of q = true then (B (pairEquiv (payOf p, payOf q))).val
            else if payOf p = rotPay d pad hd (payOf q) then 2 ^ k else 0
          else 0)) =
        if t0Of p = false ∧ t1Of p = false then
          ∑ y : Fin d → Bool, (A (pairEquiv (payOf p, y))).val * (B (pairEquiv (payOf p, y))).val
        else 0 := by
      intro p
      by_cases hp : t0Of p = false ∧ t1Of p = false
      · simp only [hp, and_self, ↓reduceIte, true_and]
        rw [← Finset.sum_subset (s₁ := (Finset.univ : Finset (Fin d → Bool)).image (fun y => mkSt y false true))
          (fun _ _ => Finset.mem_univ _)]
        · rw [Finset.sum_image]
          · apply Finset.sum_congr rfl
            intro y _
            simp [payOf_mkSt, t0Of_mkSt, t1Of_mkSt]
          · intro y1 _ y2 _ h
            simpa [payOf_mkSt] using congrArg payOf h
        · intro q _ hq
          simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hq
          have hnot : ¬ (t0Of q = false ∧ t1Of q = true) := by
            intro ⟨h1, h2⟩
            exact hq (payOf q) (by rw [← h1, ← h2, mkSt_eta])
          by_cases h1 : t0Of q = false <;> by_cases h2 : t1Of q = true <;> simp_all
      · simp only [hp, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro q _
        have hfalse : ¬ (t0Of q = false ∧ t0Of p = false ∧ t1Of p = false) := fun h => hp ⟨h.2.1, h.2.2⟩
        simp [hfalse]
    simp_rw [houter]
    rw [← Finset.sum_subset (s₁ := (Finset.univ : Finset (Fin d → Bool)).image (fun x => mkSt x false false))
      (fun _ _ => Finset.mem_univ _)]
    · rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro x _
        simp [payOf_mkSt, t0Of_mkSt, t1Of_mkSt]
      · intro x1 _ x2 _ h
        simpa [payOf_mkSt] using congrArg payOf h
    · intro p _ hp
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hp
      have hnot : ¬ (t0Of p = false ∧ t1Of p = false) := by
        intro ⟨h1, h2⟩
        exact hp (payOf p) (by
          calc mkSt (payOf p) false false = mkSt (payOf p) (t0Of p) (t1Of p) := by rw [h1, h2]
            _ = p := mkSt_eta p)
      simp [hnot]
  rw [htrace_simp, ← Fintype.sum_prod_type']
  exact Equiv.sum_comp pairEquiv (fun i => (A i).val * (B i).val)

private def afterBobAux {X : Type*} {S : Nat} (start : Fin S)
    (runAlice runBob : Nat → Fin S → X → Fin S) : Nat → X → X → Fin S
  | 0, _, _ => start
  | r + 1, A, B => runBob r (runAlice r (afterBobAux start runAlice runBob r A B) A) B

private theorem rectangle_partition {M q m S R a b p n H : Nat}
    (hq : 0 < q) (hp : 0 < p) (hR : 0 < R) (hHn : H ≤ n)
    (aliceRows bobRows : (Fin M → Fin q) → Nat → Row)
    (w : Nat)
    (hgadget : ∀ (A B : Fin M → Fin q),
      totalCount w n (fun site => if site < H then aliceRows A site else bobRows B (site - H)) =
        ∑ i : Fin M, (A i).val * (B i).val)
    (hsucc : succeedsProp w n p m S R a b) :
    0 < S ∧
    ∃ (T : Fin (S ^ (2 * p - 1)) → Finset (Fin M → Fin q) × Finset (Fin M → Fin q) × ((Fin M → Fin q) → Nat)),
      (∑ τ : Fin (S ^ (2 * p - 1)), (T τ).1.card * (T τ).2.1.card = q ^ (2 * M)) ∧
      (a * q ^ (2 * M) ≤ b * ∑ τ : Fin (S ^ (2 * p - 1)),
        (((T τ).1 ×ˢ (T τ).2.1).filter (fun AB =>
          (∑ i : Fin M, (AB.1 i).val * (AB.2 i).val) % m = (T τ).2.2 AB.2 % m)).card) := by
  obtain ⟨init, update, output, hok⟩ := hsucc
  have hS_pos : 0 < S := Fin.pos (init ⟨0, hR⟩)
  let X := Fin M → Fin q
  let glue : X → X → Nat → Row := fun A B site =>
    if site < H then aliceRows A site else bobRows B (site - H)
  let hit : Fin R → X × X → Bool := fun coin AB =>
    output coin (runAlg p n S (init coin) (update coin) (glue AB.1 AB.2)) ==
      (∑ i : Fin M, (AB.1 i).val * (AB.2 i).val) % m
  have hsum_all : a * R * Fintype.card (X × X) ≤
      b * ∑ coin : Fin R, ((Finset.univ : Finset (X × X)).filter (fun AB => hit coin AB = true)).card := by
    have h1 : ∀ AB : X × X,
        a * R ≤ b * ((Finset.univ : Finset (Fin R)).filter (fun coin => hit coin AB = true)).card := by
      intro AB
      have h := hok (glue AB.1 AB.2)
      rw [finRange_filter_length_eq_finset_card, hgadget AB.1 AB.2] at h
      exact h
    have h2 := Finset.sum_le_sum (s := (Finset.univ : Finset (X × X))) (fun AB _ => h1 AB)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm (Fintype.card (X × X)), ← Finset.mul_sum] at h2
    have hswap : (∑ AB : X × X, ((Finset.univ : Finset (Fin R)).filter (fun coin => hit coin AB = true)).card) =
        ∑ coin : Fin R, ((Finset.univ : Finset (X × X)).filter (fun AB => hit coin AB = true)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap] at h2
    exact h2
  have hex_coin : ∃ coin0 : Fin R,
      a * Fintype.card (X × X) ≤
        b * ((Finset.univ : Finset (X × X)).filter (fun AB => hit coin0 AB = true)).card := by
    by_contra hnone
    push_neg at hnone
    have hlt : b * ∑ coin : Fin R, ((Finset.univ : Finset (X × X)).filter (fun AB => hit coin AB = true)).card <
        ∑ _coin : Fin R, (a * Fintype.card (X × X)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_lt_sum_of_nonempty
        ⟨⟨0, hR⟩, Finset.mem_univ _⟩ (fun coin _ => hnone coin)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    have hmul : R * (a * Fintype.card (X × X)) = a * R * Fintype.card (X × X) := by ring
    omega
  obtain ⟨coin0, hcoin0⟩ := hex_coin
  have hcardXX : Fintype.card (X × X) = q ^ (2 * M) := by
    simp only [X, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    rw [← pow_add, two_mul]
  rw [hcardXX] at hcoin0
  let start := init coin0
  let step := update coin0
  let out := output coin0
  let runAlice : Nat → Fin S → X → Fin S := fun passId st A =>
    (List.range H).foldl (fun s i => step passId i s (aliceRows A i)) st
  let runBob : Nat → Fin S → X → Fin S := fun passId st B =>
    (List.range (n - H)).foldl (fun s j => step passId (H + j) s (bobRows B j)) st
  have honePass : ∀ passId st A B,
      (List.range n).foldl (fun s siteId => step passId siteId s (glue A B siteId)) st =
        runBob passId (runAlice passId st A) B := by
    intro passId st A B
    have hrange : List.range n = List.range H ++ (List.range (n - H)).map (H + ·) := by
      have h1 : n = H + (n - H) := by omega
      conv_lhs => rw [h1, List.range_add]
    rw [hrange, List.foldl_append, List.foldl_map]
    have hA : (List.range H).foldl (fun s siteId => step passId siteId s (glue A B siteId)) st =
        runAlice passId st A := by
      dsimp only [runAlice]
      have hgen : ∀ (L : List Nat) (st0 : Fin S), (∀ x ∈ L, x < H) →
          L.foldl (fun s siteId => step passId siteId s (glue A B siteId)) st0 =
          L.foldl (fun s siteId => step passId siteId s (aliceRows A siteId)) st0 := by
        intro L
        induction L with
        | nil => intro _ _; rfl
        | cons x xs ih =>
          intro st0 hL
          simp only [List.foldl_cons]
          have hx : x < H := hL x List.mem_cons_self
          have hgx : glue A B x = aliceRows A x := by simp [glue, hx]
          rw [hgx]
          exact ih _ (fun y hy => hL y (List.mem_cons_of_mem x hy))
      exact hgen (List.range H) st (fun x hx => List.mem_range.mp hx)
    rw [hA]
    dsimp only [runBob]
    have hB : ∀ (L : List Nat) (st0 : Fin S),
        L.foldl (fun s j => step passId (H + j) s (glue A B (H + j))) st0 =
        L.foldl (fun s j => step passId (H + j) s (bobRows B j)) st0 := by
      intro L
      induction L with
      | nil => intro _; rfl
      | cons x xs ih =>
        intro st0
        simp only [List.foldl_cons]
        have hgx : glue A B (H + x) = bobRows B x := by
          have : ¬ (H + x < H) := by omega
          simp [glue, this]
        rw [hgx]
        exact ih _
    exact hB (List.range (n - H)) _
  let afterBob : Nat → X → X → Fin S := afterBobAux start runAlice runBob
  have hrun_eq : ∀ r A B,
      (List.range r).foldl (fun prev passId =>
        (List.range n).foldl (fun state siteId => step passId siteId state (glue A B siteId)) prev) start =
      afterBob r A B := by
    intro r A B
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, honePass]
      rfl
  let Trans := (Fin (p - 1) → Fin S) × (Fin p → Fin S)
  have hcardTrans : Fintype.card Trans = S ^ (2 * p - 1) := by
    simp only [Trans, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    rw [← pow_add]
    congr 1
    omega
  let eT : Trans ≃ Fin (S ^ (2 * p - 1)) := Fintype.equivFinOfCardEq hcardTrans
  let trOf : X → X → Trans := fun A B =>
    (fun r : Fin (p - 1) => afterBob (r.val + 1) A B,
     fun r : Fin p => runAlice r.val (afterBob r.val A B) A)
  let Uset : Trans → Finset X := fun ts =>
    Finset.univ.filter (fun A =>
      ∀ r : Fin p,
        runAlice r.val (if h : r.val = 0 then start else ts.1 ⟨r.val - 1, by omega⟩) A = ts.2 r)
  let Vset : Trans → Finset X := fun ts =>
    Finset.univ.filter (fun B =>
      ∀ r : Fin (p - 1), runBob r.val (ts.2 ⟨r.val, by omega⟩) B = ts.1 r)
  let gFun : Trans → X → Nat := fun ts B => out (runBob (p - 1) (ts.2 ⟨p - 1, by omega⟩) B)
  have htr_iff : ∀ ts A B, trOf A B = ts ↔ A ∈ Uset ts ∧ B ∈ Vset ts := by
    intro ts A B
    constructor
    · intro h
      have h1 : ∀ r : Fin (p - 1), afterBob (r.val + 1) A B = ts.1 r := fun r => congrFun (congrArg Prod.fst h) r
      have h2 : ∀ r : Fin p, runAlice r.val (afterBob r.val A B) A = ts.2 r := fun r => congrFun (congrArg Prod.snd h) r
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      · intro r
        by_cases hr0 : r.val = 0
        · simp only [hr0, ↓reduceDIte]
          have := h2 r
          rw [hr0] at this
          exact this
        · simp only [hr0, ↓reduceDIte]
          have hsub : r.val - 1 + 1 = r.val := by omega
          have hprev := h1 ⟨r.val - 1, by omega⟩
          rw [← hprev, hsub]
          exact h2 r
      · intro r
        have hprev := h2 ⟨r.val, by omega⟩
        rw [← hprev]
        exact h1 r
    · intro ⟨hA, hB⟩
      have hA' := (Finset.mem_filter.mp hA).2
      have hB' := (Finset.mem_filter.mp hB).2
      have hrec : ∀ r, ∀ hr : r < p,
          afterBob r A B = (if h : r = 0 then start else ts.1 ⟨r - 1, by omega⟩) ∧
          runAlice r (afterBob r A B) A = ts.2 ⟨r, hr⟩ := by
        intro r
        induction r with
        | zero =>
          intro _
          refine ⟨by simp [afterBob, afterBobAux], ?_⟩
          have h := hA' ⟨0, hp⟩
          simpa [afterBob, afterBobAux] using h
        | succ r ih =>
          intro hr
          obtain ⟨_, ih2⟩ := ih (by omega)
          have hbob : afterBob (r + 1) A B = ts.1 ⟨r, by omega⟩ := by
            change runBob r (runAlice r (afterBob r A B) A) B = ts.1 ⟨r, by omega⟩
            rw [ih2]
            exact hB' ⟨r, by omega⟩
          refine ⟨by simp [hbob], ?_⟩
          have h := hA' ⟨r + 1, hr⟩
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel] at h
          rw [hbob]
          exact h
      apply Prod.ext
      · funext r
        obtain ⟨_, ih2⟩ := hrec r.val (by omega)
        change runBob r.val (runAlice r.val (afterBob r.val A B) A) B = ts.1 r
        rw [ih2]
        exact hB' r
      · funext r
        exact (hrec r.val r.isLt).2
  have hout_eq : ∀ ts A B, trOf A B = ts →
      out (runAlg p n S start step (glue A B)) = gFun ts B := by
    intro ts A B h
    dsimp only [runAlg, gFun]
    rw [hrun_eq p A B]
    have hp1 : p = (p - 1) + 1 := by omega
    conv_lhs => rw [hp1]
    change out (runBob (p - 1) (runAlice (p - 1) (afterBob (p - 1) A B) A) B) =
      out (runBob (p - 1) (ts.2 ⟨p - 1, by omega⟩) B)
    have h2 := congrFun (congrArg Prod.snd h) ⟨p - 1, by omega⟩
    dsimp only [trOf] at h2
    rw [h2]
  refine ⟨hS_pos, fun τ => (Uset (eT.symm τ), Vset (eT.symm τ), gFun (eT.symm τ)), ?_, ?_⟩
  · rw [Equiv.sum_comp eT.symm (fun ts => (Uset ts).card * (Vset ts).card)]
    have hpart := Finset.card_eq_sum_card_fiberwise
      (f := fun AB : X × X => trOf AB.1 AB.2)
      (s := (Finset.univ : Finset (X × X)))
      (t := (Finset.univ : Finset Trans))
      (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, hcardXX] at hpart
    rw [hpart]
    apply Finset.sum_congr rfl
    intro ts _
    rw [← Finset.card_product]
    congr 1
    ext ⟨A, B⟩
    simp [Finset.mem_product, htr_iff]
  · rw [Equiv.sum_comp eT.symm (fun ts =>
      (((Uset ts ×ˢ Vset ts).filter (fun AB =>
        (∑ i : Fin M, (AB.1 i).val * (AB.2 i).val) % m = gFun ts AB.2 % m)).card))]
    refine le_trans hcoin0 (Nat.mul_le_mul_left b ?_)
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun AB : X × X => trOf AB.1 AB.2)
      (s := (Finset.univ : Finset (X × X)).filter (fun AB => hit coin0 AB = true))
      (t := (Finset.univ : Finset Trans))
      (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    apply Finset.sum_le_sum
    intro ts _
    apply Finset.card_le_card
    intro ⟨A, B⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hit, beq_iff_eq] at hmem
    obtain ⟨h1, h2⟩ := hmem
    have hrect := (htr_iff ts A B).mp h2
    have ho := hout_eq ts A B h2
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨hrect, ?_⟩
    have heq : gFun ts B = (∑ i : Fin M, (A i).val * (B i).val) % m := by
      rw [← ho]
      exact h1
    rw [heq, Nat.mod_mod]

private noncomputable def om (m c : Nat) (x : ℤ) : ℂ :=
  Complex.exp (↑(2 * Real.pi * ((c : ℝ) * (x : ℝ)) / (m : ℝ)) * Complex.I)

private theorem norm_om (m c : Nat) (x : ℤ) : ‖om m c x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem om_add (m c : Nat) (x y : ℤ) : om m c (x + y) = om m c x * om m c y := by
  dsimp only [om]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem om_sub (m c : Nat) (x y : ℤ) : om m c (x - y) = om m c x * om m c (-y) := by
  rw [sub_eq_add_neg, om_add]

private theorem om_conj (m c : Nat) (x : ℤ) : starRingEnd ℂ (om m c x) = om m c (-x) := by
  dsimp only [om]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem om_pow (m c a : Nat) (y : ℤ) : (om m c y) ^ a = om m c ((a : ℤ) * y) := by
  dsimp only [om]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem om_eq_one_iff (m c : Nat) (hm : 0 < m) (x : ℤ) :
    om m c x = 1 ↔ (m : ℤ) ∣ (c : ℤ) * x := by
  dsimp only [om]
  rw [Complex.exp_eq_one_iff]
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by
    intro h
    have : 2 * Real.pi = 0 := Complex.ofReal_eq_zero.mp (by simpa using h)
    linarith [Real.pi_pos]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  constructor
  · intro ⟨n, hn⟩
    have hmul : (↑(2 * Real.pi * ((c : ℝ) * (x : ℝ)) / (m : ℝ)) : ℂ) = ↑(n : ℝ) * (2 * Real.pi) := by
      have h1 : (↑(2 * Real.pi * ((c : ℝ) * (x : ℝ)) / (m : ℝ)) : ℂ) * Complex.I =
          (↑(n : ℝ) * (2 * Real.pi)) * Complex.I := by
        simpa [mul_assoc] using hn
      exact mul_right_cancel₀ hI h1
    have hreal : 2 * Real.pi * ((c : ℝ) * (x : ℝ)) / (m : ℝ) = (n : ℝ) * (2 * Real.pi) :=
      Complex.ofReal_injective (by simpa using hmul)
    have h2piR : (2 * Real.pi : ℝ) ≠ 0 := by linarith [Real.pi_pos]
    have hcx : ((c : ℝ) * (x : ℝ)) = (n : ℝ) * (m : ℝ) := by
      field_simp [hmR] at hreal
      nlinarith [Real.pi_pos]
    have hint : (c : ℤ) * x = n * (m : ℤ) := by
      exact_mod_cast hcx
    exact ⟨n, by linarith⟩
  · intro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hcx : ((c : ℝ) * (x : ℝ)) = (m : ℝ) * (n : ℝ) := by
      exact_mod_cast hn
    rw [hcx]
    have hdiv : 2 * Real.pi * ((m : ℝ) * (n : ℝ)) / (m : ℝ) = (n : ℝ) * (2 * Real.pi) := by
      field_simp [hmR]
    rw [hdiv]
    push_cast
    ring

private theorem sum_om_geom (m c : Nat) (hm : 0 < m) (y : ℤ) :
    (∑ a : Fin m, om m c ((a.val : ℤ) * y)) =
      if (m : ℤ) ∣ (c : ℤ) * y then (m : ℂ) else 0 := by
  have hsum : (∑ a : Fin m, om m c ((a.val : ℤ) * y)) = ∑ a ∈ Finset.range m, (om m c y) ^ a := by
    rw [← Fin.sum_univ_eq_sum_range (fun a => (om m c y) ^ a)]
    apply Finset.sum_congr rfl
    intro a _
    exact (om_pow m c a.val y).symm
  rw [hsum]
  by_cases hdvd : (m : ℤ) ∣ (c : ℤ) * y
  · have hone : om m c y = 1 := (om_eq_one_iff m c hm y).mpr hdvd
    simp [hdvd, hone]
  · have hne : om m c y ≠ 1 := fun h => hdvd ((om_eq_one_iff m c hm y).mp h)
    rw [geom_sum_eq hne m]
    have hpow1 : (om m c y) ^ m = 1 := by
      rw [om_pow, om_eq_one_iff m c hm]
      exact ⟨(c : ℤ) * y, by ring⟩
    simp [hdvd, hpow1]

private theorem sum_om_indicator (m x y : Nat) (hm : 0 < m) :
    (∑ c : Fin m, om m c.val ((x : ℤ) - (y : ℤ))) =
      if x % m = y % m then (m : ℂ) else 0 := by
  have h1 : ∀ c : Fin m, om m c.val ((x : ℤ) - (y : ℤ)) = om m 1 ((c.val : ℤ) * ((x : ℤ) - (y : ℤ))) := by
    intro c
    dsimp only [om]
    congr 2
    push_cast
    ring
  simp_rw [h1]
  rw [sum_om_geom m 1 hm ((x : ℤ) - (y : ℤ))]
  simp only [Nat.cast_one, one_mul]
  have hdvd : ((m : ℤ) ∣ (x : ℤ) - (y : ℤ)) ↔ x % m = y % m := by
    rw [Int.dvd_iff_emod_eq_zero]
    have h1' : ((x : ℤ) - (y : ℤ)) % (m : ℤ) = 0 ↔ (x : ℤ) % (m : ℤ) = (y : ℤ) % (m : ℤ) := by
      constructor
      · intro h
        exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr h
      · intro h
        exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h
    rw [h1']
    exact_mod_cast Iff.rfl
  exact ite_eq_of_iff hdvd (m : ℂ) 0

private noncomputable def charSum {M m : Nat} (c : Nat)
    (U V : Finset (Fin M → Fin m)) (g : (Fin M → Fin m) → Nat) : ℂ :=
  ∑ A ∈ U, ∑ B ∈ V, om m c ((∑ i : Fin M, (A i).val * (B i).val : Nat) - (g B : ℤ))

private theorem card_congr_le {m d : Nat} (hm : 0 < m) (hd : d ∣ m) (r : Nat) :
    ((Finset.univ : Finset (Fin m)).filter (fun b : Fin m => ((m / d : Nat) : ℤ) ∣ (r : ℤ) - (b.val : ℤ))).card ≤ d := by
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd hm
  let q := m / d
  have hqd : q * d = m := Nat.div_mul_cancel hd
  have hq_pos : 0 < q := by
    by_contra h0
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h0
    rw [hq0, zero_mul] at hqd
    omega
  have hsub : ((Finset.univ : Finset (Fin m)).filter
      (fun b : Fin m => (q : ℤ) ∣ (r : ℤ) - (b.val : ℤ))) ⊆
      (Finset.univ : Finset (Fin d)).image (fun k : Fin d =>
        ⟨r % q + k.val * q, by
          have hr : r % q < q := Nat.mod_lt r hq_pos
          have hk : k.val + 1 ≤ d := k.isLt
          calc r % q + k.val * q < q + k.val * q := by omega
            _ = (k.val + 1) * q := by ring
            _ ≤ d * q := Nat.mul_le_mul_right q hk
            _ = m := by rw [mul_comm]; exact hqd⟩) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hmod : b.val % q = r % q := by
      have h1 : (r : ℤ) % (q : ℤ) = (b.val : ℤ) % (q : ℤ) :=
        Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp hb)
      exact_mod_cast h1.symm
    have hdiv_lt : b.val / q < d := by
      have hlt : b.val < q * d := by rw [hqd]; exact b.isLt
      exact (Nat.div_lt_iff_lt_mul hq_pos).mpr (by rw [mul_comm]; exact hlt)
    refine Finset.mem_image.mpr ⟨⟨b.val / q, hdiv_lt⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    have hdm := Nat.div_add_mod b.val q
    rw [hmod] at hdm
    linarith
  calc ((Finset.univ : Finset (Fin m)).filter _).card
      ≤ ((Finset.univ : Finset (Fin d)).image _).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_image_le
    _ = d := by simp

private theorem norm_charSum_sq_le {M m : Nat} (hm : 0 < m) (c : Nat)
    (U V : Finset (Fin M → Fin m)) (g : (Fin M → Fin m) → Nat) :
    ‖charSum c U V g‖ ^ 2 ≤
      (U.card : ℝ) * (V.card : ℝ) * (m : ℝ) ^ M * ((Nat.gcd c m : Nat) : ℝ) ^ M := by
  let X := Fin M → Fin m
  let inner : X → ℂ := fun A =>
    ∑ B ∈ V, om m c ((∑ i : Fin M, (A i).val * (B i).val : Nat) - (g B : ℤ))
  have h1 : ‖charSum c U V g‖ ≤ ∑ A ∈ U, ‖inner A‖ := norm_sum_le U inner
  have h2 : ‖charSum c U V g‖ ^ 2 ≤ (∑ A ∈ U, 1 * ‖inner A‖) ^ 2 := by
    have hnn : 0 ≤ ‖charSum c U V g‖ := norm_nonneg _
    have h1' : ‖charSum c U V g‖ ≤ ∑ A ∈ U, 1 * ‖inner A‖ := by simpa using h1
    nlinarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) (fun A => ‖inner A‖)
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsub_all : ∑ A ∈ U, ‖inner A‖ ^ 2 ≤ ∑ A : X, ‖inner A‖ ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg (fun A => sq_nonneg _)
  have hexpand : (∑ A : X, ‖inner A‖ ^ 2) =
      (∑ B1 ∈ V, ∑ B2 ∈ V,
        om m c ((g B2 : ℤ) - (g B1 : ℤ)) *
          ∏ i : Fin M, ∑ a : Fin m, om m c ((a.val : ℤ) * ((B1 i).val - (B2 i).val))).re := by
    have hnorm_sq : ∀ A : X, (‖inner A‖ ^ 2 : ℝ) = (inner A * starRingEnd ℂ (inner A)).re := by
      intro A
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    simp_rw [hnorm_sq]
    rw [← Complex.re_sum]
    congr 1
    have hprod_inner : ∀ A : X, inner A * starRingEnd ℂ (inner A) =
        ∑ B1 ∈ V, ∑ B2 ∈ V,
          om m c ((g B2 : ℤ) - (g B1 : ℤ)) *
            ∏ i : Fin M, om m c (((A i).val : ℤ) * ((B1 i).val - (B2 i).val)) := by
      intro A
      dsimp only [inner]
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro B1 _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B2 _
      rw [om_conj, ← om_add]
      have hprod_om : (∏ i : Fin M, om m c (((A i).val : ℤ) * ((B1 i).val - (B2 i).val))) =
          om m c (∑ i : Fin M, ((A i).val : ℤ) * ((B1 i).val - (B2 i).val)) := by
        have hgen : ∀ (s : Finset (Fin M)) (f : Fin M → ℤ),
            (∏ i ∈ s, om m c (f i)) = om m c (∑ i ∈ s, f i) := by
          intro s f
          induction s using Finset.induction_on with
          | empty => simp [om]
          | insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, om_add]
        exact hgen Finset.univ _
      rw [hprod_om, ← om_add]
      congr 1
      push_cast
      have hsum_sub : (∑ i : Fin M, ((A i).val : ℤ) * ((B1 i).val - (B2 i).val)) =
          (∑ i : Fin M, ((A i).val : ℤ) * (B1 i).val) - (∑ i : Fin M, ((A i).val : ℤ) * (B2 i).val) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum_sub]
      ring
    simp_rw [hprod_inner]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B1 _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B2 _
    rw [← Finset.mul_sum]
    congr 1
    rw [Fintype.prod_sum]
  let d := Nat.gcd c m
  have hd_dvd : d ∣ m := Nat.gcd_dvd_right c m
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hm
  have hq_eq : ∀ (y : ℤ), ((m : ℤ) ∣ (c : ℤ) * y) ↔ ((m / d : Nat) : ℤ) ∣ y := by
    intro y
    let c' := c / d
    let q := m / d
    have hc_eq : c = d * c' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left c m)).symm
    have hm_eq : m = d * q := (Nat.mul_div_cancel' hd_dvd).symm
    have hcop : Nat.Coprime c' q := Nat.coprime_div_gcd_div_gcd hd_pos
    have hcopZ : IsCoprime (c' : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
    constructor
    · intro ⟨k, hk⟩
      have h1 : (d : ℤ) * (c' : ℤ) * y = (d : ℤ) * (q : ℤ) * k := by
        have hcc : (c : ℤ) = (d : ℤ) * (c' : ℤ) := by exact_mod_cast hc_eq
        have hmm : (m : ℤ) = (d : ℤ) * (q : ℤ) := by exact_mod_cast hm_eq
        rw [hcc, hmm] at hk
        exact hk
      have hdZ : (d : ℤ) ≠ 0 := by omega
      have h2 : (c' : ℤ) * y = (q : ℤ) * k := mul_left_cancel₀ hdZ (by linarith)
      have hdvd_cy : (q : ℤ) ∣ (c' : ℤ) * y := ⟨k, h2⟩
      exact hcopZ.symm.dvd_of_dvd_mul_left hdvd_cy
    · intro ⟨k, hk⟩
      refine ⟨(c' : ℤ) * k, ?_⟩
      have hcc : (c : ℤ) = (d : ℤ) * (c' : ℤ) := by exact_mod_cast hc_eq
      have hmm : (m : ℤ) = (d : ℤ) * (q : ℤ) := by exact_mod_cast hm_eq
      rw [hcc, hmm, hk]
      ring
  have hinner_bound : ∑ A : X, ‖inner A‖ ^ 2 ≤ (V.card : ℝ) * (m : ℝ) ^ M * (d : ℝ) ^ M := by
    rw [hexpand]
    calc (∑ B1 ∈ V, ∑ B2 ∈ V,
            om m c ((g B2 : ℤ) - (g B1 : ℤ)) *
              ∏ i : Fin M, ∑ a : Fin m, om m c ((a.val : ℤ) * ((B1 i).val - (B2 i).val))).re
        ≤ ‖∑ B1 ∈ V, ∑ B2 ∈ V,
            om m c ((g B2 : ℤ) - (g B1 : ℤ)) *
              ∏ i : Fin M, ∑ a : Fin m, om m c ((a.val : ℤ) * ((B1 i).val - (B2 i).val))‖ :=
          Complex.re_le_norm _
      _ ≤ ∑ B1 ∈ V, ∑ B2 ∈ V,
            ‖om m c ((g B2 : ℤ) - (g B1 : ℤ)) *
              ∏ i : Fin M, ∑ a : Fin m, om m c ((a.val : ℤ) * ((B1 i).val - (B2 i).val))‖ := by
          refine le_trans (norm_sum_le _ _) ?_
          apply Finset.sum_le_sum
          intro B1 _
          exact norm_sum_le _ _
      _ = ∑ B1 ∈ V, ∑ B2 ∈ V,
            if (∀ i : Fin M, ((m / d : Nat) : ℤ) ∣ ((B1 i).val : ℤ) - ((B2 i).val : ℤ))
            then (m : ℝ) ^ M else 0 := by
          apply Finset.sum_congr rfl
          intro B1 _
          apply Finset.sum_congr rfl
          intro B2 _
          rw [norm_mul, norm_om, one_mul]
          have hprod_eval : (∏ i : Fin M, ∑ a : Fin m, om m c ((a.val : ℤ) * ((B1 i).val - (B2 i).val))) =
              if (∀ i : Fin M, ((m / d : Nat) : ℤ) ∣ ((B1 i).val : ℤ) - ((B2 i).val : ℤ))
              then ((m : ℂ) ^ M) else 0 := by
            simp_rw [sum_om_geom m c hm, hq_eq]
            by_cases hall : ∀ i : Fin M, ((m / d : Nat) : ℤ) ∣ ((B1 i).val : ℤ) - ((B2 i).val : ℤ)
            · simp only [hall, implies_true, ↓reduceIte, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            · simp only [hall, ↓reduceIte]
              push Not at hall
              obtain ⟨i0, hi0⟩ := hall
              exact Finset.prod_eq_zero (Finset.mem_univ i0) (by simp only [hi0, ↓reduceIte])
          rw [hprod_eval]
          split_ifs
          · rw [norm_pow, Complex.norm_natCast]
          · simp
      _ ≤ ∑ B1 ∈ V, (d : ℝ) ^ M * (m : ℝ) ^ M := by
          apply Finset.sum_le_sum
          intro B1 _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hcard_le : (V.filter (fun B2 =>
              ∀ i : Fin M, ((m / d : Nat) : ℤ) ∣ ((B1 i).val : ℤ) - ((B2 i).val : ℤ))).card ≤ d ^ M := by
            let PiSet : Finset (Fin M → Fin m) :=
              Fintype.piFinset (fun i : Fin M =>
                (Finset.univ : Finset (Fin m)).filter (fun b : Fin m =>
                  ((m / d : Nat) : ℤ) ∣ ((B1 i).val : ℤ) - (b.val : ℤ)))
            have hsub : V.filter (fun B2 =>
                ∀ i : Fin M, ((m / d : Nat) : ℤ) ∣ ((B1 i).val : ℤ) - ((B2 i).val : ℤ)) ⊆ PiSet := by
              intro B2 hB2
              simp only [Finset.mem_filter] at hB2
              simp only [PiSet, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hB2.2
            calc (V.filter _).card ≤ PiSet.card := Finset.card_le_card hsub
              _ = ∏ i : Fin M, ((Finset.univ : Finset (Fin m)).filter (fun b : Fin m =>
                    ((m / d : Nat) : ℤ) ∣ ((B1 i).val : ℤ) - (b.val : ℤ))).card :=
                  Fintype.card_piFinset _
              _ ≤ ∏ _i : Fin M, d := Finset.prod_le_prod'
                    (fun i _ => card_congr_le hm hd_dvd (B1 i).val)
              _ = d ^ M := by simp
          exact_mod_cast hcard_le
      _ = (V.card : ℝ) * (m : ℝ) ^ M * (d : ℝ) ^ M := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  calc ‖charSum c U V g‖ ^ 2
      ≤ (∑ A ∈ U, 1 * ‖inner A‖) ^ 2 := h2
    _ ≤ (U.card : ℝ) * ∑ A ∈ U, ‖inner A‖ ^ 2 := hcs
    _ ≤ (U.card : ℝ) * ∑ A : X, ‖inner A‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsub_all (Nat.cast_nonneg _)
    _ ≤ (U.card : ℝ) * ((V.card : ℝ) * (m : ℝ) ^ M * (d : ℝ) ^ M) :=
        mul_le_mul_of_nonneg_left hinner_bound (Nat.cast_nonneg _)
    _ = (U.card : ℝ) * (V.card : ℝ) * (m : ℝ) ^ M * (d : ℝ) ^ M := by ring

private theorem norm_charSum_le_half {H m : Nat} (hm : 0 < m) (c : Nat)
    (U V : Finset (Fin (2 * H) → Fin m)) (g : (Fin (2 * H) → Fin m) → Nat) :
    ‖charSum c U V g‖ ≤
      Real.sqrt ((U.card : ℝ) * (V.card : ℝ)) * ((m : ℝ) * (Nat.gcd c m : ℝ)) ^ H := by
  have hsq := norm_charSum_sq_le hm c U V g
  have hpow : (m : ℝ) ^ (2 * H) * ((Nat.gcd c m : Nat) : ℝ) ^ (2 * H) =
      (((m : ℝ) * (Nat.gcd c m : ℝ)) ^ H) ^ 2 := by
    rw [← mul_pow, ← pow_mul, mul_comm H 2]
  have hsq2 : ‖charSum c U V g‖ ^ 2 ≤
      (Real.sqrt ((U.card : ℝ) * (V.card : ℝ)) * ((m : ℝ) * (Nat.gcd c m : ℝ)) ^ H) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← hpow]
    linarith
  have hnn : 0 ≤ Real.sqrt ((U.card : ℝ) * (V.card : ℝ)) * ((m : ℝ) * (Nat.gcd c m : ℝ)) ^ H := by
    positivity
  nlinarith [norm_nonneg (charSum c U V g)]

private theorem rect_hits_eq_sum_charSum {M m : Nat} (hm : 0 < m)
    (U V : Finset (Fin M → Fin m)) (g : (Fin M → Fin m) → Nat) :
    ((m : ℝ) * (((U ×ˢ V).filter (fun AB =>
      (∑ i : Fin M, (AB.1 i).val * (AB.2 i).val) % m = g AB.2 % m)).card : ℝ)) =
    (∑ c : Fin m, charSum c.val U V g).re := by
  have h1 : (∑ c : Fin m, charSum c.val U V g) =
      ∑ A ∈ U, ∑ B ∈ V,
        if (∑ i : Fin M, (A i).val * (B i).val) % m = g B % m then (m : ℂ) else 0 := by
    dsimp only [charSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro A _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B _
    exact sum_om_indicator m (∑ i : Fin M, (A i).val * (B i).val) (g B) hm
  rw [h1, ← Finset.sum_product']
  have h2 : (∑ AB ∈ U ×ˢ V,
      if (∑ i : Fin M, (AB.1 i).val * (AB.2 i).val) % m = g AB.2 % m then (m : ℂ) else 0) =
      (((U ×ˢ V).filter (fun AB =>
        (∑ i : Fin M, (AB.1 i).val * (AB.2 i).val) % m = g AB.2 % m)).card : ℂ) * (m : ℂ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [h2]
  simp [mul_comm]

private theorem sum_sqrt_le {K N : Nat} (a b : Fin K → Nat)
    (hsum : ∑ τ : Fin K, a τ * b τ = N ^ 2) :
    ∑ τ : Fin K, Real.sqrt ((a τ : ℝ) * (b τ : ℝ)) ≤ Real.sqrt (K : ℝ) * (N : ℝ) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin K))
    (fun _ => (1 : ℝ)) (fun τ => Real.sqrt ((a τ : ℝ) * (b τ : ℝ)))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  have hsq_sum : (∑ τ : Fin K, Real.sqrt ((a τ : ℝ) * (b τ : ℝ)) ^ 2) = (N : ℝ) ^ 2 := by
    have h1 : ∀ τ : Fin K, Real.sqrt ((a τ : ℝ) * (b τ : ℝ)) ^ 2 = ((a τ * b τ : Nat) : ℝ) := by
      intro τ
      rw [Real.sq_sqrt (by positivity)]
      push_cast
      rfl
    simp_rw [h1, ← Nat.cast_sum, hsum]
    push_cast
    rfl
  rw [hsq_sum] at hcs
  have htarget : (Real.sqrt (K : ℝ) * (N : ℝ)) ^ 2 = (K : ℝ) * (N : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg K)]
  have hnn1 : 0 ≤ ∑ τ : Fin K, Real.sqrt ((a τ : ℝ) * (b τ : ℝ)) :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hnn2 : 0 ≤ Real.sqrt (K : ℝ) * (N : ℝ) := by positivity
  nlinarith

private theorem prime_lower_bound {H prime K : Nat} (hprime : Nat.Prime prime) (hK : 0 < K)
    (T : Fin K → Finset (Fin (2 * H) → Fin prime) × Finset (Fin (2 * H) → Fin prime) × ((Fin (2 * H) → Fin prime) → Nat))
    (hpart : ∑ τ : Fin K, (T τ).1.card * (T τ).2.1.card = prime ^ (2 * (2 * H)))
    (hadv : 2 * prime ^ (2 * (2 * H)) ≤ prime * ∑ τ : Fin K,
      (((T τ).1 ×ˢ (T τ).2.1).filter (fun AB =>
        (∑ i : Fin (2 * H), (AB.1 i).val * (AB.2 i).val) % prime = (T τ).2.2 AB.2 % prime)).card) :
    prime ^ (2 * H) ≤ (prime - 1) ^ 2 * K := by
  have hp_pos : 0 < prime := hprime.pos
  have hrect_ub : ∀ τ : Fin K,
      (prime : ℝ) * ((((T τ).1 ×ˢ (T τ).2.1).filter (fun AB =>
        (∑ i : Fin (2 * H), (AB.1 i).val * (AB.2 i).val) % prime = (T τ).2.2 AB.2 % prime)).card : ℝ) ≤
      ((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ) +
        ((prime - 1 : Nat) : ℝ) * (prime : ℝ) ^ H * Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) := by
    intro τ
    rw [rect_hits_eq_sum_charSum hp_pos]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hp_pos⟩ : Fin prime))]
    rw [Complex.add_re]
    have hc0 : (charSum 0 (T τ).1 (T τ).2.1 (T τ).2.2).re =
        ((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ) := by
      dsimp only [charSum, om]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hc0]
    refine add_le_add (le_refl _) ?_
    calc (∑ c ∈ Finset.univ.erase (⟨0, hp_pos⟩ : Fin prime), charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2).re
        ≤ ‖∑ c ∈ Finset.univ.erase (⟨0, hp_pos⟩ : Fin prime), charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ :=
          Complex.re_le_norm _
      _ ≤ ∑ c ∈ Finset.univ.erase (⟨0, hp_pos⟩ : Fin prime), ‖charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _c ∈ Finset.univ.erase (⟨0, hp_pos⟩ : Fin prime),
            Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) * (prime : ℝ) ^ H := by
          apply Finset.sum_le_sum
          intro c hc
          simp only [Finset.mem_erase, ne_eq, Fin.ext_iff] at hc
          have hcop : Nat.gcd c.val prime = 1 := by
            have hdvd := Nat.gcd_dvd_right c.val prime
            rcases hprime.eq_one_or_self_of_dvd _ hdvd with h1 | hp
            · exact h1
            · exfalso
              have hd := Nat.gcd_dvd_left c.val prime
              rw [hp] at hd
              have hle : prime ≤ c.val := Nat.le_of_dvd (Nat.pos_of_ne_zero hc.1) hd
              omega
          have h := norm_charSum_le_half hp_pos c.val (T τ).1 (T τ).2.1 (T τ).2.2
          rw [hcop] at h
          simpa using h
      _ = ((prime - 1 : Nat) : ℝ) * (prime : ℝ) ^ H * Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
  have hsum_ub := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin K))) (fun τ _ => hrect_ub τ)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum_ub
  have hpartR : (∑ τ : Fin K, ((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) = (prime : ℝ) ^ (2 * (2 * H)) := by
    have : (∑ τ : Fin K, ((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) =
        ((∑ τ : Fin K, (T τ).1.card * (T τ).2.1.card : Nat) : ℝ) := by
      push_cast; rfl
    rw [this, hpart]
    push_cast; rfl
  have hpart_sq : ∑ τ : Fin K, (T τ).1.card * (T τ).2.1.card = (prime ^ (2 * H)) ^ 2 := by
    rw [hpart, ← pow_mul, mul_comm 2]
  have hcs := sum_sqrt_le (fun τ => (T τ).1.card) (fun τ => (T τ).2.1.card) hpart_sq
  have hadvR : 2 * (prime : ℝ) ^ (2 * (2 * H)) ≤
      (prime : ℝ) * ∑ τ : Fin K,
        ((((T τ).1 ×ˢ (T τ).2.1).filter (fun AB =>
          (∑ i : Fin (2 * H), (AB.1 i).val * (AB.2 i).val) % prime = (T τ).2.2 AB.2 % prime)).card : ℝ) := by
    exact_mod_cast hadv
  have hineq : (prime : ℝ) ^ (2 * (2 * H)) ≤
      ((prime - 1 : Nat) : ℝ) * (prime : ℝ) ^ H * (Real.sqrt (K : ℝ) * ((prime ^ (2 * H) : Nat) : ℝ)) := by
    have h1 : (prime : ℝ) * ∑ τ : Fin K,
          ((((T τ).1 ×ˢ (T τ).2.1).filter (fun AB =>
            (∑ i : Fin (2 * H), (AB.1 i).val * (AB.2 i).val) % prime = (T τ).2.2 AB.2 % prime)).card : ℝ) ≤
        (prime : ℝ) ^ (2 * (2 * H)) +
          ((prime - 1 : Nat) : ℝ) * (prime : ℝ) ^ H * (Real.sqrt (K : ℝ) * ((prime ^ (2 * H) : Nat) : ℝ)) := by
      rw [hpartR] at hsum_ub
      refine le_trans hsum_ub (add_le_add (le_refl _) ?_)
      exact mul_le_mul_of_nonneg_left hcs (by positivity)
    linarith
  have hpow_fac : (prime : ℝ) ^ (2 * (2 * H)) = (prime : ℝ) ^ H * ((prime ^ (2 * H) : Nat) : ℝ) * (prime : ℝ) ^ H := by
    push_cast
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hpos_fac : 0 < (prime : ℝ) ^ H * ((prime ^ (2 * H) : Nat) : ℝ) := by
    have hpR : (0 : ℝ) < (prime : ℝ) := Nat.cast_pos.mpr hp_pos
    push_cast
    positivity
  have hroot : (prime : ℝ) ^ H ≤ ((prime - 1 : Nat) : ℝ) * Real.sqrt (K : ℝ) := by
    rw [hpow_fac] at hineq
    have hineq' : (prime : ℝ) ^ H * ((prime ^ (2 * H) : Nat) : ℝ) * (prime : ℝ) ^ H ≤
        (prime : ℝ) ^ H * ((prime ^ (2 * H) : Nat) : ℝ) * (((prime - 1 : Nat) : ℝ) * Real.sqrt (K : ℝ)) := by
      linarith
    exact le_of_mul_le_mul_left hineq' hpos_fac
  have hsq : ((prime : ℝ) ^ H) ^ 2 ≤ (((prime - 1 : Nat) : ℝ) * Real.sqrt (K : ℝ)) ^ 2 := by
    have hnn : 0 ≤ (prime : ℝ) ^ H := by positivity
    nlinarith
  rw [← pow_mul, mul_comm H 2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg K)] at hsq
  exact_mod_cast hsq

private theorem geom_half_sum_le (H : Nat) (hH : 2 ≤ H) (N : Nat) :
    ∑ t ∈ Finset.range (N + 1), (2 : ℝ) ^ t / (2 : ℝ) ^ (t * H) ≤ 2 := by
  have hstep : ∀ m : Nat, ∑ t ∈ Finset.range (m + 1), (1 / 2 : ℝ) ^ t = 2 - (1 / 2 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  calc ∑ t ∈ Finset.range (N + 1), (2 : ℝ) ^ t / (2 : ℝ) ^ (t * H)
      ≤ ∑ t ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ t := by
        apply Finset.sum_le_sum
        intro t _
        rw [one_div, inv_pow, div_le_iff₀ (by positivity)]
        have h1 : (2 : ℝ) ^ t * (2 : ℝ) ^ t ≤ (2 : ℝ) ^ (t * H) := by
          rw [← pow_add]
          exact pow_le_pow_right₀ (by norm_num) (by nlinarith)
        calc (2 : ℝ) ^ t = ((2 : ℝ) ^ t)⁻¹ * ((2 : ℝ) ^ t * (2 : ℝ) ^ t) := by
              field_simp
          _ ≤ ((2 : ℝ) ^ t)⁻¹ * (2 : ℝ) ^ (t * H) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 - (1 / 2 : ℝ) ^ N := hstep N
    _ ≤ 2 := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N]

private theorem pow2_lower_bound {H k j K : Nat} (hH : 2 ≤ H) (hjk : j ≤ k) (hK : 0 < K)
    (T : Fin K → Finset (Fin (2 * H) → Fin (2 ^ k)) × Finset (Fin (2 * H) → Fin (2 ^ k)) × ((Fin (2 * H) → Fin (2 ^ k)) → Nat))
    (hpart : ∑ τ : Fin K, (T τ).1.card * (T τ).2.1.card = (2 ^ k) ^ (2 * (2 * H)))
    (hadv : 2 ^ j * (2 ^ k) ^ (2 * (2 * H)) ≤ 2 ^ k * ∑ τ : Fin K,
      (((T τ).1 ×ˢ (T τ).2.1).filter (fun AB =>
        (∑ i : Fin (2 * H), (AB.1 i).val * (AB.2 i).val) % (2 ^ k) = (T τ).2.2 AB.2 % (2 ^ k))).card) :
    2 ^ (j * (2 * H)) ≤ 4 * K := by
  by_cases hj0 : j = 0
  · subst hj0
    simp only [zero_mul, pow_zero]
    omega
  have hj_pos : 0 < j := by omega
  let Q := 2 ^ k
  have hQ_pos : 0 < Q := by dsimp [Q]; positivity
  let Slow : Finset (Fin Q) := Finset.univ.filter (fun c : Fin Q => 2 ^ (k - j + 1) ∣ c.val)
  let Shigh : Finset (Fin Q) := Finset.univ.filter (fun c : Fin Q => ¬ (2 ^ (k - j + 1) ∣ c.val))
  have hcard_Slow : Slow.card = 2 ^ (j - 1) := by
    let f : Fin (2 ^ (j - 1)) → Fin Q := fun u =>
      ⟨u.val * 2 ^ (k - j + 1), by
        have hu : u.val < 2 ^ (j - 1) := u.isLt
        have hmul : 2 ^ (j - 1) * 2 ^ (k - j + 1) = Q := by
          dsimp only [Q]; rw [← pow_add]; congr 1; omega
        calc u.val * 2 ^ (k - j + 1) < 2 ^ (j - 1) * 2 ^ (k - j + 1) :=
              Nat.mul_lt_mul_of_pos_right hu (by positivity)
          _ = Q := hmul⟩
    have hSlow_eq : Slow = Finset.univ.image f := by
      ext c
      simp only [Slow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro ⟨u, hu⟩
        have hu_lt : u < 2 ^ (j - 1) := by
          have hmul : 2 ^ (k - j + 1) * 2 ^ (j - 1) = Q := by
            dsimp only [Q]; rw [← pow_add]; congr 1; omega
          have hlt : 2 ^ (k - j + 1) * u < 2 ^ (k - j + 1) * 2 ^ (j - 1) := by
            rw [← hu, hmul]; exact c.isLt
          exact Nat.lt_of_mul_lt_mul_left hlt
        exact ⟨⟨u, hu_lt⟩, Fin.ext (by dsimp [f]; linarith)⟩
      · intro ⟨u, hu⟩
        rw [← hu]
        exact ⟨u.val, by dsimp [f]; ring⟩
    rw [hSlow_eq, Finset.card_image_of_injective]
    · simp
    · intro u1 u2 h
      have h' : u1.val * 2 ^ (k - j + 1) = u2.val * 2 ^ (k - j + 1) := congrArg Fin.val h
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by positivity) h')
  let layer : Nat → Finset (Fin Q) := fun r =>
    Finset.univ.filter (fun c : Fin Q => Nat.gcd c.val Q = 2 ^ (k - r))
  have hcard_layer : ∀ r, 1 ≤ r → r ≤ k → (layer r).card ≤ 2 ^ (r - 1) := by
    intro r hr1 hrk
    let f : Fin (2 ^ (r - 1)) → Fin Q := fun u =>
      ⟨(2 * u.val + 1) * 2 ^ (k - r), by
        have hlt : 2 * u.val + 1 < 2 ^ r := by
          have hu : u.val < 2 ^ (r - 1) := u.isLt
          have h2 : 2 * 2 ^ (r - 1) = 2 ^ r := by
            rw [← pow_succ', Nat.sub_add_cancel hr1]
          omega
        have hmul : 2 ^ r * 2 ^ (k - r) = Q := by
          dsimp only [Q]; rw [← pow_add, Nat.add_sub_of_le hrk]
        calc (2 * u.val + 1) * 2 ^ (k - r) < 2 ^ r * 2 ^ (k - r) :=
              Nat.mul_lt_mul_of_pos_right hlt (by positivity)
          _ = Q := hmul⟩
    have hsub : layer r ⊆ Finset.univ.image f := by
      intro c hc
      simp only [layer, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      have hdvd : 2 ^ (k - r) ∣ c.val := hc ▸ Nat.gcd_dvd_left c.val Q
      obtain ⟨m, hm⟩ := hdvd
      have hm_odd : m % 2 = 1 := by
        by_contra heven
        have h2m : 2 ∣ m := by omega
        obtain ⟨m', rfl⟩ := h2m
        have hdvd1 : 2 ^ (k - r + 1) ∣ c.val := by
          refine ⟨m', ?_⟩
          rw [hm, pow_succ]
          ring
        have hdvd2 : 2 ^ (k - r + 1) ∣ Q :=
          Nat.pow_dvd_pow 2 (by omega)
        have hle : 2 ^ (k - r + 1) ≤ Nat.gcd c.val Q :=
          Nat.le_of_dvd (by rw [hc]; positivity) (Nat.dvd_gcd hdvd1 hdvd2)
        rw [hc, pow_succ] at hle
        have hpos : 0 < 2 ^ (k - r) := by positivity
        omega
      have hu_lt : m / 2 < 2 ^ (r - 1) := by
        have hmul : 2 ^ (k - r) * 2 ^ r = Q := by
          dsimp only [Q]; rw [← pow_add, Nat.sub_add_cancel hrk]
        have hm_lt : m < 2 ^ r := by
          have hlt : 2 ^ (k - r) * m < 2 ^ (k - r) * 2 ^ r := by
            rw [← hm, hmul]; exact c.isLt
          exact Nat.lt_of_mul_lt_mul_left hlt
        have h2 : 2 * 2 ^ (r - 1) = 2 ^ r := by rw [← pow_succ', Nat.sub_add_cancel hr1]
        omega
      refine Finset.mem_image.mpr ⟨⟨m / 2, hu_lt⟩, Finset.mem_univ _, Fin.ext ?_⟩
      dsimp only [f]
      have hdm := Nat.div_add_mod m 2
      rw [hm_odd] at hdm
      have hm2 : 2 * (m / 2) + 1 = m := by omega
      rw [hm2, mul_comm, ← hm]
    calc (layer r).card ≤ (Finset.univ.image f).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin (2 ^ (r - 1)))).card := Finset.card_image_le
      _ = 2 ^ (r - 1) := by simp
  have hShigh_sub : Shigh ⊆ (Finset.Icc j k).biUnion layer := by
    intro c hc
    simp only [Shigh, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have hdvdQ : Nat.gcd c.val Q ∣ 2 ^ k := Nat.gcd_dvd_right c.val Q
    obtain ⟨e, hek, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdQ
    have he_le : e ≤ k - j := by
      by_contra hgt
      have hge : k - j + 1 ≤ e := by omega
      apply hc
      exact dvd_trans (Nat.pow_dvd_pow 2 hge) (heq ▸ Nat.gcd_dvd_left c.val Q)
    refine Finset.mem_biUnion.mpr ⟨k - e, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simp only [layer, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq]
    congr 1
    omega
  have hrect_ub : ∀ τ : Fin K,
      (Q : ℝ) * ((((T τ).1 ×ˢ (T τ).2.1).filter (fun AB =>
        (∑ i : Fin (2 * H), (AB.1 i).val * (AB.2 i).val) % Q = (T τ).2.2 AB.2 % Q)).card : ℝ) ≤
      (2 : ℝ) ^ (j - 1) * (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) +
        ((2 : ℝ) ^ j / (2 : ℝ) ^ (j * H)) * (Q : ℝ) ^ (2 * H) *
          Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) := by
    intro τ
    rw [rect_hits_eq_sum_charSum hQ_pos]
    have hsplit : (Finset.univ : Finset (Fin Q)) = Slow ∪ Shigh := by
      ext c; simp [Slow, Shigh, em]
    have hdisj : Disjoint Slow Shigh := by
      rw [Finset.disjoint_left]; intro c h1 h2
      simp only [Slow, Shigh, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact h2 h1
    rw [hsplit, Finset.sum_union hdisj, Complex.add_re]
    have hlow_le : (∑ c ∈ Slow, charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2).re ≤
        (2 : ℝ) ^ (j - 1) * (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) := by
      calc (∑ c ∈ Slow, charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2).re
          ≤ ‖∑ c ∈ Slow, charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ := Complex.re_le_norm _
        _ ≤ ∑ c ∈ Slow, ‖charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ := norm_sum_le _ _
        _ ≤ ∑ _c ∈ Slow, ((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ) := by
            apply Finset.sum_le_sum
            intro c _
            dsimp only [charSum]
            calc ‖∑ A ∈ (T τ).1, ∑ B ∈ (T τ).2.1,
                    om Q c.val ((∑ i : Fin (2 * H), (A i).val * (B i).val : Nat) - ((T τ).2.2 B : ℤ))‖
                ≤ ∑ A ∈ (T τ).1, ∑ B ∈ (T τ).2.1,
                    ‖om Q c.val ((∑ i : Fin (2 * H), (A i).val * (B i).val : Nat) - ((T τ).2.2 B : ℤ))‖ := by
                  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun A _ => norm_sum_le _ _))
              _ = ((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ) := by
                  simp [norm_om]
        _ = (2 : ℝ) ^ (j - 1) * (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) := by
            rw [Finset.sum_const, hcard_Slow, nsmul_eq_mul]
            push_cast
            rfl
    have hhigh_le : (∑ c ∈ Shigh, charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2).re ≤
        ((2 : ℝ) ^ j / (2 : ℝ) ^ (j * H)) * (Q : ℝ) ^ (2 * H) *
          Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) := by
      calc (∑ c ∈ Shigh, charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2).re
          ≤ ‖∑ c ∈ Shigh, charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ := Complex.re_le_norm _
        _ ≤ ∑ c ∈ Shigh, ‖charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ := norm_sum_le _ _
        _ ≤ ∑ c ∈ (Finset.Icc j k).biUnion layer, ‖charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg hShigh_sub (fun _ _ _ => norm_nonneg _)
        _ ≤ ∑ r ∈ Finset.Icc j k, ∑ c ∈ layer r, ‖charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ := by
            have hbiU : ∀ s : Finset Nat,
                ∑ c ∈ s.biUnion layer, ‖charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ ≤
                ∑ r ∈ s, ∑ c ∈ layer r, ‖charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ := by
              intro s
              induction s using Finset.induction_on with
              | empty => simp
              | insert a s ha ih =>
                rw [Finset.biUnion_insert, Finset.sum_insert ha]
                have hun : ∀ A B : Finset (Fin Q),
                    ∑ c ∈ A ∪ B, ‖charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ ≤
                    ∑ c ∈ A, ‖charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ +
                    ∑ c ∈ B, ‖charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖ := by
                  intro A B
                  have h1 : A ∪ B = A ∪ (B \ A) := (Finset.union_sdiff_self_eq_union).symm
                  rw [h1, Finset.sum_union Finset.disjoint_sdiff]
                  exact add_le_add (le_refl _) (Finset.sum_le_sum_of_subset_of_nonneg
                    Finset.sdiff_subset (fun _ _ _ => norm_nonneg _))
                exact le_trans (hun _ _) (add_le_add (le_refl _) ih)
            exact hbiU (Finset.Icc j k)
        _ ≤ ∑ r ∈ Finset.Icc j k,
              (2 : ℝ) ^ (r - 1) * (Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) *
                ((Q : ℝ) ^ (2 * H) / (2 : ℝ) ^ (r * H))) := by
            apply Finset.sum_le_sum
            intro r hr
            simp only [Finset.mem_Icc] at hr
            calc ∑ c ∈ layer r, ‖charSum c.val (T τ).1 (T τ).2.1 (T τ).2.2‖
                ≤ ∑ _c ∈ layer r,
                    Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) *
                      ((Q : ℝ) ^ (2 * H) / (2 : ℝ) ^ (r * H)) := by
                  apply Finset.sum_le_sum
                  intro c hc
                  have hgcd : Nat.gcd c.val Q = 2 ^ (k - r) := (Finset.mem_filter.mp hc).2
                  have h := norm_charSum_le_half hQ_pos c.val (T τ).1 (T τ).2.1 (T τ).2.2
                  rw [hgcd] at h
                  have hfac : ((Q : ℝ) * ((2 ^ (k - r) : Nat) : ℝ)) ^ H =
                      (Q : ℝ) ^ (2 * H) / (2 : ℝ) ^ (r * H) := by
                    dsimp only [Q]
                    push_cast
                    rw [eq_div_iff (by positivity)]
                    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
                    congr 1
                    have hrk : r ≤ k := hr.2
                    have hsub : k * H + (k - r) * H + r * H = k * (2 * H) := by
                      have : (k - r) + r = k := Nat.sub_add_cancel hrk
                      nlinarith
                    exact hsub
                  rw [hfac] at h
                  exact h
              _ = ((layer r).card : ℝ) * (Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) *
                    ((Q : ℝ) ^ (2 * H) / (2 : ℝ) ^ (r * H))) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (2 : ℝ) ^ (r - 1) * (Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) *
                    ((Q : ℝ) ^ (2 * H) / (2 : ℝ) ^ (r * H))) := by
                  refine mul_le_mul_of_nonneg_right ?_
                    (mul_nonneg (Real.sqrt_nonneg _)
                      (div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (by norm_num) _)))
                  exact_mod_cast hcard_layer r (by omega) hr.2
        _ = (∑ r ∈ Finset.Icc j k, (2 : ℝ) ^ (r - 1) / (2 : ℝ) ^ (r * H)) *
              ((Q : ℝ) ^ (2 * H) * Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ))) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro r _
            ring
        _ ≤ ((2 : ℝ) ^ j / (2 : ℝ) ^ (j * H)) *
              ((Q : ℝ) ^ (2 * H) * Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_
              (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _))
            have hshift : (∑ r ∈ Finset.Icc j k, (2 : ℝ) ^ (r - 1) / (2 : ℝ) ^ (r * H)) =
                ((2 : ℝ) ^ (j - 1) / (2 : ℝ) ^ (j * H)) *
                  ∑ t ∈ Finset.range (k - j + 1), (2 : ℝ) ^ t / (2 : ℝ) ^ (t * H) := by
              rw [Finset.mul_sum]
              refine Finset.sum_bij (fun r _ => r - j) ?_ ?_ ?_ ?_
              · intro r hr
                simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
                omega
              · intro r1 hr1 r2 hr2 h
                simp only [Finset.mem_Icc] at hr1 hr2
                omega
              · intro t ht
                simp only [Finset.mem_range] at ht
                refine ⟨j + t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
              · intro r hr
                simp only [Finset.mem_Icc] at hr
                rw [div_mul_div_comm, ← pow_add, ← pow_add]
                congr 1
                · congr 1; omega
                · congr 1
                  have h1 : j + (r - j) = r := by omega
                  nlinarith
            rw [hshift]
            have hgeom := geom_half_sum_le H hH (k - j)
            have h2j : (2 : ℝ) ^ (j - 1) * 2 = (2 : ℝ) ^ j := by
              rw [← pow_succ, Nat.sub_add_cancel hj_pos]
            calc ((2 : ℝ) ^ (j - 1) / (2 : ℝ) ^ (j * H)) *
                    ∑ t ∈ Finset.range (k - j + 1), (2 : ℝ) ^ t / (2 : ℝ) ^ (t * H)
                ≤ ((2 : ℝ) ^ (j - 1) / (2 : ℝ) ^ (j * H)) * 2 :=
                  mul_le_mul_of_nonneg_left hgeom (by positivity)
              _ = (2 : ℝ) ^ j / (2 : ℝ) ^ (j * H) := by
                  rw [div_mul_eq_mul_div, h2j]
        _ = ((2 : ℝ) ^ j / (2 : ℝ) ^ (j * H)) * (Q : ℝ) ^ (2 * H) *
              Real.sqrt (((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) := by ring
    exact add_le_add hlow_le hhigh_le
  have hsum_ub := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin K))) (fun τ _ => hrect_ub τ)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_ub
  have hpartR : (∑ τ : Fin K, ((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) = (Q : ℝ) ^ (2 * (2 * H)) := by
    have : (∑ τ : Fin K, ((T τ).1.card : ℝ) * ((T τ).2.1.card : ℝ)) =
        ((∑ τ : Fin K, (T τ).1.card * (T τ).2.1.card : Nat) : ℝ) := by
      push_cast; rfl
    rw [this, hpart]
    dsimp only [Q]; push_cast; rfl
  have hpart_sq : ∑ τ : Fin K, (T τ).1.card * (T τ).2.1.card = (Q ^ (2 * H)) ^ 2 := by
    rw [hpart]; dsimp only [Q]; simp only [← pow_mul]; congr 1; ring
  have hcs := sum_sqrt_le (fun τ => (T τ).1.card) (fun τ => (T τ).2.1.card) hpart_sq
  have hadvR : (2 : ℝ) ^ j * (Q : ℝ) ^ (2 * (2 * H)) ≤
      (Q : ℝ) * ∑ τ : Fin K,
        ((((T τ).1 ×ˢ (T τ).2.1).filter (fun AB =>
          (∑ i : Fin (2 * H), (AB.1 i).val * (AB.2 i).val) % Q = (T τ).2.2 AB.2 % Q)).card : ℝ) := by
    exact_mod_cast hadv
  have h2j : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hj_pos]
  have hineq : (2 : ℝ) ^ (j - 1) * (Q : ℝ) ^ (2 * (2 * H)) ≤
      ((2 : ℝ) ^ j / (2 : ℝ) ^ (j * H)) * (Q : ℝ) ^ (2 * H) *
        (Real.sqrt (K : ℝ) * ((Q ^ (2 * H) : Nat) : ℝ)) := by
    rw [hpartR] at hsum_ub
    have h1 : (Q : ℝ) * ∑ τ : Fin K,
          ((((T τ).1 ×ˢ (T τ).2.1).filter (fun AB =>
            (∑ i : Fin (2 * H), (AB.1 i).val * (AB.2 i).val) % Q = (T τ).2.2 AB.2 % Q)).card : ℝ) ≤
        (2 : ℝ) ^ (j - 1) * (Q : ℝ) ^ (2 * (2 * H)) +
          ((2 : ℝ) ^ j / (2 : ℝ) ^ (j * H)) * (Q : ℝ) ^ (2 * H) *
            (Real.sqrt (K : ℝ) * ((Q ^ (2 * H) : Nat) : ℝ)) := by
      refine le_trans hsum_ub (add_le_add (le_refl _) ?_)
      exact mul_le_mul_of_nonneg_left hcs
        (mul_nonneg (div_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _))
          (pow_nonneg (Nat.cast_nonneg _) _))
    rw [h2j] at hadvR; linarith
  have hQpow : (Q : ℝ) ^ (2 * (2 * H)) = (Q : ℝ) ^ (2 * H) * ((Q ^ (2 * H) : Nat) : ℝ) := by
    push_cast
    rw [← pow_add, two_mul]
  have hpos_fac : 0 < (2 : ℝ) ^ (j - 1) * (Q : ℝ) ^ (2 * (2 * H)) := by
    have hQR : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ_pos
    positivity
  have hroot : (2 : ℝ) ^ (j * H) ≤ 2 * Real.sqrt (K : ℝ) := by
    have h1 : (2 : ℝ) ^ (j - 1) * (Q : ℝ) ^ (2 * (2 * H)) * 1 ≤
        (2 : ℝ) ^ (j - 1) * (Q : ℝ) ^ (2 * (2 * H)) * ((2 / (2 : ℝ) ^ (j * H)) * Real.sqrt (K : ℝ)) := by
      calc (2 : ℝ) ^ (j - 1) * (Q : ℝ) ^ (2 * (2 * H)) * 1
          = (2 : ℝ) ^ (j - 1) * (Q : ℝ) ^ (2 * (2 * H)) := mul_one _
        _ ≤ ((2 : ℝ) ^ j / (2 : ℝ) ^ (j * H)) * (Q : ℝ) ^ (2 * H) *
              (Real.sqrt (K : ℝ) * ((Q ^ (2 * H) : Nat) : ℝ)) := hineq
        _ = (2 : ℝ) ^ (j - 1) * (Q : ℝ) ^ (2 * (2 * H)) *
              ((2 / (2 : ℝ) ^ (j * H)) * Real.sqrt (K : ℝ)) := by
            rw [h2j, hQpow]; ring
    have h2 : (1 : ℝ) ≤ (2 / (2 : ℝ) ^ (j * H)) * Real.sqrt (K : ℝ) :=
      le_of_mul_le_mul_left h1 hpos_fac
    have h3 : (1 : ℝ) * (2 : ℝ) ^ (j * H) ≤ ((2 / (2 : ℝ) ^ (j * H)) * Real.sqrt (K : ℝ)) * (2 : ℝ) ^ (j * H) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have hne : ((2 : ℝ) ^ (j * H)) ≠ 0 := by positivity
    have h4 : ((2 / (2 : ℝ) ^ (j * H)) * Real.sqrt (K : ℝ)) * (2 : ℝ) ^ (j * H) = 2 * Real.sqrt (K : ℝ) := by
      field_simp [hne]
    linarith
  have hsq : ((2 : ℝ) ^ (j * H)) ^ 2 ≤ (2 * Real.sqrt (K : ℝ)) ^ 2 := by
    have hnn : 0 ≤ (2 : ℝ) ^ (j * H) := by positivity
    nlinarith
  rw [← pow_mul, mul_pow, Real.sq_sqrt (Nat.cast_nonneg K)] at hsq
  have hexp : j * H * 2 = j * (2 * H) := by ring
  rw [hexp] at hsq
  have h4 : (2 : ℝ) ^ 2 = (4 : ℝ) := by norm_num
  rw [h4] at hsq
  exact_mod_cast hsq

private theorem main_result (d n p k : Nat) (hd : 0 < d) (hp : 0 < p) (hk : 0 < k)
    (hn : 2 * (k * (2 * (d + 2) + (2 ^ (d + 2) - 1)) + (d + 2)) ≤ n) :
    let w := d + 2
    let D := 2 ^ w
    let M := 4 ^ d
    let Q := 2 ^ k
    ((∀ j : Nat, j ≤ k →
        succeedsProp w n p Q (2 ^ (j * (D * ((D + p - 1) / p) + 1))) (2 ^ (k - j)) (2 ^ j) Q ∧
        ∀ S R : Nat, 0 < R → succeedsProp w n p Q S R (2 ^ j) Q → 2 ^ (j * M) ≤ 4 * S ^ (2 * p - 1)) ∧
      ∀ prime S' R' : Nat, Nat.Prime prime → prime ≤ Q → 0 < R' →
        succeedsProp w n p prime S' R' 2 prime → prime ^ M ≤ (prime - 1) ^ 2 * S' ^ (2 * p - 1)) := by
  intro w D M Q
  have hn_pos : 0 < n := by omega
  let Hhalf := k * (2 * w + (2 ^ w - 1)) + w
  have hHn : Hhalf ≤ n := by dsimp [Hhalf, w]; omega
  obtain ⟨aliceRows, bobRows, hgadget⟩ := exists_ip_gadget d n k hd hk hn
  let HalfM := 2 * 4 ^ (d - 1)
  have hM_eq : M = 2 * HalfM := by
    dsimp only [M, HalfM]
    have h1 : 4 ^ d = 4 * 4 ^ (d - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hd]
    omega
  have hHalfM_ge : 2 ≤ HalfM := by
    dsimp only [HalfM]
    have : 1 ≤ 4 ^ (d - 1) := Nat.one_le_pow _ _ (by omega)
    omega
  let eM : Fin (2 * HalfM) ≃ Fin M := finCongr hM_eq.symm
  refine ⟨?_, ?_⟩
  · intro j hjk
    refine ⟨achieve_part d n p k j hp hn_pos hjk, ?_⟩
    intro S R hR hsucc
    have hQ_pos : 0 < Q := by dsimp [Q]; positivity
    let aliceQ : (Fin (2 * HalfM) → Fin Q) → Nat → Row := fun A => aliceRows (fun i => A (eM.symm i))
    let bobQ : (Fin (2 * HalfM) → Fin Q) → Nat → Row := fun B => bobRows (fun i => B (eM.symm i))
    have hgadQ : ∀ A B : Fin (2 * HalfM) → Fin Q,
        totalCount w n (fun site => if site < Hhalf then aliceQ A site else bobQ B (site - Hhalf)) =
          ∑ i : Fin (2 * HalfM), (A i).val * (B i).val := by
      intro A B
      rw [hgadget]
      exact Equiv.sum_comp eM.symm (fun i => (A i).val * (B i).val)
    obtain ⟨hS_pos, T, hpart, hadv⟩ :=
      rectangle_partition hQ_pos hp hR hHn aliceQ bobQ w hgadQ hsucc
    have hK_pos : 0 < S ^ (2 * p - 1) := pow_pos hS_pos _
    rw [hM_eq]
    exact pow2_lower_bound hHalfM_ge hjk hK_pos T hpart hadv
  · intro prime S' R' hprime hpleQ hR' hsucc
    have hp_pos : 0 < prime := hprime.pos
    let lift : Fin prime → Fin Q := fun x => ⟨x.val, lt_of_lt_of_le x.isLt hpleQ⟩
    let aliceP : (Fin (2 * HalfM) → Fin prime) → Nat → Row :=
      fun A => aliceRows (fun i => lift (A (eM.symm i)))
    let bobP : (Fin (2 * HalfM) → Fin prime) → Nat → Row :=
      fun B => bobRows (fun i => lift (B (eM.symm i)))
    have hgadP : ∀ A B : Fin (2 * HalfM) → Fin prime,
        totalCount w n (fun site => if site < Hhalf then aliceP A site else bobP B (site - Hhalf)) =
          ∑ i : Fin (2 * HalfM), (A i).val * (B i).val := by
      intro A B
      rw [hgadget]
      exact Equiv.sum_comp eM.symm (fun i => (A i).val * (B i).val)
    obtain ⟨hS'_pos, T, hpart, hadv⟩ :=
      rectangle_partition hp_pos hp hR' hHn aliceP bobP w hgadP hsucc
    have hK_pos : 0 < S' ^ (2 * p - 1) := pow_pos hS'_pos _
    rw [hM_eq]
    exact prime_lower_bound hprime hK_pos T hpart hadv

end PEqualNP.Outside.L_clb_089_aux

theorem PEqualNP.Outside.L_clb_089 : ∀ (d n p k : Nat), 0 < d → 0 < p → 0 < k →
  let w := d+2
  let D := 2^w
  let M := 4^d
  let Q := 2^k
  2*(k*(2*w+(2^w-1))+w) ≤ n →
  let Row := Nat → Bool
  let total := fun (rows : Nat → Row) =>
    ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
        acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
      rows site pat))).length
  let run := fun (S : Nat) (start : Fin S)
      (step : Nat → Nat → Fin S → Row → Fin S) (table : Nat → Row) =>
    (List.range p).foldl (fun prev passId =>
      (List.range n).foldl (fun state siteId => step passId siteId state (table siteId)) prev) start
  let succeeds := fun (m S R a b : Nat) =>
    ∃ (init : Fin R → Fin S) (update : Fin R → Nat → Nat → Fin S → Row → Fin S)
      (output : Fin R → Fin S → Nat), ∀ input : Nat → Row,
        a*R ≤ b*((List.finRange R).filter (fun coin =>
          output coin (run S (init coin) (update coin) input) == (total input)%m)).length
  ((∀ j : Nat, j ≤ k →
      succeeds Q (2^(j*(D*((D+p-1)/p)+1))) (2^(k-j)) (2^j) Q ∧
      ∀ S R : Nat, 0 < R → succeeds Q S R (2^j) Q → 2^(j*M) ≤ 4*S^(2*p-1)) ∧
    ∀ prime S' R' : Nat, Nat.Prime prime → prime ≤ Q → 0 < R' →
      succeeds prime S' R' 2 prime → prime^M ≤ (prime-1)^2*S'^(2*p-1)) := by
  intro d n p k hd hp hk w D M Q hn
  exact PEqualNP.Outside.L_clb_089_aux.main_result d n p k hd hp hk hn
