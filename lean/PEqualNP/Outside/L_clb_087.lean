import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_377

namespace PEqualNP.Outside.L_clb_087

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

private theorem batch_mod (n w p j : Nat) (hn : 0 < n) (hp : 0 < p) :
    let D := 2^w
    ∃ (start : Fin (2^(j*(D*((D+p-1)/p)+1))))
      (step : Nat → Nat → Fin (2^(j*(D*((D+p-1)/p)+1))) → Row → Fin (2^(j*(D*((D+p-1)/p)+1))))
      (answer : Fin (2^(j*(D*((D+p-1)/p)+1))) → Nat),
      ∀ input : Nat → Row,
        answer (runAlg p n _ start step input) = totalCount w n input % (2^j) := by
  intro D
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
  let initAlg : Fin (2 ^ (j * (D * B + 1))) := enc initSt
  let updAlg : Nat → Nat → Fin (2 ^ (j * (D * B + 1))) → Row →
      Fin (2 ^ (j * (D * B + 1))) :=
    fun passId siteId s row => enc (stepSt passId siteId (enc.symm s) row)
  let outAlg : Fin (2 ^ (j * (D * B + 1))) → Nat := fun s =>
    let st := enc.symm s
    (foldDiag st.1 st.2 (p - 1)).val
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
  dsimp only [outAlg, runAlg, initAlg, updAlg]
  rw [hrun_conj p, Equiv.symm_apply_apply]
  exact hlow

end PEqualNP.Outside.L_clb_087

open PEqualNP.Outside.L_clb_087 in
theorem PEqualNP.Outside.L_clb_087 : ∀ (n w p : Nat), 0 < n → 0 < w → 0 < p →
  let D := 2^w
  let slots := (D+p-1)/p
  let Row := Nat → Bool
  let parity := fun (rows : Nat → Row) =>
    ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
        acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
      rows site pat))).length.testBit 0
  let run := fun (S : Nat) (start : Fin S)
      (step : Nat → Nat → Fin S → Row → Fin S) (table : Nat → Row) =>
    (List.range p).foldl (fun prev passId =>
      (List.range n).foldl (fun state siteId => step passId siteId state (table siteId)) prev) start
  let S := 2^(D*slots+1)
  ∃ (start : Fin S) (step : Nat → Nat → Fin S → Row → Fin S) (answer : Fin S → Bool),
    ∀ input : Nat → Row, answer (run S start step input) = parity input := by
  intro n w p hn _hw hp D slots Row parity run S
  have h := batch_mod n w p 1 hn hp
  dsimp only at h
  have hsize : 2 ^ (1 * (2 ^ w * ((2 ^ w + p - 1) / p) + 1)) = S := by
    simp [S, D, slots]
  rw [hsize] at h
  simp only [pow_one] at h
  obtain ⟨start, step, answer, hanswer⟩ := h
  refine ⟨start, step, fun st => (answer st).testBit 0, ?_⟩
  intro input
  change (answer (runAlg p n S start step input)).testBit 0 =
    (totalCount w n input).testBit 0
  rw [hanswer input]
  simp only [Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one, Nat.mod_mod]
