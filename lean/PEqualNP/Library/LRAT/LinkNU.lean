import PEqualNP.Library.LRAT.PromiseN

/-!
# Refusal certificates with NOT gates for circuits that leave named input wires unread

A circuit LEAVES WIRE `w` UNREAD when no gate lists `w` among its inputs and the output is not `w`.
For a list `U` of input wires (each below `n`), `fUnread n s U` adds to the NOT encoding the unit
clauses "no source of any gate is in `U`, and the output source is not in `U`".

The link: a circuit leaving `U` unread gives a model whose sources avoid `U` (`noU_ofCirc`); the
normal-form argument of `LinkN2.exists_nf2` is redone among such models only (`exists_nf2U`): every
move it makes (moving a trivial gate to the front, swapping sources, exchanging adjacent gates)
relabels gate wires only, and every redirect target it uses is a constant, a source of the gate, or
a gate wire (`GoodT`), so the sources keep avoiding `U`. `promiseNU_lower` and
`repNU_lower_mask` then turn one unsatisfiable formula into the floor for such circuits.
-/

namespace PEqualNP.Library.LRAT.LinkN

/-- No source of a gate below `s`, and not the output source, is in `U`. -/
def NoU (U : ℕ → Prop) (s : ℕ) (M : Model) : Prop :=
  (∀ j < s, ¬ U (M.s1 j) ∧ ¬ U (M.s2 j)) ∧ ¬ U M.so

/-- A redirect target that is a constant or names a wire outside `U`. -/
def GoodT (U : ℕ → Prop) (t : ℕ) : Prop := t ≤ 1 ∨ ¬ U (t - 2)

section unread
variable {n s : ℕ} {U : ℕ → Prop} (hUn : ∀ k, U k → k < n)
include hUn

theorem nU_ge {k : ℕ} (hk : n ≤ k) : ¬ U k := fun h => by have := hUn k h; omega

theorem nU_phi {d k : ℕ} (h : ¬ U k) : ¬ U (phi n d k) := by
  unfold phi
  split_ifs with h1 h2
  · exact h
  · exact nU_ge hUn (by omega)
  · exact h

theorem nU_rd {d t j k : ℕ} (hk : ¬ U k) (ht : GoodT U t) : ¬ U (rd n d t j k) := by
  unfold rd
  split_ifs with h1 h2 h3
  · exact nU_ge hUn (by omega)
  · exact nU_ge hUn (by omega)
  · rcases ht with ht | ht
    · omega
    · exact nU_phi hUn ht
  · exact nU_phi hUn hk

theorem noU_mv {M : Model} {d t : ℕ} (hM : NoU U s M) (hd : d < s) (ht : GoodT U t) :
    NoU U s (mv n s M d t) := by
  refine ⟨fun j hj => ?_, ?_⟩
  · simp only [mv]
    split_ifs with h0 h1
    · exact ⟨nU_ge hUn le_rfl, nU_ge hUn le_rfl⟩
    · have := hM.1 (j - 1) (by omega)
      exact ⟨nU_phi hUn this.1, nU_phi hUn this.2⟩
    · have := hM.1 j hj
      exact ⟨nU_rd hUn this.1 ht, nU_rd hUn this.2 ht⟩
  · simp only [mv]
    exact nU_rd hUn hM.2 ht

theorem nU_tsw {j k : ℕ} (h : ¬ U k) : ¬ U (tsw n j k) := by
  unfold tsw
  split_ifs
  · exact nU_ge hUn (by omega)
  · exact nU_ge hUn (by omega)
  · exact h

theorem noU_xsw {M : Model} {j : ℕ} (hM : NoU U s M) (hj : j + 1 < s) : NoU U s (xsw n M j) := by
  refine ⟨fun i hi => ?_, ?_⟩
  · simp only [xsw]
    split_ifs
    · exact hM.1 (j + 1) hj
    · exact hM.1 j (by omega)
    · have := hM.1 i hi
      exact ⟨nU_tsw hUn this.1, nU_tsw hUn this.2⟩
    · exact hM.1 i hi
  · simp only [xsw]
    exact nU_tsw hUn hM.2

end unread

theorem noU_sw {U : ℕ → Prop} {s : ℕ} {M : Model} (hM : NoU U s M) (j : ℕ) : NoU U s (sw M j) := by
  refine ⟨fun i hi => ?_, hM.2⟩
  simp only [sw]
  split_ifs with h
  · subst h
    exact ⟨(hM.1 i hi).2, (hM.1 i hi).1⟩
  · exact hM.1 i hi

/-! ## Trivial gates have good targets -/

section trivU
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {U : ℕ → Prop}
  (hv : Valid n s g R M) {j : ℕ} (hj : j < s)
include hv hj

theorem copy_tgtU {k : ℕ} (hk : k ≤ n + j) (hku : ¬ U k) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ GoodT U t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), Or.inr (by simpa using hku), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, Or.inl (by omega), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgtU (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ GoodT U t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, Or.inl (by omega), fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), Or.inl (by omega), fun r hr => by rw [hw r hr]; simp [tval]⟩

theorem op2_trivU (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ GoodT U t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgtU true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

theorem false_srcU (hu1 : ¬ U (M.s1 j)) (hu2 : ¬ U (M.s2 j))
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ GoodT U t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgtU false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgtU hv hj (hv.s2_le j hj) hu2 fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgtU hv hj (hv.s1_le j hj) hu1 fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · by_cases h3 : M.op j = 3
      · have he := hv.not_eq j hj h3
        refine const_tgtU true fun r hr => ?_
        rw [hw r hr, h3]
        rcases h with h | h
        · simp [gfun, h r hr]
        · rw [he]; simp [gfun, h r hr]
      · exact op2_trivU hv hj (by omega)

theorem true_srcU (hu1 : ¬ U (M.s1 j)) (hu2 : ¬ U (M.s2 j))
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ GoodT U t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgtU hv hj (hv.s2_le j hj) hu2 fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgtU hv hj (hv.s1_le j hj) hu1 fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgtU true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · by_cases h3 : M.op j = 3
      · have he := hv.not_eq j hj h3
        refine const_tgtU false fun r hr => ?_
        rw [hw r hr, h3]
        rcases h with h | h
        · simp [gfun, h r hr]
        · rw [he]; simp [gfun, h r hr]
      · exact op2_trivU hv hj (by omega)

theorem notnot_trivU (hUn : ∀ k, U k → k < n) {i : ℕ} (hi : i < j) (h3 : M.op j = 3)
    (hi3 : M.op i = 3) (hui : ¬ U (M.s1 i)) (he : M.s1 j = n + i) :
    ∃ t, TgtOk n j t ∧ GoodT U t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hle := hv.s1_le i (by omega)
  refine copy_tgtU hv hj (k := if M.s1 i < n + i then M.s1 i else n + j) (by split_ifs <;> omega)
    (by split_ifs
        · exact hui
        · exact nU_ge hUn (by omega))
    fun r hr => ?_
  have e1 : M.sv n j (n + i) r = M.w i r := by
    unfold Model.sv
    simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
      show n + i - n = i by omega]
  rw [hv.w_eq j hj r hr, h3, he, e1, hv.w_eq i (by omega) r hr, hi3]
  simp only [gfun, show ¬ (3 : ℕ) = 0 by omega, show ¬ (3 : ℕ) = 1 by omega, if_true, if_false,
    Bool.not_not]
  unfold Model.sv
  by_cases h6 : M.s1 i < n + i
  · simp only [if_pos h6]
    by_cases h7 : M.s1 i < n
    · simp [h7]
    · simp only [if_neg h7, if_pos (show M.s1 i < n + j by omega)]
  · simp only [if_neg h6, if_neg (show ¬ M.s1 i < n by omega), if_neg (show ¬ n + j < n by omega),
      if_neg (show ¬ n + j < n + j by omega)]

theorem same_srcU (hu1 : ¬ U (M.s1 j)) (h3 : M.op j ≠ 3) (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ GoodT U t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_trivU hv hj h2
  refine copy_tgtU hv hj (hv.s1_le j hj) hu1 fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  simp only [if_neg h3]
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end trivU


/-! ## The normal form among models avoiding `U` -/

/-- A model of least `meas2` is in normal form (the argument of `exists_nf`, with `meas2`). -/
theorem nf_of_min2U {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {U : ℕ → Prop} (hv : Valid n s g R M)
    (hUn : ∀ k, U k → k < n) (hM : NoU U s M)
    (hmin : ∀ M', Valid n s g R M' → NoU U s M' → meas2 n s M' < meas2 n s M → False) : NF n s M := by
  classical
  have hmv : ∀ d t, d < s → TgtOk n d t → GoodT U t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht hg htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (noU_mv hUn hM hd hg) (meas2_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ GoodT U t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hg, hw⟩
    exact hmv d t hd ht hg (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_trivU hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_srcU hv hj (hM.1 j hj).1 (hM.1 j hj).2 ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_srcU hv hj (hM.1 j hj).1 (hM.1 j hj).2 ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have notNot : ∀ j < s, ∀ i < j, M.op j = 3 → M.op i = 3 → M.s1 j ≠ n + i := by
    intro j hj i hi h3 hi3 he
    exact htriv j hj (fun hp => by have := hp.1; omega) (notnot_trivU hv hj hUn hi h3 hi3 (hM.1 i (by omega)).1 he)
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j ∨ (M.op j = 3 ∧ M.s1 j = M.s2 j) := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_srcU hv hj (hM.1 j hj).1 (fun h3 => hc (Or.inr ⟨h3, he⟩)) he)
    · exact hmin _ (valid_sw hv j) (noU_sw hM j) (meas2_sw hv hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl)) (Or.inl (by omega))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (Or.inl (by omega)) (fun h => absurd h hc) (Or.inl hnp)
  refine {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    notNot := notNot
    used := ?_
    out := ?_ }
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by
          have := hall (s - 1 - j) (by omega)
          rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

/-- A model of least `meas2` is lexicographically ordered. -/

theorem lex_of_min2U {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {U : ℕ → Prop} (hv : Valid n s g R M)
    (hUn : ∀ k, U k → k < n) (hM : NoU U s M)
    (hmin : ∀ M', Valid n s g R M' → NoU U s M' → meas2 n s M' < meas2 n s M → False) : LexNF n s M := by
  have hnf := nf_of_min2U hv hUn hM hmin
  intro j hj hnp ha hb
  have hnp1 : ¬ M.pad n (j + 1) := fun h => hnp (hnf.pre j hj h)
  have f0 := hnf.noF j (by omega) hnp
  have f1 := hnf.noF (j + 1) hj hnp1
  have l1 := hv.s1_le j (by omega)
  have l2 := hv.s2_le j (by omega)
  have l3 := hv.s1_le (j + 1) hj
  have l4 := hv.s2_le (j + 1) hj
  have h1 : M.s1 j < n + j := by omega
  have h2 : M.s2 j < n + j := by omega
  have h3 : M.s1 (j + 1) < n + j := by omega
  have h4 : M.s2 (j + 1) < n + j := by omega
  have o0 := hv.op_lt j (by omega)
  have o1 := hv.op_lt (j + 1) hj
  have o0' : M.op j ≠ 2 := fun h => hnp (hnf.padOp j (by omega) h)
  have o1' : M.op (j + 1) ≠ 2 := fun h => hnp1 (hnf.padOp (j + 1) hj h)
  -- a strictly smaller key at `j + 1` contradicts minimality through `xsw`
  have hx : lexKey n s M (j + 1) < lexKey n s M j → False := fun hlt =>
    hmin _ (valid_xsw hv hj h1 h2 h3 h4) (noU_xsw hUn hM hj) (meas2_xsw hv hj h1 h2 h3 h4 hlt)
  have hK : ∀ y z : ℕ, y < n + j → z < 4 → y * 4 + z < 4 * (n + s + 1) := by
    intro y z hy hz; omega
  by_contra hc
  rcases lt_trichotomy (M.s1 j) (M.s1 (j + 1)) with e1 | e1 | e1
  · exact hc (Or.inl e1)
  · rcases lt_trichotomy (M.s2 j) (M.s2 (j + 1)) with e2 | e2 | e2
    · exact hc (Or.inr ⟨e1, Or.inl e2⟩)
    · by_cases e3 : M.op j = M.op (j + 1)
      · -- gate `j + 1` is a copy of wire `n + j`
        have hw : ∀ r, R r → M.w (j + 1) r = M.sv n (j + 1) (n + j) r := by
          intro r hr
          have hs : ∀ k, k < n + j → M.sv n (j + 1) k r = M.sv n j k r := by
            intro k hk
            unfold Model.sv
            by_cases h6 : k < n
            · simp [h6]
            · simp only [if_neg h6, if_pos hk, if_pos (show k < n + (j + 1) by omega)]
          rw [hv.w_eq (j + 1) hj r hr, hs _ h3, hs _ h4, ← e1, ← e2, ← e3,
            ← hv.w_eq j (by omega) r hr]
          unfold Model.sv
          simp only [if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + (j + 1) by omega),
            show n + j - n = j by omega]
        obtain ⟨t, ht, hg, htw⟩ := copy_tgtU hv hj (k := n + j) (by omega) (nU_ge hUn (by omega)) hw
        have hv' := valid_mv hv hj ht (fun _ => htw)
        exact hmin _ hv' (noU_mv hUn hM hj hg) (meas2_mv hv hv' hj (Or.inl hnp1))
      · have q0 := hnf.ord j (by omega) hnp
        have q1 := hnf.ord (j + 1) hj hnp1
        have n0 := hv.not_eq j (by omega)
        have n1 := hv.not_eq (j + 1) hj
        have : M.op j = 0 ∧ M.op (j + 1) = 1 ∨ M.op (j + 1) < M.op j := by omega
        rcases this with h | h
        · exact hc (Or.inr ⟨e1, Or.inr ⟨e2, h⟩⟩)
        · apply hx
          unfold lexKey
          exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inr ⟨e2.symm, h⟩⟩)
    · apply hx
      unfold lexKey
      exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inl e2⟩)
  · apply hx
    unfold lexKey
    exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inl e1)

/-- Among valid models whose sources avoid `U` there is one in normal form and lexicographically
ordered, still avoiding `U`. -/
theorem exists_nf2U {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {U : ℕ → Prop} (hUn : ∀ k, U k → k < n)
    (h : ∃ M, Valid n s g R M ∧ NoU U s M) :
    ∃ M, Valid n s g R M ∧ NoU U s M ∧ NF n s M ∧ LexNF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ NoU U s M ∧ meas2 n s M = m := by
    obtain ⟨M, h1, h2⟩ := h
    exact ⟨_, M, h1, h2, rfl⟩
  obtain ⟨M, hv, hM, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → NoU U s M' → meas2 n s M' < meas2 n s M → False := by
    intro M' h1 h2 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, h2, rfl⟩
  exact ⟨M, hv, hM, nf_of_min2U hv hUn hM hmin, lex_of_min2U hv hUn hM hmin⟩


/-! ## The unit clauses and the link -/

section formulaU
variable (n s : ℕ)

/-- No source of a gate, and not the output source, is a wire of `U`. -/
def fUnread (U : List ℕ) : List (List ℕ) :=
  ([1, 2].flatMap fun e => (List.range s).flatMap fun j => U.map fun w => [Q (ix n s e j w)]) ++
    U.map fun w => [Q (ix n s 6 0 w)]

end formulaU

theorem s_fUnread {n s : ℕ} {M : Model} {U : List ℕ} (hUn : ∀ w ∈ U, w < n)
    (hM : NoU (· ∈ U) s M) : ∀ c ∈ fUnread n s U, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUnread, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  have hwd : ∀ w ∈ U, w < wd n s := fun w hw => wd_lt1 (by have := hUn w hw; omega)
  rcases hc with ⟨e, he, j, hj, w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [litVal_Q]
    rcases he with rfl | rfl
    · rw [v_s1 M (by omega) (hwd w hw)]
      have := (hM.1 j hj).1
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
      exact fun h => this (h ▸ hw)
    · rw [v_s2 M (by omega) (hwd w hw)]
      have := (hM.1 j hj).2
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
      exact fun h => this (h ▸ hw)
  · refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [litVal_Q, v_so M (hwd w hw)]
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
    exact fun h => hM.2 (h ▸ hw)

open PEqualNP.CircuitLowerBounds in
theorem code_src1 (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).2.1 = n + j ∨ ∃ a ∈ g.inputs, (code n g j).2.1 = nm n j a := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _⟩⟩ <;> simp [code]

open PEqualNP.CircuitLowerBounds in
theorem code_src2 (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).2.2 = n + j ∨ ∃ a ∈ g.inputs, (code n g j).2.2 = nm n j a := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _⟩⟩ <;> simp [code]

open PEqualNP.CircuitLowerBounds in
/-- A circuit leaving the wires of `U` unread gives a model whose sources avoid `U`. -/
theorem noU_ofCirc (n s : ℕ) (C : Circuit) (U : List ℕ) (hUn : ∀ w ∈ U, w < n)
    (hread : ∀ gt ∈ C.gates, ∀ i ∈ gt.inputs, i ∉ U) (hout : C.output ∉ U) :
    NoU (· ∈ U) s (ofCirc n s C) := by
  have hge : ∀ k, n ≤ k → k ∉ U := fun k hk h => by have := hUn k h; omega
  have hsrc : ∀ j (x : ℕ), (x = n + j ∨ ∃ a ∈ (gateAt C j).inputs, x = nm n j a) → x ∉ U := by
    intro j x hx
    rcases hx with rfl | ⟨a, ha, rfl⟩
    · exact hge _ (by omega)
    · unfold nm
      split_ifs with h
      · unfold gateAt at ha
        by_cases hj : j < C.gates.length
        · rw [List.getD_eq_getElem _ _ hj] at ha
          exact hread _ (List.getElem_mem hj) a ha
        · rw [List.getD_eq_default _ _ (by omega)] at ha
          simp at ha
      · exact hge _ (by omega)
  refine ⟨fun j _ => ⟨hsrc j _ (code_src1 n _ j), hsrc j _ (code_src2 n _ j)⟩, ?_⟩
  simp only [ofCirc]
  split_ifs
  · exact hout
  · exact hge _ (by omega)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
/-- A circuit with NOT gates leaving the wires of `U` unread and right on the listed rows has
more than `s` gates when `enc2 n s g rows ++ fUnread n s U` is unsatisfiable. -/
theorem promiseNU_lower (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (U : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hUn : ∀ w ∈ U, w < n)
    (hU : ¬ FormulaSat (enc2 n s g rows ++ fUnread n s U)) (C : Circuit) (hC : FanInTwo C)
    (hread : ∀ gt ∈ C.gates, ∀ i ∈ gt.inputs, i ∉ U) (hout : C.output ∉ U)
    (hev : ∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i) = g r) :
    s + 1 ≤ C.size := by
  by_contra h
  have hv := valid_ofCirc n s g (· ∈ rows) C hC (by simp only [Circuit.size] at h; omega)
    (fun r hr => hev r hr)
  obtain ⟨M, hM, hnoU, hnf, hlx⟩ :=
    exists_nf2U (U := (· ∈ U)) hUn ⟨_, hv, noU_ofCirc n s C U hUn hread hout⟩
  refine hU ⟨val n s M, fun c hc => ?_⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact enc2_sat hrows hM hnf hlx c hc
  · exact s_fUnread hUn hnoU c hc


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents in
/-- The floor on the `n` by `m` representing problem for circuits with NOT gates leaving the
wires of `U` unread (`U` a `Finset`, `L` a list with the same members, used in the formula). -/
theorem repNU_lower_mask (n m M s : ℕ) (U : Finset ℕ) (L : List ℕ) (hL : ∀ i, i ∈ L ↔ i ∈ U)
    (hUn : ∀ w ∈ L, w < n + m)
    (hU : ¬ FormulaSat (enc2 (n + m) s (Promise.gMask n m M) (Promise.repRows n m) ++
      fUnread (n + m) s L)) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ U) ∧
      C.output ∉ U ∧ Represents (fun (u : Fin n) (v : Fin m) => M.testBit (m * u + v)) C := by
  rintro ⟨C, hC, hs, hread, hout, hr⟩
  have hmem : ∀ r ∈ Promise.repRows n m, ∃ (u : Fin n) (v : Fin m), Promise.repRow n u v = r := by
    intro r hr'
    simpa [Promise.repRows] using hr'
  have hrow : ∀ r ∈ Promise.repRows n m, r < 2 ^ (n + m) := by
    intro r hr'
    obtain ⟨u, v, rfl⟩ := hmem r hr'
    refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    rw [Promise.repRow_testBit u.2]
    have := u.2; have := v.2
    simp; omega
  have := promiseNU_lower (n + m) s (Promise.gMask n m M) (Promise.repRows n m) L hrow hUn hU C hC
    (fun gt hg i hi h => hread gt hg i hi ((hL i).1 h)) (fun h => hout ((hL _).1 h)) (by
      intro r hr'
      obtain ⟨u, v, rfl⟩ := hmem r hr'
      rw [Promise.repRow_eq, hr, Promise.gMask_row])
  omega

end PEqualNP.Library.LRAT.LinkN
