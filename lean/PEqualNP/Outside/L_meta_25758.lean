import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25758_aux

private def radFn (f : Bool → Bool → Bool) : ℕ :=
  let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
  if ones = 0 ∨ ones = 4 then 1 else if ones = 2 then 2 else 3

private theorem radFn_pos (f : Bool → Bool → Bool) : 0 < radFn f := by
  dsimp only [radFn]
  split_ifs <;> omega

private def tab (b00 b01 b10 b11 : Bool) : Bool → Bool → Bool
  | false, false => b00
  | false, true => b01
  | true, false => b10
  | true, true => b11

private theorem eq_tab (f : Bool → Bool → Bool) :
    f = tab (f false false) (f false true) (f true false) (f true true) := by
  funext a b
  cases a <;> cases b <;> rfl

private def colorRaw (f : Bool → Bool → Bool) (u : Bool × Bool) : ℕ :=
  let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
  if ones = 0 ∨ ones = 4 then 0
  else if ones = 2 then
    if f false false = f false true then u.1.toNat
    else if f false false = f true false then u.2.toNat
    else (Bool.xor u.1 u.2).toNat
  else
    let maj : Bool := decide (ones = 3)
    let a0 : Bool := decide (f false false = maj ∧ f false true = maj)
    let b0 : Bool := decide (f false false = maj ∧ f true false = maj)
    if u.1 = a0 ∧ u.2 = b0 then 0
    else if u.1 = a0 then 1
    else if u.2 = b0 then 2
    else 0

private theorem colorRaw_lt_tab :
    ∀ b00 b01 b10 b11 : Bool, ∀ u : Bool × Bool,
      colorRaw (tab b00 b01 b10 b11) u < radFn (tab b00 b01 b10 b11) := by
  decide

private theorem colorRaw_spec_tab :
    ∀ b00 b01 b10 b11 : Bool, ∀ u v : Bool × Bool,
      tab b00 b01 b10 b11 u.1 v.2 ≠ tab b00 b01 b10 b11 v.1 u.2 →
        colorRaw (tab b00 b01 b10 b11) u ≠ colorRaw (tab b00 b01 b10 b11) v := by
  decide

private def colorGate (f : Bool → Bool → Bool) (u : Bool × Bool) : Fin (radFn f) :=
  ⟨colorRaw f u, by
    rw [eq_tab f]
    exact colorRaw_lt_tab _ _ _ _ u⟩

private theorem colorGate_spec (f : Bool → Bool → Bool) (u v : Bool × Bool)
    (hne : f u.1 v.2 ≠ f v.1 u.2) :
    colorGate f u ≠ colorGate f v := by
  intro heq
  have hval : colorRaw f u = colorRaw f v := congrArg Fin.val heq
  rw [eq_tab f] at hne hval
  exact colorRaw_spec_tab _ _ _ _ u v hne hval

private def embedRaw (f : Bool → Bool → Bool) (k : ℕ) : Bool × Bool :=
  let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
  if ones = 0 ∨ ones = 4 then (false, false)
  else if ones = 2 then
    if f false false = f false true then (decide (k = 1), false)
    else if f false false = f true false then (false, decide (k = 1))
    else (decide (k = 1), false)
  else
    let maj : Bool := decide (ones = 3)
    let a0 : Bool := decide (f false false = maj ∧ f false true = maj)
    let b0 : Bool := decide (f false false = maj ∧ f true false = maj)
    if k = 0 then (a0, b0)
    else if k = 1 then (a0, !b0)
    else (!a0, b0)

private theorem embedRaw_spec_tab :
    ∀ b00 b01 b10 b11 : Bool,
      ∀ d₁ d₂ : Fin (radFn (tab b00 b01 b10 b11)), d₁ ≠ d₂ →
        tab b00 b01 b10 b11 (embedRaw (tab b00 b01 b10 b11) d₁.val).1
            (embedRaw (tab b00 b01 b10 b11) d₂.val).2 ≠
          tab b00 b01 b10 b11 (embedRaw (tab b00 b01 b10 b11) d₂.val).1
            (embedRaw (tab b00 b01 b10 b11) d₁.val).2 := by
  decide

private def embedGate (f : Bool → Bool → Bool) (d : Fin (radFn f)) : Bool × Bool :=
  embedRaw f d.val

private theorem embedGate_spec (f : Bool → Bool → Bool) (d₁ d₂ : Fin (radFn f)) (hne : d₁ ≠ d₂) :
    f (embedGate f d₁).1 (embedGate f d₂).2 ≠ f (embedGate f d₂).1 (embedGate f d₁).2 := by
  dsimp only [embedGate]
  have hne_val : d₁.val ≠ d₂.val := fun h => hne (Fin.ext h)
  have hd1 : d₁.val < radFn (tab (f false false) (f false true) (f true false) (f true true)) := by
    rw [← eq_tab f]; exact d₁.isLt
  have hd2 : d₂.val < radFn (tab (f false false) (f false true) (f true false) (f true true)) := by
    rw [← eq_tab f]; exact d₂.isLt
  have hspec := embedRaw_spec_tab (f false false) (f false true) (f true false) (f true true)
    ⟨d₁.val, hd1⟩ ⟨d₂.val, hd2⟩ (fun h => hne_val (congrArg Fin.val h))
  dsimp only at hspec
  rw [← eq_tab f] at hspec
  exact hspec

private def mkOut {n q : ℕ} (H : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n))
    (probe : Fin n → Fin n → Fin q → Bool) (S : Finset (Fin n)) (w : Fin q → Bool) : Bool :=
  if hS : S.Nonempty then
    let a := S.min' hS
    if hSa : (S.erase a).Nonempty then
      let b := (S.erase a).min' hSa
      if w = probe a b then H a (π b) else H b (π a)
    else
      H a (π a)
  else
    false

private theorem mkOut_diag {n q : ℕ} (H : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n))
    (probe : Fin n → Fin n → Fin q → Bool) (a : Fin n) (w : Fin q → Bool) :
    mkOut H π probe ({a, a} : Finset (Fin n)) w = H a (π a) := by
  dsimp only [mkOut]
  have hS : ({a, a} : Finset (Fin n)).Nonempty := ⟨a, by simp⟩
  simp only [hS, ↓reduceDIte]
  have hmin : ({a, a} : Finset (Fin n)).min' hS = a := by
    have hm := Finset.min'_mem ({a, a} : Finset (Fin n)) hS
    rcases Finset.mem_insert.mp hm with h1 | h2
    · exact h1
    · exact Finset.mem_singleton.mp h2
  have hbody : ∀ x : Fin n, x = a →
      (if hSa : (({a, a} : Finset (Fin n)).erase x).Nonempty then
        let b := (({a, a} : Finset (Fin n)).erase x).min' hSa
        if w = probe x b then H x (π b) else H b (π x)
      else H x (π x)) = H a (π a) := by
    rintro x rfl
    have he : (({x, x} : Finset (Fin n)).erase x) = ∅ := by simp
    have hnot : ¬ (({x, x} : Finset (Fin n)).erase x).Nonempty := by
      rw [he]; exact Finset.not_nonempty_empty
    simp only [hnot, ↓reduceDIte]
  exact hbody _ hmin

private theorem mkOut_pair_lt {n q : ℕ} (H : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n))
    (probe : Fin n → Fin n → Fin q → Bool) {a b : Fin n} (hlt : a < b) (w : Fin q → Bool) :
    mkOut H π probe ({a, b} : Finset (Fin n)) w =
      if w = probe a b then H a (π b) else H b (π a) := by
  have hab : a ≠ b := ne_of_lt hlt
  dsimp only [mkOut]
  have hS : ({a, b} : Finset (Fin n)).Nonempty := ⟨a, by simp⟩
  simp only [hS, ↓reduceDIte]
  have hmin : ({a, b} : Finset (Fin n)).min' hS = a := by
    have hm := Finset.min'_mem ({a, b} : Finset (Fin n)) hS
    have hle := Finset.min'_le ({a, b} : Finset (Fin n)) a (Finset.mem_insert_self a {b})
    rcases Finset.mem_insert.mp hm with h1 | h2
    · exact h1
    · rw [Finset.mem_singleton.mp h2] at hle
      exact absurd hlt (not_lt.mpr hle)
  have hbody : ∀ x : Fin n, x = a →
      (if hSa : (({a, b} : Finset (Fin n)).erase x).Nonempty then
        let y := (({a, b} : Finset (Fin n)).erase x).min' hSa
        if w = probe x y then H x (π y) else H y (π x)
      else H x (π x)) = (if w = probe a b then H a (π b) else H b (π a)) := by
    rintro x rfl
    have he : (({x, b} : Finset (Fin n)).erase x) = {b} := by
      ext y
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl⟩
        · exact absurd rfl hne
        · rfl
      · rintro rfl
        exact ⟨Ne.symm hab, Or.inr rfl⟩
    have hne : (({x, b} : Finset (Fin n)).erase x).Nonempty := by
      rw [he]; exact Finset.singleton_nonempty b
    simp only [hne, ↓reduceDIte]
    have hm := Finset.min'_mem (({x, b} : Finset (Fin n)).erase x) hne
    have hmb : (({x, b} : Finset (Fin n)).erase x).min' hne = b := by
      have h1 : (({x, b} : Finset (Fin n)).erase x).min' hne ∈ ({b} : Finset (Fin n)) := by
        simpa only [he] using hm
      exact Finset.mem_singleton.mp h1
    rw [hmb]
  exact hbody _ hmin

private theorem solve_25758 (n q : ℕ) (op : Fin q → Bool → Bool → Bool) :
    let I := Fin n
    let rad := fun (f : Bool → Bool → Bool) =>
      let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
      if ones = 0 ∨ ones = 4 then 1 else if ones = 2 then 2 else 3
    let D := ∏ t : Fin q, rad (op t)
    ∀ (H : I → I → Bool) (π : Equiv.Perm I) (e : ℕ),
      (∃ (R C : Fin q → I → Bool) (out : Finset I → (Fin q → Bool) → Bool),
        ((Finset.univ : Finset (I × I)).filter (fun z =>
          out {z.1, z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2))).card ≤ e) ↔
      ∃ label : I → Fin D,
        ((Finset.univ : Finset (I × I)).filter (fun z =>
          z.1 < z.2 ∧ label z.1 = label z.2 ∧ H z.1 (π z.2) ≠ H z.2 (π z.1))).card ≤ e := by
  intro I rad D H π e
  let equivPi : (∀ t : Fin q, Fin (radFn (op t))) ≃ Fin D :=
    Fintype.equivFinOfCardEq (by
      rw [Fintype.card_pi]
      simp only [Fintype.card_fin]
      rfl)
  constructor
  · rintro ⟨R, C, out, herr⟩
    let label : I → Fin D := fun i =>
      equivPi (fun t => colorGate (op t) (R t i, C t (π i)))
    refine ⟨label, ?_⟩
    let Err : Finset (I × I) := Finset.univ.filter (fun z =>
      out {z.1, z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2))
    let Coll : Finset (I × I) := Finset.univ.filter (fun z =>
      z.1 < z.2 ∧ label z.1 = label z.2 ∧ H z.1 (π z.2) ≠ H z.2 (π z.1))
    let φ : I × I → I × I := fun z =>
      if out {z.1, z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2) then z else (z.2, z.1)
    have hle : Coll.card ≤ Err.card := by
      apply Finset.card_le_card_of_injOn φ
      · intro z hz
        rcases (Finset.mem_filter.mp hz).2 with ⟨_, hlab, hHne⟩
        have hprobe : (fun t => op t (R t z.1) (C t (π z.2))) =
            (fun t => op t (R t z.2) (C t (π z.1))) := by
          funext t
          have hcol : colorGate (op t) (R t z.1, C t (π z.1)) =
              colorGate (op t) (R t z.2, C t (π z.2)) :=
            congrFun (equivPi.injective hlab) t
          by_contra hne
          exact colorGate_spec (op t) (R t z.1, C t (π z.1)) (R t z.2, C t (π z.2)) hne hcol
        dsimp only [φ]
        split_ifs with hcond
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcond⟩
        · push Not at hcond
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [Finset.pair_comm z.2 z.1, ← hprobe, hcond]
          exact hHne
      · intro z₁ hz₁ z₂ hz₂ heq
        have hlt1 : z₁.1 < z₁.2 := (Finset.mem_filter.mp hz₁).2.1
        have hlt2 : z₂.1 < z₂.2 := (Finset.mem_filter.mp hz₂).2.1
        have hset : ({z₁.1, z₁.2} : Finset I) = {z₂.1, z₂.2} := by
          dsimp only [φ] at heq
          split_ifs at heq
          · rw [heq]
          · have h1 := congrArg Prod.fst heq
            have h2 := congrArg Prod.snd heq
            dsimp only at h1 h2
            rw [h1, h2, Finset.pair_comm]
          · have h1 := congrArg Prod.fst heq
            have h2 := congrArg Prod.snd heq
            dsimp only at h1 h2
            rw [← h1, ← h2, Finset.pair_comm]
          · have h1 := congrArg Prod.fst heq
            have h2 := congrArg Prod.snd heq
            dsimp only at h1 h2
            rw [h1, h2]
        have hm1 : z₁.1 ∈ ({z₂.1, z₂.2} : Finset I) := by rw [← hset]; simp
        have hm2 : z₁.2 ∈ ({z₂.1, z₂.2} : Finset I) := by rw [← hset]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
        rcases hm1 with e1 | e1 <;> rcases hm2 with e2 | e2
        · rw [e1, e2] at hlt1; exact absurd hlt1 (lt_irrefl _)
        · exact Prod.ext e1 e2
        · rw [e1, e2] at hlt1; exact absurd hlt1 (lt_asymm hlt2)
        · rw [e1, e2] at hlt1; exact absurd hlt1 (lt_irrefl _)
    exact hle.trans herr
  · rintro ⟨label, hcoll⟩
    let d : I → ∀ t : Fin q, Fin (radFn (op t)) := fun i => equivPi.symm (label i)
    let R : Fin q → I → Bool := fun t i => (embedGate (op t) (d i t)).1
    let C : Fin q → I → Bool := fun t y => (embedGate (op t) (d (π.symm y) t)).2
    let probe : I → I → Fin q → Bool := fun i j t => op t (R t i) (C t (π j))
    let out : Finset I → (Fin q → Bool) → Bool := mkOut H π probe
    refine ⟨R, C, out, ?_⟩
    let Err : Finset (I × I) := Finset.univ.filter (fun z =>
      out {z.1, z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2))
    let Coll : Finset (I × I) := Finset.univ.filter (fun z =>
      z.1 < z.2 ∧ label z.1 = label z.2 ∧ H z.1 (π z.2) ≠ H z.2 (π z.1))
    have hle : Err.card ≤ Coll.card := by
      apply Finset.card_le_card_of_injOn (fun z : I × I => (z.2, z.1))
      · intro z hz
        have herr : mkOut H π probe ({z.1, z.2} : Finset I) (probe z.1 z.2) ≠ H z.1 (π z.2) :=
          (Finset.mem_filter.mp hz).2
        have hne : z.1 ≠ z.2 := by
          intro heq
          rw [heq] at herr
          exact herr (mkOut_diag H π probe z.2 (probe z.2 z.2))
        have hgt : z.2 < z.1 := by
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exfalso
            rw [mkOut_pair_lt H π probe hlt (probe z.1 z.2)] at herr
            simp only [ite_true] at herr
            exact herr rfl
          · exact hgt
        rw [Finset.pair_comm z.1 z.2, mkOut_pair_lt H π probe hgt (probe z.1 z.2)] at herr
        have hlab : label z.2 = label z.1 := by
          by_contra hlab_ne
          have hd_ne : d z.2 ≠ d z.1 := fun h => hlab_ne (equivPi.symm.injective h)
          have hex : ∃ t : Fin q, d z.2 t ≠ d z.1 t := by
            by_contra hall
            apply hd_ne
            funext t
            by_contra hne_t
            exact hall ⟨t, hne_t⟩
          rcases hex with ⟨t, ht⟩
          have hprobe_ne : probe z.1 z.2 ≠ probe z.2 z.1 := by
            intro heq
            have hval := congrFun heq t
            dsimp only [probe, R, C] at hval
            rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hval
            exact embedGate_spec (op t) (d z.2 t) (d z.1 t) ht hval.symm
          simp only [hprobe_ne, ite_false] at herr
          exact herr rfl
        have hprobe_eq : probe z.1 z.2 = probe z.2 z.1 := by
          funext t
          dsimp only [probe, R, C, d]
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hlab]
        simp only [hprobe_eq, ite_true] at herr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, hlab, herr⟩
      · intro z₁ _ z₂ _ heq
        exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    exact hle.trans hcoll

end PEqualNP.Outside.L_meta_25758_aux

theorem PEqualNP.Outside.L_meta_25758 :
∀ (n q : ℕ) (op : Fin q → Bool → Bool → Bool),
  let I := Fin n
  let rad := fun (f : Bool → Bool → Bool) =>
    let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
    if ones = 0 ∨ ones = 4 then 1 else if ones = 2 then 2 else 3
  let D := ∏ t : Fin q, rad (op t)
  ∀ (H : I → I → Bool) (π : Equiv.Perm I) (e : ℕ),
    (∃ (R C : Fin q → I → Bool) (out : Finset I → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (I × I)).filter (fun z =>
        out {z.1,z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2))).card ≤ e) ↔
    ∃ label : I → Fin D,
      ((Finset.univ : Finset (I × I)).filter (fun z =>
        z.1 < z.2 ∧ label z.1 = label z.2 ∧ H z.1 (π z.2) ≠ H z.2 (π z.1))).card ≤ e := by
  intro n q op
  exact PEqualNP.Outside.L_meta_25758_aux.solve_25758 n q op
