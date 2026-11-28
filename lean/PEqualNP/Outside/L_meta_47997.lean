import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47997

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def fullMask : Nat := 0xffffffffffffffff
abbrev Masked (mask w : Nat) : Prop := w &&& mask = w
def bsel {α : Type} (c : Bool) (t f : α) : α := Bool.rec f t c
theorem bsel_true {α : Type} (t f : α) : bsel true t f = t := rfl
theorem bsel_false {α : Type} (t f : α) : bsel false t f = f := rfl
theorem beq_false_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h
theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp
theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]
theorem xor_cancel_left (mask v : Nat) : mask ^^^ (mask ^^^ v) = v := by
  apply Nat.eq_of_testBit_eq; intro i; simp
theorem masked_sub_and {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (w &&& mask) &&& cut = w &&& cut := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and] at es ⊢
  cases hc : cut.testBit i <;> simp_all
theorem masked_sub_xor {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (mask ^^^ w) &&& cut = cut ^^^ (w &&& cut) := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at es ⊢
  cases hc : cut.testBit i <;> simp_all
def canon (mask w : Nat) : Nat :=
  let v := w &&& mask
  bsel (Nat.beq v 0 || Nat.beq v mask) 0
    (let iv := mask ^^^ v; bsel (Nat.blt v iv) v iv)
theorem canon_zero (mask : Nat) : canon mask 0 = 0 := by
  unfold canon; simp [bsel]
theorem canon_self (mask : Nat) : canon mask mask = 0 := by
  unfold canon; simp [bsel]
theorem canon_land (mask w : Nat) : canon mask (w &&& mask) = canon mask w := by
  unfold canon; dsimp only; rw [masked_land_right mask w]
theorem canon_cases (mask w : Nat) :
    (canon mask w = 0 ∧ (w &&& mask = 0 ∨ w &&& mask = mask)) ∨
    (canon mask w ≠ 0 ∧ (canon mask w = w &&& mask ∨ canon mask w = mask ^^^ (w &&& mask))) := by
  unfold canon; dsimp only
  set v := w &&& mask
  by_cases hv0 : v = 0
  · left; rw [hv0]; simp [bsel]
  · by_cases hvm : v = mask
    · left; rw [hvm]; simp [bsel]
    · right
      rw [beq_false_ne hv0, beq_false_ne hvm]
      simp only [Bool.or_false, bsel_false]
      cases hlt : Nat.blt v (mask ^^^ v)
      · rw [bsel_false]
        refine ⟨?_, Or.inr rfl⟩
        intro hz
        have e := congrArg (fun x => mask ^^^ x) hz
        rw [xor_cancel_left] at e
        exact hvm (by simpa using e)
      · rw [bsel_true]; exact ⟨hv0, Or.inl rfl⟩
theorem canon_xor_mask (mask w : Nat) : canon mask (mask ^^^ w) = canon mask w := by
  have hsub : (mask ^^^ w) &&& mask = mask ^^^ (w &&& mask) := masked_sub_xor (masked_self mask)
  unfold canon; dsimp only
  rw [hsub]
  generalize hv : w &&& mask = v
  set iv := mask ^^^ v
  have hiv : mask ^^^ iv = v := xor_cancel_left mask v
  rw [hiv]
  by_cases hv0 : v = 0
  · have hivm : iv = mask := by simp [iv, hv0]
    rw [hv0, hivm]; simp [bsel]
  · by_cases hvm : v = mask
    · have hiv0 : iv = 0 := by simp [iv, hvm]
      rw [hvm, hiv0]; simp [bsel]
    · have hiv0 : iv ≠ 0 := by
        intro h; apply hvm
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      have hivm : iv ≠ mask := by
        intro h; apply hv0
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      rw [beq_false_ne hv0, beq_false_ne hvm, beq_false_ne hiv0, beq_false_ne hivm]
      simp only [Bool.or_false, bsel_false]
      have hne : v ≠ iv := by
        intro h
        have hm0 : mask = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          have ei := congrArg (fun x => x.testBit i) h
          simp only [iv, Nat.testBit_xor] at ei
          cases hv' : v.testBit i <;> cases hm' : mask.testBit i <;> simp_all
        have : v = 0 := by rw [← hv, hm0]; simp
        exact hv0 this
      by_cases hlt : v < iv
      · have h1 : Nat.blt v iv = true := Nat.blt_eq.mpr hlt
        have h2 : Nat.blt iv v = false := by cases h : Nat.blt iv v; rfl; have := Nat.blt_eq.mp h; omega
        rw [h1, h2, bsel_true, bsel_false]
      · have hgt : iv < v := by omega
        have h1 : Nat.blt v iv = false := by cases h : Nat.blt v iv; rfl; have := Nat.blt_eq.mp h; omega
        have h2 : Nat.blt iv v = true := Nat.blt_eq.mpr hgt
        rw [h1, h2, bsel_false, bsel_true]
theorem canon_idem (mask w : Nat) : canon mask (canon mask w) = canon mask w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0, canon_zero]
  · calc canon mask (canon mask w) = canon mask (w &&& mask) := by rw [h1]
      _ = canon mask w := canon_land mask w
  · calc canon mask (canon mask w) = canon mask (mask ^^^ (w &&& mask)) := by rw [h2]
      _ = canon mask (w &&& mask) := canon_xor_mask mask (w &&& mask)
      _ = canon mask w := canon_land mask w
theorem canon_submask {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w ≠ 0) :
    canon cut (canon mask w) = canon cut w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · exact absurd h0 hc
  · rw [h1, ← canon_land cut (w &&& mask), masked_sub_and sub, canon_land]
  · rw [h2, ← canon_land cut (mask ^^^ (w &&& mask)), masked_sub_xor sub, masked_sub_and sub]
    rw [← masked_sub_xor (masked_self cut), canon_land, canon_xor_mask]
theorem canon_submask_zero {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w = 0) :
    canon cut w = 0 := by
  rcases canon_cases mask w with ⟨_, h0 | hm⟩ | ⟨hne, _⟩
  · rw [← canon_land cut w, ← masked_sub_and sub, h0]; simp [canon_zero]
  · rw [← canon_land cut w, ← masked_sub_and sub, hm, sub, canon_self]
  · exact absurd hc hne
theorem canon_testBit_eq {mask w p n : Nat} (hp : mask.testBit p = true) (hn : mask.testBit n = true) :
    ((canon mask w).testBit p = (canon mask w).testBit n) ↔ (w.testBit p = w.testBit n) := by
  rcases canon_cases mask w with ⟨h0, h1 | h2⟩ | ⟨_, h1 | h2⟩
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h1
    have e2 := congrArg (fun x => x.testBit n) h1
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h2
    have e2 := congrArg (fun x => x.testBit n) h2
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h1]; simp [Nat.testBit_and, hp, hn]
  · rw [h2]; simp [Nat.testBit_xor, Nat.testBit_and, hp, hn]
def binOp (mask op a b : Nat) : Nat :=
  bsel (Nat.beq op 0) (canon mask (a &&& b))
    (bsel (Nat.beq op 1) (canon mask (a ||| b))
      (bsel (Nat.beq op 2) (canon mask (a &&& (mask ^^^ b)))
        (canon mask ((mask ^^^ a) &&& b))))
theorem binOp_canon (mask op a b : Nat) : canon mask (binOp mask op a b) = binOp mask op a b := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false] <;> exact canon_idem mask _
theorem binOp_comm (mask op a b : Nat) (hop : op < 4) :
    ∃ op' < 4, binOp mask op a b = binOp mask op' b a := by
  have hland : a &&& b = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have hlor : a ||| b = b ||| a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]
  have h23 : a &&& (mask ^^^ b) = (mask ^^^ b) &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have h32 : (mask ^^^ a) &&& b = b &&& (mask ^^^ a) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by change canon mask (a &&& b) = canon mask (b &&& a); rw [hland]⟩
  · exact ⟨1, by omega, by change canon mask (a ||| b) = canon mask (b ||| a); rw [hlor]⟩
  · exact ⟨3, by omega, by change canon mask (a &&& (mask ^^^ b)) = canon mask ((mask ^^^ b) &&& a); rw [h23]⟩
  · exact ⟨2, by omega, by change canon mask ((mask ^^^ a) &&& b) = canon mask (b &&& (mask ^^^ a)); rw [h32]⟩
theorem binOp_zero_left (mask op b : Nat) : binOp mask op 0 b = 0 ∨ binOp mask op 0 b = canon mask b := by
  unfold binOp
  have hmb : (mask ^^^ 0) &&& b = b &&& mask := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · right; rw [hmb, canon_land]
  · left; simp [canon_zero]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
theorem binOp_zero_right (mask op a : Nat) : binOp mask op a 0 = 0 ∨ binOp mask op a 0 = canon mask a := by
  unfold binOp
  have hma : a &&& (mask ^^^ 0) = a &&& mask := by simp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; simp [canon_zero]
  · right; rw [hma, canon_land]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
theorem binOp_self (mask op a : Nat) : binOp mask op a a = 0 ∨ binOp mask op a a = canon mask a := by
  have h2 : canon mask (a &&& (mask ^^^ a)) = 0 := by
    rw [← canon_land]
    have : (a &&& (mask ^^^ a)) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  have h3 : canon mask ((mask ^^^ a) &&& a) = 0 := by
    rw [← canon_land]
    have : ((mask ^^^ a) &&& a) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; exact h3
  · left; exact h2
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
theorem deMorgan_or_mask {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  unfold Masked at ha hb
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ea eb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases hm : mask.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem canon_and_in_binOp (mask x y : Nat) :
    canon mask (x &&& y) = 0 ∨
    canon mask (x &&& y) = canon mask x ∨
    canon mask (x &&& y) = canon mask y ∨
    ∃ op < 4, canon mask (x &&& y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x &&& y) = canon mask ((x &&& mask) &&& (y &&& mask)) := by
    rw [← canon_land mask (x &&& y), ← canon_land mask ((x &&& mask) &&& (y &&& mask))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases mask.testBit i <;> rfl
  rw [hxy]
  have hvxm : Masked mask (x &&& mask) := masked_land_right mask x
  have hvym : Masked mask (y &&& mask) := masked_land_right mask y
  rcases canon_cases mask x with ⟨hx0, hx1 | hx2⟩ | ⟨_, hx1 | hx2⟩
  · left; rw [hx1]; simp [canon_zero]
  · right; right; left; rw [hx2]
    have : mask &&& (y &&& mask) = y &&& mask := by
      apply Nat.eq_of_testBit_eq; intro i
      have e := congrArg (fun t => t.testBit i) hvym
      simp only [Nat.testBit_and] at e ⊢; rw [Bool.and_comm]; exact e
    rw [this, canon_land]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨0, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& canon mask y)
      rw [hx1, hy1]
    · right; right; right; refine ⟨2, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& (mask ^^^ canon mask y))
      rw [hx1, hy2, xor_cancel_left]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨3, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask ((mask ^^^ canon mask x) &&& canon mask y)
      rw [hx2, hy1, xor_cancel_left]
    · right; right; right; refine ⟨1, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x ||| canon mask y)
      rw [hx2, hy2, ← deMorgan_or_mask hvxm hvym, canon_xor_mask]
theorem canon_or_in_binOp (mask x y : Nat) :
    canon mask (x ||| y) = 0 ∨
    canon mask (x ||| y) = canon mask x ∨
    canon mask (x ||| y) = canon mask y ∨
    ∃ op < 4, canon mask (x ||| y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x ||| y) = canon mask ((mask ^^^ x) &&& (mask ^^^ y)) := by
    rw [← canon_xor_mask mask (x ||| y), ← canon_land mask (mask ^^^ (x ||| y))]
    rw [← canon_land mask ((mask ^^^ x) &&& (mask ^^^ y))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    cases mask.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  rw [hxy]
  have h := canon_and_in_binOp mask (mask ^^^ x) (mask ^^^ y)
  rwa [canon_xor_mask, canon_xor_mask] at h
theorem canon_sub_binOp {mask cut op a b : Nat} (sub : mask &&& cut = cut) :
    canon cut (binOp mask op a b) = 0 ∨
    canon cut (binOp mask op a b) = canon cut a ∨
    canon cut (binOp mask op a b) = canon cut b ∨
    ∃ op' < 4, canon cut (binOp mask op a b) = binOp cut op' (canon cut a) (canon cut b) := by
  have go (u : Nat) : canon cut (canon mask u) = canon cut u := by
    by_cases h : canon mask u = 0
    · rw [h, canon_zero, (canon_submask_zero sub h).symm]
    · exact canon_submask sub h
  have hmx1 : canon cut ((mask ^^^ a) &&& b) = canon cut ((cut ^^^ a) &&& b) := by
    rw [← canon_land cut ((mask ^^^ a) &&& b), ← canon_land cut ((cut ^^^ a) &&& b)]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hmx2 : canon cut (a &&& (mask ^^^ b)) = canon cut (a &&& (cut ^^^ b)) := by
    rw [← canon_land cut (a &&& (mask ^^^ b)), ← canon_land cut (a &&& (cut ^^^ b))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hsub_case1 : canon cut ((cut ^^^ a) &&& b) = 0 ∨ canon cut ((cut ^^^ a) &&& b) = canon cut a ∨
      canon cut ((cut ^^^ a) &&& b) = canon cut b ∨
      ∃ op' < 4, canon cut ((cut ^^^ a) &&& b) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut (cut ^^^ a) b
    rwa [canon_xor_mask] at h
  have hsub_case2 : canon cut (a &&& (cut ^^^ b)) = 0 ∨ canon cut (a &&& (cut ^^^ b)) = canon cut a ∨
      canon cut (a &&& (cut ^^^ b)) = canon cut b ∨
      ∃ op' < 4, canon cut (a &&& (cut ^^^ b)) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut a (cut ^^^ b)
    rwa [canon_xor_mask] at h
  have hbin_eq : binOp mask op a b = canon mask (a &&& b) ∨ binOp mask op a b = canon mask (a ||| b) ∨
      binOp mask op a b = canon mask (a &&& (mask ^^^ b)) ∨ binOp mask op a b = canon mask ((mask ^^^ a) &&& b) := by
    unfold binOp
    cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp [bsel]
  rcases hbin_eq with h | h | h | h <;> rw [h, go]
  · exact canon_and_in_binOp cut a b
  · exact canon_or_in_binOp cut a b
  · rw [hmx2]; exact hsub_case2
  · rw [hmx1]; exact hsub_case1
def Avail (bank : List Nat) (w : Nat) : Prop := w = 0 ∨ w ∈ bank
def GateBin (mask : Nat) (bank : List Nat) (v : Nat) : Prop :=
  ∃ a b op, op < 4 ∧ Avail bank a ∧ Avail bank b ∧ v = binOp mask op a b
def BuildsBin (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | v :: vs => GateBin mask bank v ∧ BuildsBin mask (v :: bank) vs
def LowerBin (mask : Nat) (stock : List Nat) (goal m : Nat) : Prop :=
  ∀ vs, BuildsBin mask stock vs → Avail (vs ++ stock) goal → m ≤ vs.length
theorem avail_weaken {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {w : Nat} (h : Avail b1 w) :
    Avail b2 w := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (sub w h)
theorem gate_weaken {mask : Nat} {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {v : Nat}
    (h : GateBin mask b1 v) : GateBin mask b2 v := by
  obtain ⟨a, b, op, hop, ha, hb, hv⟩ := h
  exact ⟨a, b, op, hop, avail_weaken sub ha, avail_weaken sub hb, hv⟩
theorem builds_weaken {mask : Nat} {b1 b2 vs : List Nat} (sub : ∀ w ∈ b1, w ∈ b2)
    (h : BuildsBin mask b1 vs) : BuildsBin mask b2 vs := by
  induction vs generalizing b1 b2 with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gate_weaken sub h.1, ih ?_ h.2⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub w hw)
theorem builds_append {mask : Nat} {roots first second : List Nat}
    (h1 : BuildsBin mask roots first) (h2 : BuildsBin mask (first ++ roots) second) :
    BuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact h2
  | cons v vs ih =>
    refine ⟨h1.1, ih h1.2 ?_⟩
    exact builds_weaken (fun w hw => by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto) h2
def dropIf (drop : Bool) (x : Nat) (S : Finset Nat) : Finset Nat :=
  if drop then S.erase x else S
theorem dropIf_subset (drop : Bool) (x : Nat) (S : Finset Nat) : dropIf drop x S ⊆ S := by
  unfold dropIf; split; exact Finset.erase_subset _ _; exact Finset.Subset.refl _
theorem dropIf_card_le (drop : Bool) (x : Nat) (S : Finset Nat) :
    S.card ≤ (dropIf drop x S).card + 1 := by
  unfold dropIf; split
  · by_cases hx : x ∈ S
    · have := Finset.card_erase_add_one hx; omega
    · rw [Finset.erase_eq_of_notMem hx]; omega
  · omega
inductive LiveBin (mask goal : Nat) : Nat → Finset Nat → Prop
  | done : LiveBin mask goal 0 {goal}
  | step {k : Nat} {S : Finset Nat} {a b op : Nat}
      (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hop : op < 4)
      (hz : binOp mask op a b ≠ 0) (hf : binOp mask op a b ∉ S)
      (keepA keepB : Bool) :
      LiveBin mask goal k (insert (binOp mask op a b) (dropIf (!keepA) a (dropIf (!keepB) b S))) →
      LiveBin mask goal (k + 1) S
theorem liveBin_zero_not_mem {mask goal k : Nat} {S : Finset Nat} (hg : goal ≠ 0)
    (h : LiveBin mask goal k S) : 0 ∉ S := by
  induction h with
  | done => simp [hg.symm]
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    intro h0; apply ih
    apply Finset.mem_insert_of_mem
    unfold dropIf
    split
    · apply Finset.mem_erase.mpr; refine ⟨ha0.symm, ?_⟩
      split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
    · split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
theorem liveBin_card_le {mask goal k : Nat} {S : Finset Nat} (h : LiveBin mask goal k S) :
    S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    set z := binOp mask op a b
    have h1 := dropIf_card_le (!keepB) b S
    have h2 := dropIf_card_le (!keepA) a (dropIf (!keepB) b S)
    have hz' : z ∉ dropIf (!keepA) a (dropIf (!keepB) b S) := fun hm =>
      hf (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm))
    have h3 : (insert z (dropIf (!keepA) a (dropIf (!keepB) b S))).card =
        (dropIf (!keepA) a (dropIf (!keepB) b S)).card + 1 := Finset.card_insert_of_notMem hz'
    omega
theorem extractLiveBin_aux {mask goal : Nat} (hg : goal ≠ 0) :
    ∀ (vs bank : List Nat) (k : Nat) (L : Finset Nat),
      BuildsBin mask bank vs → (∀ w ∈ bank, canon mask w = w) →
      L ⊆ (vs ++ bank).toFinset → LiveBin mask goal k L →
      ∃ k' S, k' ≤ k + vs.length ∧ S ⊆ bank.toFinset ∧ LiveBin mask goal k' S
  | [], bank, k, L, _, _, hsub, hlive => ⟨k, L, by simp, hsub, hlive⟩
  | v :: vs, bank, k, L, hbuild, hcb, hsub, hlive => by
    have hcv : canon mask v = v := by
      obtain ⟨a, b, op, _, _, _, rfl⟩ := hbuild.1; exact binOp_canon mask op a b
    have hcb' : ∀ w ∈ v :: bank, canon mask w = w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hcv; exact hcb w hw
    have hsub' : L ⊆ (vs ++ (v :: bank)).toFinset := by
      intro w hw
      have := hsub hw
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto
    obtain ⟨k1, L1, hk1, hL1sub, hlive1⟩ := extractLiveBin_aux hg vs (v :: bank) k L hbuild.2 hcb' hsub' hlive
    by_cases hv : v ∈ L1 ∧ v ∉ bank
    · obtain ⟨hvL, hvb⟩ := hv
      have hv0 : v ≠ 0 := fun h0 => liveBin_zero_not_mem hg hlive1 (h0 ▸ hvL)
      obtain ⟨a, b, op, hop, haA, hbA, hvEq⟩ := hbuild.1
      have ha0 : a ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_left mask op b with h | h
        · exact hv0 (hvEq.trans h)
        · rcases hbA with rfl | hbM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb b hbM] at h; exact hvb ((hvEq.trans h) ▸ hbM)
      have hb0 : b ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_right mask op a with h | h
        · exact hv0 (hvEq.trans h)
        · rcases haA with rfl | haM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb a haM] at h; exact hvb ((hvEq.trans h) ▸ haM)
      have haM : a ∈ bank := haA.resolve_left ha0
      have hbM : b ∈ bank := hbA.resolve_left hb0
      have hab : a ≠ b := by
        intro h; subst h
        rcases binOp_self mask op a with h0 | ha'
        · exact hv0 (hvEq.trans h0)
        · rw [hcb a haM] at ha'; exact hvb ((hvEq.trans ha') ▸ haM)
      set R := L1.erase v
      set S := insert a (insert b R)
      have hSsub : S ⊆ bank.toFinset := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact List.mem_toFinset.mpr haM
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact List.mem_toFinset.mpr hbM
          · have h1 := hL1sub (Finset.mem_of_mem_erase hw)
            simp only [List.toFinset_cons, Finset.mem_insert] at h1
            exact h1.resolve_left (Finset.ne_of_mem_erase hw)
      have hvNotS : v ∉ S := by
        intro hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hvb haM
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hvb hbM
          · exact (Finset.notMem_erase v L1) hm
      have hL1eq : insert v (dropIf (!(decide (a ∈ R))) a (dropIf (!(decide (b ∈ R))) b S)) = L1 := by
        ext w
        by_cases haR : a ∈ R <;> by_cases hbR : b ∈ R
        · simp only [haR, hbR, decide_true, Bool.not_true, Bool.false_eq_true, dropIf, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | rfl | rfl | ⟨_, hw⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h; exact Or.inr (Or.inr (Or.inr ⟨h, hw⟩))
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_false, Bool.not_false, dropIf, ite_true, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, ?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            · intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
            · intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
      refine ⟨k1 + 1, S, by simp only [List.length_cons]; omega, hSsub, ?_⟩
      apply LiveBin.step (a := a) (b := b) (op := op)
        (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
        hab ha0 hb0 hop (hvEq ▸ hv0) (hvEq ▸ hvNotS) (decide (a ∈ R)) (decide (b ∈ R))
      rw [← hvEq, hL1eq]; exact hlive1
    · refine ⟨k1, L1, by simp only [List.length_cons]; omega, ?_, hlive1⟩
      intro w hw
      have h1 := hL1sub hw
      simp only [List.toFinset_cons, Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · have hvb : w ∈ bank := by by_contra hnb; exact hv ⟨hw, hnb⟩
        exact List.mem_toFinset.mpr hvb
      · exact h1
theorem extractLiveBin {mask goal : Nat} {stock vs : List Nat}
    (hg : goal ≠ 0) (hcs : ∀ w ∈ stock, canon mask w = w)
    (hbuild : BuildsBin mask stock vs) (hhit : Avail (vs ++ stock) goal) :
    ∃ k S, k ≤ vs.length ∧ S ⊆ stock.toFinset ∧ LiveBin mask goal k S := by
  have hmem : goal ∈ vs ++ stock := hhit.resolve_left hg
  have hsub : ({goal} : Finset Nat) ⊆ (vs ++ stock).toFinset := by
    intro w hw; rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hmem
  obtain ⟨k, S, hk, hS, hL⟩ := extractLiveBin_aux hg vs stock 0 {goal} hbuild hcs hsub LiveBin.done
  exact ⟨k, S, by omega, hS, hL⟩
theorem liveBin_agrees {mask goal k p n : Nat} {S : Finset Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (h : LiveBin mask goal k S) (hag : ∀ w ∈ S, w.testBit p = w.testBit n) :
    goal.testBit p = goal.testBit n := by
  induction h with
  | done => exact hag goal (Finset.mem_singleton_self goal)
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    apply ih; intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ea := hag a ha
      have eb := hag b hb
      unfold binOp
      cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
      all_goals rw [canon_testBit_eq hp hn]
      all_goals simp [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn, ea, eb]
    · exact hag w (dropIf_subset _ _ _ (dropIf_subset _ _ _ hw))
def forceW {α : Type} (w : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) w
theorem forceW_eq {α : Type} (w : Nat) (k : Nat → α) : forceW w k = k w := by
  cases w <;> rfl
def forceWs (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => forceW w (fun v => next (fun rest => k (v :: rest)))) ws) k
theorem forceWs_eq (ws : List Nat) (k : List Nat → Bool) : forceWs ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW w (fun v => forceWs ws (fun rest => k (v :: rest))) = _
    rw [forceW_eq, ih]
def dagPart (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      (Nat.beq p 0 || Nat.beq n 0) ||
        forceW (p &&& w) (fun up =>
          forceW (n &&& w) (fun down =>
            rest up down &&
              forceW (p ^^^ up) (fun offP =>
                forceW (n ^^^ down) (rest offP))))) ws
theorem offBits {v w i : Nat} (h : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at h
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at h ⊢
theorem dagPart_sound {ws : List Nat} {pos neg : Nat} (fail : dagPart ws pos neg = false) :
    ∃ p n, pos.testBit p = true ∧ neg.testBit n = true ∧ ∀ w ∈ ws, w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all; apply hn; apply Nat.eq_of_testBit_eq; intro i; simp [all i]
  induction ws generalizing pos neg with
  | nil =>
    change (Nat.beq pos 0 || Nat.beq neg 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p, hp⟩ := nonempty (ne_of_beq_false fail.1)
    obtain ⟨n, hn⟩ := nonempty (ne_of_beq_false fail.2)
    exact ⟨p, n, hp, hn, by simp⟩
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up =>
        forceW (neg &&& w) (fun down =>
          dagPart ws up down &&
            forceW (pos ^^^ up) (fun offP =>
              forceW (neg ^^^ down) (dagPart ws offP))))) = false at fail
    simp only [forceW_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p, n, hp, hn, ag⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p, n, hp.1, hn.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp.2, hn.2]
      · exact ag a ha
    · obtain ⟨p, n, hp, hn, ag⟩ := ih off
      have hp' := offBits hp
      have hn' := offBits hn
      refine ⟨p, n, hp'.1, hn'.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp'.2, hn'.2]
      · exact ag a ha
theorem dagPart_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    dagPart ws goal (mask ^^^ goal) = true := by
  by_contra hf
  have hfalse : dagPart ws goal (mask ^^^ goal) = false := by
    cases h : dagPart ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, ag⟩ := dagPart_sound hfalse
  have hpm : mask.testBit p = true := by
    have e := congrArg (fun x => x.testBit p) hgm
    simp only [Nat.testBit_and, hp, Bool.true_and] at e; exact e
  have hnm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have imp : goal.testBit n = true → mask.testBit n = true := by
      intro hg
      have e := congrArg (fun x => x.testBit n) hgm
      simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
    cases hm : mask.testBit n <;> cases hg : goal.testBit n <;> simp_all
  have eq := liveBin_agrees hpm hnm.1 hlive (fun w hw => ag w (List.mem_toFinset.mp hw))
  rw [hp, hnm.2] at eq; exact Bool.noConfusion eq
def flatSet (cut : Nat) (S : Finset Nat) : Finset Nat :=
  S.filter (fun w => Nat.beq (canon cut w) 0)
theorem flatSet_insert_notMem {cut w : Nat} {S : Finset Nat} (hw : w ∉ S) :
    (flatSet cut (insert w S)).card =
      if canon cut w = 0 then (flatSet cut S).card + 1 else (flatSet cut S).card := by
  unfold flatSet
  rw [Finset.filter_insert]
  by_cases hc : canon cut w = 0
  · simp only [hc, Nat.beq_refl, ite_true]
    exact Finset.card_insert_of_notMem (fun h => hw (Finset.mem_filter.mp h).1)
  · simp only [beq_false_ne hc, Bool.false_eq_true, ite_false, hc]
theorem flatSet_erase {cut w : Nat} {S : Finset Nat} :
    (flatSet cut S).card ≤ (flatSet cut (S.erase w)).card + (if canon cut w = 0 then 1 else 0) := by
  unfold flatSet
  rw [Finset.filter_erase]
  by_cases hm : w ∈ S.filter (fun x => Nat.beq (canon cut x) 0)
  · have hcw : canon cut w = 0 := Nat.eq_of_beq_eq_true (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_erase_add_one hm
    simp only [hcw, ite_true]; omega
  · rw [Finset.erase_eq_of_notMem hm]; omega
theorem maskedBuildBin {mask cut goal k : Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) (hgnf : canon cut goal ≠ 0)
    (h : LiveBin mask goal k S) :
    ∀ (bank : List Nat), (∀ w ∈ S, Avail bank (canon cut w)) →
      ∃ vs, vs.length + (flatSet cut S).card ≤ k ∧ BuildsBin cut bank vs ∧
        Avail (vs ++ bank) (canon cut goal) := by
  induction h with
  | done =>
    intro bank hsup
    have hfl : (flatSet cut {goal}).card = 0 := by
      unfold flatSet
      simp [hgnf]
    exact ⟨[], by simp [hfl], trivial, hsup goal (Finset.mem_singleton_self goal)⟩
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    intro bank hsup
    set z := binOp mask op a b
    set S1 := dropIf (!keepB) b S
    set S2 := dropIf (!keepA) a S1
    set S' := insert z S2
    have hS2sub : S2 ⊆ S := Finset.Subset.trans (dropIf_subset _ _ _) (dropIf_subset _ _ _)
    have hzNotS2 : z ∉ S2 := fun hm => hf (hS2sub hm)
    have hfl1 : (flatSet cut S).card ≤ (flatSet cut S1).card + (if canon cut b = 0 then 1 else 0) := by
      unfold S1 dropIf; split; exact flatSet_erase; omega
    have hfl2 : (flatSet cut S1).card ≤ (flatSet cut S2).card + (if canon cut a = 0 then 1 else 0) := by
      unfold S2 dropIf; split; exact flatSet_erase; omega
    have hfl3 : (flatSet cut S').card =
        if canon cut z = 0 then (flatSet cut S2).card + 1 else (flatSet cut S2).card :=
      flatSet_insert_notMem hzNotS2
    have hcz : canon cut z = 0 ∨ canon cut z = canon cut a ∨ canon cut z = canon cut b ∨
        ∃ op' < 4, canon cut z = binOp cut op' (canon cut a) (canon cut b) :=
      canon_sub_binOp sub
    by_cases hfa : canon cut a = 0
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact h
          · exact h.trans hfa
          · exact h.trans hfb
          · rw [hfa, hfb] at h
            rcases binOp_zero_left cut op' 0 with h0 | h0
            · exact h.trans h0
            · exact h.trans (h0.trans (canon_zero cut))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Or.inl hfz
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, hfz, ite_true] at hfl1 hfl2 hfl3
        exact ⟨vs, by omega, hbd, hhit⟩
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut b := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hfa)
          · exact Or.inr h
          · rw [hfa] at h
            rcases binOp_zero_left cut op' (canon cut b) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut b)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | hb'
            · exact Or.inl h0
            · rw [hb']; exact hsup b hb
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut a := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans hfb)
          · rw [hfb] at h
            rcases binOp_zero_right cut op' (canon cut a) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut a)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | ha'
            · exact Or.inl h0
            · rw [ha']; exact hsup a ha
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
      · simp only [hfa, hfb, ite_false] at hfl1 hfl2
        have hfl_le : (flatSet cut S).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        rcases hcz with h0 | ha' | hb' | ⟨op', hop', hbin⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inl h0
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [ha']; exact hsup a ha
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [hb']; exact hsup b hb
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · set cz := canon cut z
          have hgate : GateBin cut bank cz := ⟨canon cut a, canon cut b, op', hop', hsup a ha, hsup b hb, hbin⟩
          have hsup' : ∀ w ∈ S', Avail (cz :: bank) (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inr List.mem_cons_self
            · exact avail_weaken (fun u hu => List.mem_cons_of_mem _ hu) (hsup w (hS2sub hw))
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih (cz :: bank) hsup'
          refine ⟨cz :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbd⟩, ?_⟩
          exact avail_weaken (fun u hu => by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto) hhit
def flatCount (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt => bsel (Nat.beq (canon cut w) 0) (cnt + 1) cnt) ws
theorem flatCount_card (cut : Nat) {ws : List Nat} (nd : ws.Nodup) :
    flatCount cut ws = (flatSet cut ws.toFinset).card := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hnd := List.nodup_cons.mp nd
    have fresh : w ∉ ws.toFinset := by simpa using hnd.1
    change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
    rw [List.toFinset_cons, flatSet_insert_notMem fresh, ih hnd.2]
    by_cases hc : canon cut w = 0
    · simp [hc, bsel]
    · rw [beq_false_ne hc, bsel_false]; simp [hc]
def availB (bank : List Nat) (w : Nat) : Bool :=
  Nat.beq w 0 || bank.contains w
theorem availB_spec {bank : List Nat} {w : Nat} : availB bank w = true ↔ Avail bank w := by
  unfold availB Avail; simp [Nat.beq_eq]
def addUniq (w : Nat) (l : List Nat) : List Nat :=
  if l.contains w then l else w :: l
def recipeStart (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canon cut w
    if availB stock v then acc else addUniq v acc) ws
def recipeClose (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canon cut w
      if acc.contains v then
        let va := canon cut a
        let vb := canon cut b
        let acc1 := if availB stock va then acc else addUniq va acc
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        next acc2
      else next acc) hist needed
def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1
def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => bsel (Nat.ble x y) (x :: y :: ys) (y :: ih)) l
theorem insertSorted_mem {x w : Nat} {l : List Nat} :
    w ∈ insertSorted x l ↔ w = x ∨ w ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    change w ∈ bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys) ↔ _
    cases Nat.ble x y
    · rw [bsel_false]; simp only [List.mem_cons, ih]; tauto
    · rw [bsel_true]; simp only [List.mem_cons]
theorem insertSorted_nodup {x : Nat} {l : List Nat} (hx : x ∉ l) (nd : l.Nodup) :
    (insertSorted x l).Nodup := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    have hnd := List.nodup_cons.mp nd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxs : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change (bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)).Nodup
    cases Nat.ble x y
    · rw [bsel_false]
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_, ih hxs hnd.2⟩
      rcases insertSorted_mem.mp hm with h | h
      · exact hxy h.symm
      · exact hnd.1 h
    · rw [bsel_true]; exact List.nodup_cons.mpr ⟨hx, nd⟩
def dropVal (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  bsel drop (List.rec [] (fun y _ ih => bsel (Nat.beq y x) ih (y :: ih)) l) l
theorem dropVal_mem {drop : Bool} {x w : Nat} {l : List Nat} :
    w ∈ dropVal drop x l ↔ w ∈ l ∧ (drop = true → w ≠ x) := by
  cases drop
  · simp [dropVal, bsel]
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      change w ∈ bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys) ↔ _
      cases hb : Nat.beq y x
      · rw [bsel_false]
        have hne : y ≠ x := ne_of_beq_false hb
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro (rfl | ⟨hw, hwx⟩); exact ⟨Or.inl rfl, hne⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hwx⟩
      · rw [bsel_true]
        have heq : y = x := Nat.eq_of_beq_eq_true hb
        subst heq
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro ⟨hw, hwx⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact absurd rfl hwx; exact ⟨hw, hwx⟩
theorem dropVal_nodup {drop : Bool} {x : Nat} {l : List Nat} (nd : l.Nodup) :
    (dropVal drop x l).Nodup := by
  cases drop
  · exact nd
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      have hnd := List.nodup_cons.mp nd
      change (bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)).Nodup
      cases Nat.beq y x
      · rw [bsel_false]
        exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (dropVal_mem.mp hm).1, ih hnd.2⟩
      · rw [bsel_true]; exact ih hnd.2
theorem dropVal_toFinset (drop : Bool) (x : Nat) (l : List Nat) :
    (dropVal drop x l).toFinset = dropIf drop x l.toFinset := by
  ext w; simp only [List.mem_toFinset, dropVal_mem, dropIf]
  cases drop <;> simp [Finset.mem_erase, and_comm]
def subsetWords (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (b >>> 1)
      bsel (Nat.beq (b &&& 1) 1) (insertSorted w rest) rest) stock) bits
theorem subsetWords_subset (stock : List Nat) (bits : Nat) :
    ∀ w ∈ subsetWords stock bits, w ∈ stock := by
  induction stock generalizing bits with
  | nil => intro w hw; simp [subsetWords] at hw
  | cons x xs ih =>
    intro w hw
    change w ∈ bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1)) at hw
    cases hb : Nat.beq (bits &&& 1) 1
    · rw [hb, bsel_false] at hw; exact List.mem_cons_of_mem _ (ih _ w hw)
    · rw [hb, bsel_true] at hw
      rcases insertSorted_mem.mp hw with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ w hm)
theorem subsetWords_nodup {stock : List Nat} (nd : stock.Nodup) (bits : Nat) :
    (subsetWords stock bits).Nodup := by
  induction stock generalizing bits with
  | nil => simp [subsetWords]
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp nd
    change (bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))).Nodup
    cases Nat.beq (bits &&& 1) 1
    · rw [bsel_false]; exact ih hnd.2 _
    · rw [bsel_true]; exact insertSorted_nodup (fun hm => hnd.1 (subsetWords_subset xs _ x hm)) (ih hnd.2 _)
theorem exists_subsetToken (stock : List Nat) (S : Finset Nat) :
    ∃ bits < 2 ^ stock.length, (subsetWords stock bits).toFinset = S ∩ stock.toFinset := by
  induction stock with
  | nil => exact ⟨0, by simp, by simp [subsetWords]⟩
  | cons x xs ih =>
    obtain ⟨b, hb, heq⟩ := ih
    by_cases hx : x ∈ S
    · refine ⟨2 * b + 1, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b + 1) >>> 1 = b := by change (2 * b + 1) / 2 = b; omega
      have hmod : ((2 * b + 1) &&& 1) = 1 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b + 1) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b + 1) >>> 1)))
        (subsetWords xs ((2 * b + 1) >>> 1))).toFinset = _
      rw [hdiv, hmod, Nat.beq_refl, bsel_true]
      ext w; simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro (rfl | ⟨hs, hxs⟩); exact ⟨hx, Or.inl rfl⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact Or.inl rfl; exact Or.inr ⟨hs, hxs⟩
    · refine ⟨2 * b, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b) >>> 1 = b := by change (2 * b) / 2 = b; omega
      have hmod : ((2 * b) &&& 1) = 0 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b) >>> 1)))
        (subsetWords xs ((2 * b) >>> 1))).toFinset = _
      rw [hdiv, hmod]
      change (subsetWords xs b).toFinset = _
      ext w; simp only [List.mem_toFinset, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro ⟨hs, hxs⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact absurd hs hx; exact ⟨hs, hxs⟩
def rootState (stock : List Nat) (fuel token : Nat) : Nat × List Nat × List (Nat × Nat × Nat) :=
  (fuel, subsetWords stock token, [])
def childState (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := token &&& 3
  let op := (token >>> 2) &&& 3
  let b := (token >>> 4) &&& 15
  let a := token >>> 8
  if Nat.beq fuel 0 || !(Nat.blt a b) || !(Nat.blt b ws.length) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    if Nat.beq z 0 || ws.contains z then none
    else
      let keepA := Nat.beq (keep &&& 1) 1
      let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
      let rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
      some (fuel - 1, insertSorted z rest, (z, x, y) :: hist)
theorem childState_wf {mask token : Nat} {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (nd : st.2.1.Nodup) (h : childState mask token st = some ch) :
    ch.1 < st.1 ∧ ch.2.1.Nodup := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at nd
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · rename_i hfresh
      have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok hfresh
      have hfpos : fuel ≠ 0 := fun hf => hok (Or.inl (Or.inl hf))
      have hznot : ¬(ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0)
          (ws.getD ((token >>> 4) &&& 15) 0)) = true) := fun hm => hfresh (Or.inr hm)
      refine ⟨by dsimp; omega, ?_⟩
      apply insertSorted_nodup
      · intro hm
        have hmem := (dropVal_mem.mp (dropVal_mem.mp hm).1).1
        exact hznot (List.contains_iff_mem.mpr hmem)
      · exact dropVal_nodup (dropVal_nodup nd)
def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then
        if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
      else (prev (parent - 1)).bind (childState mask token)) (fuel + 1)) i
theorem dagTrace_nodup {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    (nd : stock.Nodup) {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) : st.2.1.Nodup := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s → s.2.1.Nodup from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s; exact subsetWords_nodup nd _
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p => rw [hp] at h; exact (childState_wf (ih _ _ hp) h).2
def treeBlock (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      if Nat.blt a b then
        let m := (a + b) / 2
        if Nat.beq a m then f a else next a m && next m b
      else true) (hi - lo + 1)) lo hi
theorem treeBlock_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlock lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  unfold treeBlock at h
  suffices ∀ steps a b, b - a ≤ steps →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      ∀ i, a ≤ i → i < b → f i = true by
    intro i h1 h2; exact this (hi - lo + 1) lo hi (by omega) h i h1 h2
  intro steps
  induction steps with
  | zero => intro a b hba _ i h1 h2; omega
  | succ s ih =>
    intro a b hba h i h1 h2
    dsimp only at h
    have hab : Nat.blt a b = true := Nat.blt_eq.mpr (by omega)
    simp only [hab, ite_true] at h
    set m := (a + b) / 2
    by_cases ham : a = m
    · have hbm : Nat.beq a m = true := Nat.beq_eq.mpr ham
      simp only [hbm, ite_true] at h
      have hia : i = a := by omega
      subst hia; exact h
    · have hbm : Nat.beq a m = false := beq_false_ne ham
      simp only [hbm, Bool.false_eq_true, ite_false] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hl, hr⟩
      by_cases him : i < m
      · exact ih a m (by omega) hl i h1 him
      · exact ih m b (by omega) hr i (by omega) h2
theorem block_join {a m b : Nat} {f : Nat → Bool}
    (h1 : ∀ i, a ≤ i → i < m → f i = true)
    (h2 : ∀ i, m ≤ i → i < b → f i = true) :
    ∀ i, a ≤ i → i < b → f i = true := by
  intro i hi1 hi2
  by_cases h : i < m
  · exact h1 i hi1 h
  · exact h2 i (by omega) hi2
theorem getElem_index_lt {l : List Nat} {x : Nat} (hx : x ∈ l) :
    ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, heq]
theorem list_len_child {x y z : Nat} {ws : List Nat} {keepA keepB : Bool}
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) (hz : z ∉ ws) :
    (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).length =
      ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) := by
  have nd' : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).Nodup :=
    insertSorted_nodup (fun hm => hz (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
  have h1 := List.toFinset_card_of_nodup nd'
  have h2 := List.toFinset_card_of_nodup nd
  have hset : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).toFinset =
      insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
    ext w
    simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
  rw [hset] at h1
  have hz' : z ∉ dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset) :=
    fun hm => hz (List.mem_toFinset.mp (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm)))
  rw [Finset.card_insert_of_notMem hz'] at h1
  set T := dropIf (!keepB) y ws.toFinset
  have hxb : x ∈ T := by
    unfold T dropIf; split
    · exact Finset.mem_erase.mpr ⟨hxy, List.mem_toFinset.mpr hx⟩
    · exact List.mem_toFinset.mpr hx
  have hcb : T.card = ws.toFinset.card - (if keepB then 0 else 1) := by
    unfold T dropIf; cases keepB
    · have := Finset.card_erase_add_one (List.mem_toFinset.mpr hy); simp; omega
    · simp
  have hca : (dropIf (!keepA) x T).card = T.card - (if keepA then 0 else 1) := by
    unfold dropIf; cases keepA
    · have := Finset.card_erase_add_one hxb; simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; omega
    · simp
  have hlen2 : 2 ≤ ws.toFinset.card := by
    have hsub : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact List.mem_toFinset.mpr hx
      · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hy
    have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub; omega
  rw [← h1, hca, hcb, h2]
  cases keepA <;> cases keepB <;> simp <;> omega
def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) : Nat := (gs.filter isBinary).length
def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def evalBit (k : Nat) (w : Nat) : Bool := w.testBit k
def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def actionWord (w : List Nat) (g : Gate) : Nat := match g.op with
  | .not => fullMask ^^^ ((g.inputs.head?.map (fun i => w.getD i 0)).getD 0)
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) fullMask
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0
theorem fullMask_eq : fullMask = 2 ^ 64 - 1 := by decide
theorem fullMask_bit {k : Nat} (hk : k < 64) : fullMask.testBit k = true := by
  rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
theorem readBit (w : List Nat) (i k : Nat) :
    (w.map (evalBit k)).getD i false = evalBit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), evalBit]
theorem actionWord_spec (w : List Nat) (g : Gate) (hg : legal g) {k : Nat} (hk : k < 64) :
    stepBool (w.map (evalBit k)) g = (w ++ [actionWord w g]).map (evalBit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hcap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hcap
  have hfm := fullMask_bit hk
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [stepBool, List.map_cons, List.map_nil, readBit, List.map_append, actionWord,
      GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, evalBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, hfm, Bool.true_xor]
def rawVars : List Nat :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]
theorem rawVars_avail : ∀ u ∈ rawVars, Avail rootStock (canon fullMask u) := by
  intro u hu
  simp only [rawVars, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide)
theorem compileBin_aux (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w bank : List Nat)
    (hw : ∀ u ∈ w, Avail bank (canon fullMask u)) :
    ∃ vs, vs.length ≤ binaryCost gs ∧ BuildsBin fullMask bank vs ∧
      ∀ u ∈ gs.foldl (fun acc g => acc ++ [actionWord acc g]) w, Avail (vs ++ bank) (canon fullMask u) := by
  induction gs generalizing w bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, by simpa using hw⟩
  | cons g gs ih =>
    have hg0 := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    set z := actionWord w g
    have hread (i : Nat) : Avail bank (canon fullMask (w.getD i 0)) := by
      by_cases hi : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hstep : Avail bank (canon fullMask z) ∨ (isBinary g = true ∧ GateBin fullMask bank (canon fullMask z)) := by
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hcap⟩ := hg0
      change op = .and ∨ op = .or ∨ op = .not at hop
      change args.length ≤ 2 at hcap
      rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
      · rcases hop with rfl | rfl | rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_zero]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
      · rcases hop with rfl | rfl | rfl
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [canon_land]; exact hread i
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          exact hread i
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
      · rcases hop with rfl | rfl | rfl
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          have h1 : canon fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask)) =
              canon fullMask (w.getD i 0 &&& w.getD j 0) := by
            rw [← canon_land fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask))]
            rw [← canon_land fullMask (w.getD i 0 &&& w.getD j 0)]
            congr 1; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_and]
            cases (w.getD i 0).testBit k <;> cases (w.getD j 0).testBit k <;> cases fullMask.testBit k <;> rfl
          rw [h1]
          rcases canon_and_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          rcases canon_or_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
    rcases hstep with hav | ⟨hbin, hgate⟩
    · have hw' : ∀ u ∈ w ++ [z], Avail bank (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hw u hu
        · rw [List.mem_singleton.mp hu]; exact hav
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) bank hw'
      have hbc : binaryCost gs ≤ binaryCost (g :: gs) := by
        unfold binaryCost; simp only [List.filter]; cases isBinary g <;> simp
      exact ⟨vs, Nat.le_trans hlen hbc, hbd, hall⟩
    · set cz := canon fullMask z
      have hw' : ∀ u ∈ w ++ [z], Avail (cz :: bank) (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact avail_weaken (fun a ha => List.mem_cons_of_mem _ ha) (hw u hu)
        · rw [List.mem_singleton.mp hu]; exact Or.inr List.mem_cons_self
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) (cz :: bank) hw'
      have hbc : binaryCost (g :: gs) = binaryCost gs + 1 := by
        unfold binaryCost; simp [hbin]
      refine ⟨cz :: vs, by simp only [List.length_cons, hbc]; omega, ⟨hgate, hbd⟩, ?_⟩
      intro u hu
      exact avail_weaken (fun a ha => by simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto) (hall u hu)
theorem foldl_evalBit (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List Nat) {k : Nat} (hk : k < 64) :
    gs.foldl stepBool (w.map (evalBit k)) =
      (gs.foldl (fun acc g => acc ++ [actionWord acc g]) w).map (evalBit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [actionWord_spec w g (hg g List.mem_cons_self) hk]
    exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (w ++ [actionWord w g])
theorem rawVars_ofFn (x : Fin 6 → Bool) :
    List.ofFn x = rawVars.map (evalBit (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) := by
  have hx : ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      [b0, b1, b2, b3, b4, b5] =
      rawVars.map (evalBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))) := by
    decide +kernel
  have hsum : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) =
      (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
      (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) := by
    simp [Fin.sum_univ_six]
  rw [hsum, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
theorem sum_bits_6 (n : Nat) (hn : n < 64) :
    (∑ i : Fin 6, if n.testBit i.val then 2 ^ (i : Nat) else 0) = n := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  change (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) + (if n.testBit 3 then 8 else 0) +
    (if n.testBit 4 then 16 else 0) + (if n.testBit 5 then 32 else 0) = n
  revert n; decide +kernel
theorem table2_from_lowerBin (target m : Nat)
    (hlow : LowerBin fullMask rootStock (canon fullMask target) (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) := by
  intro s ⟨C, hfan, hsize, hC⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hgm, hgop⟩ := hasNot
    have hshort : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hgm, by simp [isBinary, hgop]⟩
    have hleg : ∀ g ∈ C.gates, legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    obtain ⟨vs, hvlen, hvbd, hvhit⟩ := compileBin_aux C.gates hleg rawVars rootStock rawVars_avail
    set finalW := C.gates.foldl (fun acc g => acc ++ [actionWord acc g]) rawVars
    have hout_eq : finalW.getD C.output 0 &&& fullMask = target &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let x : Fin 6 → Bool := fun i => k.testBit i.val
        have hxidx : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) = k := sum_bits_6 k hk
        have h1 := hC x
        dsimp only at h1
        rw [hxidx, rawVars_ofFn x, hxidx] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = target.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) (canon fullMask target) := by
      rw [← canon_land fullMask target, ← hout_eq, canon_land]
      by_cases hi : C.output < finalW.length
      · exact hvhit _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hge := hlow vs hvbd hout_avail
    have hcsz : C.size = C.gates.length := rfl
    have hwsz : (⟨wg, wout⟩ : Circuit).size = m := hsz
    exact ⟨⟨wg, wout⟩, hmono, by omega, heval⟩
  · refine ⟨C, ?_, hsize, hC⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
def memN (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l
theorem memN_eq (z : Nat) (l : List Nat) : memN z l = l.contains z := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  induction l with
  | nil => simp [memN]
  | cons w ws ih =>
    change Bool.rec (memN z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := ne_of_beq_false h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]
def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l
theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]
def getDN (l : List Nat) (i : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih k => Nat.rec w (fun m _ => ih m) k) l) i
theorem getDN_eq (l : List Nat) (i : Nat) : getDN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ m => change getDN ws m = (w :: ws).getD (m + 1) 0; rw [ih]; rfl
def eqListN (l1 : List Nat) : List Nat → Bool :=
  List.rec
    (fun l2 => List.rec true (fun _ _ _ => false) l2)
    (fun x _ ih l2 => List.rec false (fun y ys _ => Bool.rec false (ih ys) (Nat.beq x y)) l2) l1
theorem eqListN_eq (l1 l2 : List Nat) : eqListN l1 l2 = (l1 == l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      change Bool.rec false (eqListN xs ys) (Nat.beq x y) = ((x :: xs) == (y :: ys))
      rw [ih]
      by_cases h : x = y
      · subst h; simp [Nat.beq_refl]
      · have h1 : Nat.beq x y = false := beq_false_ne h
        have h2 : (x == y) = false := beq_false_of_ne h
        simp [h1, h2]
def canonF (mask w : Nat) : Nat :=
  let v := Nat.land w mask
  Bool.rec
    (Bool.rec
      (let iv := Nat.xor mask v
       Bool.rec iv v (Nat.blt v iv))
      0 (Nat.beq v mask))
    0 (Nat.beq v 0)
theorem canonF_eq (mask w : Nat) : canonF mask w = canon mask w := by
  unfold canonF canon bsel; dsimp only
  change (Bool.rec (Bool.rec (Bool.rec (mask ^^^ (w &&& mask)) (w &&& mask) ((w &&& mask).blt (mask ^^^ (w &&& mask)))) 0 ((w &&& mask).beq mask)) 0 ((w &&& mask).beq 0) : Nat) = _
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def binOpF (mask op a b : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (canonF mask (Nat.land (Nat.xor mask a) b))
        (canonF mask (Nat.land a (Nat.xor mask b))) (Nat.beq op 2))
      (canonF mask (Nat.lor a b)) (Nat.beq op 1))
    (canonF mask (Nat.land a b)) (Nat.beq op 0)
theorem binOpF_eq (mask op a b : Nat) : binOpF mask op a b = binOp mask op a b := by
  unfold binOpF binOp bsel
  simp only [canonF_eq]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl
def dagPartF (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Bool.rec (Nat.beq n 0) true (Nat.beq p 0))
    (fun w _ rest p n =>
      Bool.rec
        (Bool.rec
          (forceW (Nat.land p w) (fun up =>
            forceW (Nat.land n w) (fun down =>
              Bool.rec false
                (forceW (Nat.xor p up) (fun offP =>
                  forceW (Nat.xor n down) (rest offP)))
                (rest up down))))
          true (Nat.beq n 0))
        true (Nat.beq p 0)) ws
theorem dagPartF_eq (ws : List Nat) (p n : Nat) : dagPartF ws p n = dagPart ws p n := by
  induction ws generalizing p n with
  | nil =>
    change Bool.rec (Nat.beq n 0) true (Nat.beq p 0) = (Nat.beq p 0 || Nat.beq n 0)
    cases Nat.beq p 0 <;> rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (forceW (Nat.land p w) (fun up =>
      forceW (Nat.land n w) (fun down =>
        Bool.rec false (forceW (Nat.xor p up) (fun offP => forceW (Nat.xor n down) (dagPartF ws offP)))
          (dagPartF ws up down)))) true (Nat.beq n 0)) true (Nat.beq p 0) =
      ((Nat.beq p 0 || Nat.beq n 0) || forceW (p &&& w) (fun up =>
        forceW (n &&& w) (fun down => dagPart ws up down &&
          forceW (p ^^^ up) (fun offP => forceW (n ^^^ down) (dagPart ws offP)))))
    simp only [forceW_eq]
    cases Nat.beq p 0
    · cases Nat.beq n 0
      · change Bool.rec false (dagPartF ws _ _) (dagPartF ws _ _) = (dagPart ws _ _ && dagPart ws _ _)
        rw [ih, ih]; cases dagPart ws (p &&& w) (n &&& w) <;> rfl
      · rfl
    · rfl
def insertSortedF (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => Bool.rec (y :: ih) (x :: y :: ys) (Nat.ble x y)) l
theorem insertSortedF_eq (x : Nat) (l : List Nat) : insertSortedF x l = insertSorted x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change Bool.rec (y :: insertSortedF x ys) (x :: y :: ys) (Nat.ble x y) =
      bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)
    rw [ih]; cases Nat.ble x y <;> rfl
def dropValF (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  Bool.rec l (List.rec [] (fun y _ ih => Bool.rec (y :: ih) ih (Nat.beq y x)) l) drop
theorem dropValF_eq (drop : Bool) (x : Nat) (l : List Nat) : dropValF drop x l = dropVal drop x l := by
  cases drop
  · rfl
  · induction l with
    | nil => rfl
    | cons y ys ih =>
      change Bool.rec (y :: dropValF true x ys) (dropValF true x ys) (Nat.beq y x) =
        bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)
      rw [ih]; cases Nat.beq y x <;> rfl
def subsetWordsF (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (Nat.shiftRight b 1)
      Bool.rec rest (insertSortedF w rest) (Nat.beq (Nat.land b 1) 1)) stock) bits
theorem subsetWordsF_eq (stock : List Nat) (bits : Nat) : subsetWordsF stock bits = subsetWords stock bits := by
  induction stock generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (subsetWordsF xs (Nat.shiftRight bits 1))
      (insertSortedF x (subsetWordsF xs (Nat.shiftRight bits 1))) (Nat.beq (Nat.land bits 1) 1) =
      bsel (Nat.beq (bits &&& 1) 1) (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))
    rw [ih, insertSortedF_eq]; cases Nat.beq (bits &&& 1) 1 <;> rfl
def childStateF (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := Nat.land token 3
  let op := Nat.land (Nat.shiftRight token 2) 3
  let b := Nat.land (Nat.shiftRight token 4) 15
  let a := Nat.shiftRight token 8
  Bool.rec
    (Bool.rec none
      (Bool.rec none
        (let x := getDN ws a
         let y := getDN ws b
         let z := binOpF mask op x y
         Bool.rec
           (Bool.rec
             (let keepA := Nat.beq (Nat.land keep 1) 1
              let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
              let rest := dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws)
              some (Nat.sub fuel 1, insertSortedF z rest, (z, x, y) :: hist))
             none (memN z ws))
           none (Nat.beq z 0))
        (Nat.blt b (lenN ws)))
      (Nat.blt a b))
    none (Nat.beq fuel 0)
theorem childStateF_eq (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    childStateF mask token state = childState mask token state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold childStateF childState
  simp only [lenN_eq, getDN_eq, binOpF_eq, memN_eq, dropValF_eq, insertSortedF_eq]
  cases Nat.beq fuel 0
  · cases Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
    · rfl
    · cases Nat.blt ((token >>> 4) &&& 15) ws.length
      · rfl
      · cases Nat.beq (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0)) 0
        · cases ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0))
          · cases Nat.beq ((token &&& 3) &&& 1) 1 <;> cases Nat.beq (((token &&& 3) >>> 1) &&& 1) 1 <;> rfl
          · rfl
        · rfl
  · rfl
def dagTraceF (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      Bool.rec
        (match prev (Nat.sub parent 1) with
         | none => none
         | some st => childStateF mask token st)
        (Bool.rec none (some (fuel, subsetWordsF stock token, []))
          (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
        (Nat.beq parent 0)) (Nat.add fuel 1)) i
theorem dagTraceF_eq (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    dagTraceF mask stock fuel forest i = dagTrace mask stock fuel forest i := by
  unfold dagTraceF dagTrace
  suffices ∀ steps j,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          Bool.rec
            (match prev (Nat.sub parent 1) with
             | none => none
             | some st => childStateF mask token st)
            (Bool.rec none (some (fuel, subsetWordsF stock token, []))
              (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
            (Nat.beq parent 0)) steps) j =
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j from
    this (fuel + 1) i
  intro steps
  induction steps with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    dsimp only
    have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
      rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
    cases Nat.beq (forest j).1 0
    · dsimp only
      rw [ih]
      cases (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          if Nat.beq (forest k).1 0 then
            if Nat.blt (forest k).2 (2 ^ stock.length) then some (rootState stock fuel (forest k).2) else none
          else (prev ((forest k).1 - 1)).bind (childState mask (forest k).2)) n) ((forest j).1 - 1)
      · rfl
      · exact childStateF_eq mask (forest j).2 _
    · dsimp only
      rw [hpow, subsetWordsF_eq]
      cases Nat.blt (forest j).2 (2 ^ stock.length) <;> rfl
def nthBound (bounds : List (Nat × List Nat × Nat × Nat)) (i : Nat) :
    Option (Nat × List Nat × Nat × Nat) :=
  (List.rec (motive := fun _ => Nat → Option (Nat × List Nat × Nat × Nat))
    (fun _ => none)
    (fun b _ ih k => Nat.rec (some b) (fun m _ => ih m) k) bounds) i
theorem nthBound_mem {bounds : List (Nat × List Nat × Nat × Nat)} {i : Nat} {b : Nat × List Nat × Nat × Nat}
    (h : nthBound bounds i = some b) : b ∈ bounds := by
  induction bounds generalizing i with
  | nil => simp [nthBound] at h
  | cons x xs ih =>
    cases i with
    | zero => cases h; exact List.mem_cons_self
    | succ m => exact List.mem_cons_of_mem _ (ih h)
def forceWP {α : Type} (w : Nat) (k : Nat → α) : α :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)
theorem forceWP_eq {α : Type} (w : Nat) (k : Nat → α) : forceWP w k = k w := by
  cases w <;> rfl
def forceCons {α : Type} (l : List Nat) (k : List Nat → α) : α :=
  match l with
  | [] => k []
  | x :: xs => k (x :: xs)
theorem forceCons_eq {α : Type} (l : List Nat) (k : List Nat → α) : forceCons l k = k l := by
  cases l <;> rfl
def forceList {α : Type} (ws : List Nat) (k : List Nat → α) : α :=
  (List.rec (motive := fun _ => (List Nat → α) → α) (fun k => k [])
    (fun w _ next k => next (fun rest => k (w :: rest))) ws) k
theorem forceList_eq {α : Type} (ws : List Nat) (k : List Nat → α) : forceList ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceList ws (fun rest => k (w :: rest)) = _
    rw [ih]
def canonV2 (mask w : Nat) : Nat :=
  forceWP (Nat.land w mask) (fun v =>
    Bool.rec
      (Bool.rec
        (forceWP (Nat.xor mask v) (fun iv => Bool.rec iv v (Nat.blt v iv)))
        0 (Nat.beq v mask))
      0 (Nat.beq v 0))
theorem canonV2_eq (mask w : Nat) : canonV2 mask w = canon mask w := by
  unfold canonV2 canon bsel; dsimp only
  rw [forceWP_eq]
  change Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (forceWP (Nat.xor mask (w &&& mask)) (fun iv => Bool.rec (motive := fun _ => Nat) iv (w &&& mask) (Nat.blt (w &&& mask) iv)))
      0 (Nat.beq (w &&& mask) mask)) 0 (Nat.beq (w &&& mask) 0) = _
  rw [forceWP_eq]
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def HistValid (mask : Nat) (stock : List Nat) : List (Nat × Nat × Nat) → Prop
  | [] => True
  | (z, x, y) :: rest =>
    (∃ op < 4, z = binOp mask op x y) ∧
    (x ∈ stock ∨ ∃ a b, (x, a, b) ∈ rest) ∧
    (y ∈ stock ∨ ∃ a b, (y, a, b) ∈ rest) ∧
    HistValid mask stock rest
def WsCovered (stock : List Nat) (hist : List (Nat × Nat × Nat)) (ws : List Nat) : Prop :=
  ∀ w ∈ ws, w ∈ stock ∨ ∃ a b, (w, a, b) ∈ hist
theorem getD_mem_of_lt {l : List Nat} {i : Nat} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
theorem childState_valid {mask token : Nat} {stock : List Nat}
    {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (hv : HistValid mask stock st.2.2) (hc : WsCovered stock st.2.2 st.2.1)
    (h : childState mask token st = some ch) :
    HistValid mask stock ch.2.2 ∧ WsCovered stock ch.2.2 ch.2.1 := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at hv hc
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok
      have hab : (token >>> 8) < ((token >>> 4) &&& 15) := by
        cases h1 : Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
        · exfalso; exact hok (Or.inl (Or.inr h1))
        · exact Nat.blt_eq.mp h1
      have hbl : ((token >>> 4) &&& 15) < ws.length := by
        cases h2 : Nat.blt ((token >>> 4) &&& 15) ws.length
        · exfalso; exact hok (Or.inr h2)
        · exact Nat.blt_eq.mp h2
      have hx : ws.getD (token >>> 8) 0 ∈ ws := getD_mem_of_lt (by omega)
      have hy : ws.getD ((token >>> 4) &&& 15) 0 ∈ ws := getD_mem_of_lt hbl
      have hop : ((token >>> 2) &&& 3) < 4 := by
        have := Nat.and_lt_two_pow (token >>> 2) (n := 2) (by omega : 3 < 2 ^ 2)
        simpa using this
      refine ⟨⟨⟨(token >>> 2) &&& 3, hop, rfl⟩, hc _ hx, hc _ hy, hv⟩, ?_⟩
      intro w hw
      rcases insertSorted_mem.mp hw with rfl | hrest
      · exact Or.inr ⟨_, _, List.mem_cons_self⟩
      · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hrest).1).1
        rcases hc w hwm with hst | ⟨a, b, hmem⟩
        · exact Or.inl hst
        · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ hmem⟩
theorem dagTrace_valid {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) :
    HistValid mask stock st.2.2 ∧ WsCovered stock st.2.2 st.2.1 := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s →
      HistValid mask stock s.2.2 ∧ WsCovered stock s.2.2 s.2.1 from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s
        exact ⟨trivial, fun w hw => Or.inl (subsetWords_subset stock _ w hw)⟩
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p =>
        rw [hp] at h
        have ⟨hv, hc⟩ := ih _ _ hp
        exact childState_valid hv hc h
theorem addUniq_mem {w u : Nat} {l : List Nat} : u ∈ addUniq w l ↔ u = w ∨ u ∈ l := by
  unfold addUniq
  cases h : l.contains w
  · simp [List.mem_cons]
  · simp only [ite_true]
    have hw : w ∈ l := List.contains_iff_mem.mp h
    constructor
    · exact Or.inr
    · rintro (rfl | hu); exact hw; exact hu
theorem recipeStart_mem {cut : Nat} {stock ws : List Nat} {u : Nat} :
    u ∈ recipeStart cut stock ws ↔ ∃ w ∈ ws, canon cut w = u ∧ ¬Avail stock u := by
  induction ws with
  | nil => simp [recipeStart]
  | cons w ws ih =>
    change u ∈ (if availB stock (canon cut w) then recipeStart cut stock ws
                else addUniq (canon cut w) (recipeStart cut stock ws)) ↔ _
    cases ha : availB stock (canon cut w)
    · simp only [Bool.false_eq_true, ite_false, addUniq_mem, ih]
      have hna : ¬Avail stock (canon cut w) := fun h => by rw [availB_spec.mpr h] at ha; exact Bool.noConfusion ha
      constructor
      · rintro (rfl | ⟨w', hw', rfl, hnu⟩)
        · exact ⟨w, List.mem_cons_self, rfl, hna⟩
        · exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact Or.inl rfl
        · exact Or.inr ⟨w', hw', rfl, hnu⟩
    · simp only [ite_true, ih]
      have hya : Avail stock (canon cut w) := availB_spec.mp ha
      constructor
      · rintro ⟨w', hw', rfl, hnu⟩; exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact absurd hya hnu
        · exact ⟨w', hw', rfl, hnu⟩
theorem recipeClose_sub {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} {acc : List Nat} :
    ∀ u ∈ acc, u ∈ recipeClose cut stock hist acc := by
  induction hist generalizing acc with
  | nil => intro u hu; exact hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro u hu
    change u ∈ (if acc.contains (canon cut w) then
      let va := canon cut a; let vb := canon cut b
      let acc1 := if availB stock va then acc else addUniq va acc
      let acc2 := if availB stock vb then acc1 else addUniq vb acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist acc)
    split
    · apply ih
      have h1 : u ∈ (if availB stock (canon cut a) then acc else addUniq (canon cut a) acc) := by
        split; exact hu; exact addUniq_mem.mpr (Or.inr hu)
      split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · exact ih u hu
theorem recipeClose_nil (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) :
    recipeClose cut stock hist [] = [] := by
  induction hist with
  | nil => rfl
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    change (if [].contains (canon cut w) then _ else recipeClose cut stock hist []) = []
    exact ih
theorem recipeClose_mono {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} :
    ∀ {A B : List Nat}, (∀ u ∈ A, u ∈ B) →
      ∀ u ∈ recipeClose cut stock hist A, u ∈ recipeClose cut stock hist B := by
  induction hist with
  | nil => intro A B hAB u hu; exact hAB u hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro A B hAB u hu
    change u ∈ (if A.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then A else addUniq (canon cut a) A
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist A) at hu
    change u ∈ (if B.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then B else addUniq (canon cut a) B
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist B)
    cases hA : A.contains (canon cut w)
    · simp only [hA, Bool.false_eq_true, ite_false] at hu
      cases hB : B.contains (canon cut w)
      · simp only [Bool.false_eq_true, ite_false]; exact ih hAB u hu
      · simp only [ite_true]
        apply ih _ u hu
        intro x hx
        have h1 : x ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
          split; exact hAB x hx; exact addUniq_mem.mpr (Or.inr (hAB x hx))
        split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · have hwB : B.contains (canon cut w) = true := List.contains_iff_mem.mpr (hAB _ (List.contains_iff_mem.mp hA))
      simp only [hA, ite_true] at hu
      simp only [hwB, ite_true]
      apply ih _ u hu
      intro x hx
      have h1 : ∀ y, y ∈ (if availB stock (canon cut a) then A else addUniq (canon cut a) A) →
          y ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
        intro y hy
        cases hca : availB stock (canon cut a)
        · simp only [hca, Bool.false_eq_true, ite_false, addUniq_mem] at hy ⊢
          rcases hy with rfl | hy; exact Or.inl rfl; exact Or.inr (hAB y hy)
        · simp only [hca, ite_true] at hy ⊢; exact hAB y hy
      cases hcb : availB stock (canon cut b)
      · simp only [hcb, Bool.false_eq_true, ite_false, addUniq_mem] at hx ⊢
        rcases hx with rfl | hx; exact Or.inl rfl; exact Or.inr (h1 x hx)
      · simp only [hcb, ite_true] at hx ⊢; exact h1 x hx
noncomputable def buildFrom (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    List (Nat × Nat × Nat) → List Nat
  | [] => []
  | (z, x, y) :: rest =>
    let vs := buildFrom cut bstock S rest
    let v := canon cut z
    let := Classical.propDecidable
    if v ∈ S ∧ ¬Avail (vs ++ bstock) v ∧ Avail (vs ++ bstock) (canon cut x) ∧ Avail (vs ++ bstock) (canon cut y)
    then vs ++ [v] else vs
theorem buildFrom_builds {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      BuildsBin cut bstock (buildFrom cut bstock S hist)
  | [], _ => trivial
  | (z, x, y) :: rest, ⟨⟨op, hop, hz⟩, _, _, hrest⟩ => by
    unfold buildFrom; dsimp only
    have ih := buildFrom_builds (bstock := bstock) (S := S) sub hrest
    split
    · rename_i hcond
      obtain ⟨_, hna, hax, hay⟩ := hcond
      have hgate : GateBin cut (buildFrom cut bstock S rest ++ bstock) (canon cut z) := by
        have hsub := canon_sub_binOp (op := op) (a := x) (b := y) sub
        rw [← hz] at hsub
        rcases hsub with h0 | hx | hy | ⟨op', hop', heq⟩
        · exact absurd (Or.inl h0) hna
        · exact absurd (hx ▸ hax) hna
        · exact absurd (hy ▸ hay) hna
        · exact ⟨canon cut x, canon cut y, op', hop', hax, hay, heq⟩
      exact builds_append ih ⟨hgate, trivial⟩
    · exact ih
theorem buildFrom_nodup_sub (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    ∀ (hist : List (Nat × Nat × Nat)),
      (buildFrom cut bstock S hist).Nodup ∧ ∀ u ∈ buildFrom cut bstock S hist, u ∈ S
  | [] => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | (z, x, y) :: rest => by
    unfold buildFrom; dsimp only
    obtain ⟨hnd, hsub⟩ := buildFrom_nodup_sub cut bstock S rest
    split
    · rename_i hcond
      obtain ⟨hvS, hna, _, _⟩ := hcond
      have hnm : canon cut z ∉ buildFrom cut bstock S rest := fun hm =>
        hna (Or.inr (List.mem_append_left bstock hm))
      refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun a ha b hb heq => by
        rw [List.mem_singleton.mp hb] at heq; exact hnm (heq ▸ ha)⟩, ?_⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hsub u hu
      · rw [List.mem_singleton.mp hu]; exact hvS
    · exact ⟨hnd, hsub⟩
theorem buildFrom_mono_avail (cut : Nat) (bstock : List Nat) (S : Finset Nat)
    (r : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) {u : Nat}
    (hu : Avail (buildFrom cut bstock S rest ++ bstock) u) :
    Avail (buildFrom cut bstock S (r :: rest) ++ bstock) u := by
  obtain ⟨z, x, y⟩ := r
  unfold buildFrom; dsimp only
  split
  · exact avail_weaken (fun w hw => by simp only [List.mem_append] at hw ⊢; tauto) hu
  · exact hu
theorem buildFrom_covers {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (hstk : ∀ s ∈ stock, Avail bstock (canon cut s)) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      ∀ (acc : List Nat),
        (∀ u ∈ acc, Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u) →
        (∀ u ∈ recipeClose cut bstock hist acc, u ∈ S) →
        ∀ u ∈ acc, Avail (buildFrom cut bstock S hist ++ bstock) u
  | [], _, acc, hcov, _, u, hu => by
    rcases hcov u hu with ha | ⟨_, _, _, hm, _⟩
    · exact avail_weaken (fun w hw => List.mem_append_right _ hw) ha
    · exact nomatch hm
  | (z, x, y) :: rest, ⟨_, hxc, hyc, hrest⟩, acc, hcov, hS, u, hu => by
    cases hcz : acc.contains (canon cut z)
    · have hnz : canon cut z ∉ acc := fun hm => by rw [List.contains_iff_mem.mpr hm] at hcz; exact Bool.noConfusion hcz
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then _ else recipeClose cut bstock rest acc)
        simp only [hcz, Bool.false_eq_true, ite_false]; exact hv
      have hcov' : ∀ v ∈ acc, Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v := by
        intro v hv
        rcases hcov v hv with ha | ⟨z', x', y', hm, heq⟩
        · exact Or.inl ha
        · rcases List.mem_cons.mp hm with hhead | htail
          · rcases Prod.mk.inj hhead with ⟨rfl, _⟩
            exact absurd (heq ▸ hv) hnz
          · exact Or.inr ⟨z', x', y', htail, heq⟩
      exact buildFrom_mono_avail cut bstock S (z, x, y) rest
        (buildFrom_covers hstk hrest acc hcov' hS' u hu)
    · have hzacc : canon cut z ∈ acc := List.contains_iff_mem.mp hcz
      have hzS : canon cut z ∈ S := hS _ (recipeClose_sub _ hzacc)
      set acc1 := if availB bstock (canon cut x) then acc else addUniq (canon cut x) acc
      set acc2 := if availB bstock (canon cut y) then acc1 else addUniq (canon cut y) acc1
      have hS2 : ∀ v ∈ recipeClose cut bstock rest acc2, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then recipeClose cut bstock rest acc2 else _)
        simp only [hcz, ite_true]; exact hv
      let := Classical.propDecidable
      set acc' := acc2.filter (fun v => decide (Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v))
      have hsub' : ∀ v ∈ acc', v ∈ acc2 := fun v hv => (List.mem_filter.mp hv).1
      have hcov' : ∀ v ∈ acc', Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v :=
        fun v hv => of_decide_eq_true (List.mem_filter.mp hv).2
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc', v ∈ S :=
        fun v hv => hS2 v (recipeClose_mono hsub' v hv)
      have hIH := buildFrom_covers hstk hrest acc' hcov' hS'
      have hacc_sub2 : ∀ v ∈ acc, v ∈ acc2 := by
        intro v hv
        have h1 : v ∈ acc1 := by
          unfold acc1; split; exact hv; exact addUniq_mem.mpr (Or.inr hv)
        unfold acc2; split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
      have hax : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut x) := by
        cases hbx : availB bstock (canon cut x)
        · have hx2 : canon cut x ∈ acc2 := by
            have hx1 : canon cut x ∈ acc1 := by
              unfold acc1; simp only [hbx, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
            unfold acc2; split; exact hx1; exact addUniq_mem.mpr (Or.inr hx1)
          have hpx : Avail bstock (canon cut x) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut x := by
            rcases hxc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk x hs)
            · exact Or.inr ⟨x, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hx2, decide_eq_true hpx⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hbx)
      have hay : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut y) := by
        cases hby : availB bstock (canon cut y)
        · have hy2 : canon cut y ∈ acc2 := by
            unfold acc2; simp only [hby, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
          have hpy : Avail bstock (canon cut y) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut y := by
            rcases hyc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk y hs)
            · exact Or.inr ⟨y, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hy2, decide_eq_true hpy⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hby)
      by_cases huz : u = canon cut z
      · subst huz
        unfold buildFrom; dsimp only
        split
        · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
        · rename_i hneg
          by_cases ha : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut z)
          · exact ha
          · exact absurd ⟨hzS, ha, hax, hay⟩ hneg
      · have hpu : Avail bstock u ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = u := by
          rcases hcov u hu with ha | ⟨z', x', y', hm, heq⟩
          · exact Or.inl ha
          · rcases List.mem_cons.mp hm with hhead | htail
            · rcases Prod.mk.inj hhead with ⟨rfl, _⟩; exact absurd heq.symm huz
            · exact Or.inr ⟨z', x', y', htail, heq⟩
        exact buildFrom_mono_avail cut bstock S (z, x, y) rest
          (hIH u (List.mem_filter.mpr ⟨hacc_sub2 u hu, decide_eq_true hpu⟩))
def flatStartF (cut : Nat) (stock ws : List Nat) : Nat × List Nat :=
  List.rec (0, []) (fun w _ ih =>
    match ih with
    | (fl, acc) =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec
          (Bool.rec
            (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
            (fl, acc) (memN v stock))
          (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
          (Nat.beq v 0))) ws
theorem flatStartF_eq (cut : Nat) (stock ws : List Nat) :
    flatStartF cut stock ws = (flatCount cut ws, recipeStart cut stock ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hstep : flatStartF cut stock (w :: ws) =
      match flatStartF cut stock ws with
      | (fl, acc) =>
        forceWP (canonV2 cut w) (fun v =>
          Bool.rec
            (Bool.rec
              (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
              (fl, acc) (memN v stock))
            (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
            (Nat.beq v 0)) := rfl
    rw [hstep, ih]; dsimp only; rw [forceWP_eq, canonV2_eq, forceWP_eq]
    change Bool.rec
        (Bool.rec
          (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
            (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) (recipeStart cut stock ws)))
          (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) stock))
        (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) (Nat.beq (canon cut w) 0) =
      (bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws),
       if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    simp only [memN_eq, availB, addUniq]
    have haux (b1 b2 b3 : Bool) :
        Bool.rec (Bool.rec (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
          (flatCount cut ws, recipeStart cut stock ws) b3)
          (flatCount cut ws, recipeStart cut stock ws) b2)
          (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) b1 =
        (bsel b1 (flatCount cut ws + 1) (flatCount cut ws),
         if (b1 || b2) = true then recipeStart cut stock ws
         else if b3 = true then recipeStart cut stock ws else canon cut w :: recipeStart cut stock ws) := by
      cases b1 <;> cases b2 <;> cases b3 <;> rfl
    exact haux _ _ _
def recipeCloseV2 (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (next acc)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: acc) acc (memN va acc)) acc (memN va stock)) acc (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    next))))
          (memN v acc))) hist needed
theorem recipeCloseV2_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseV2 cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hstep : recipeCloseV2 cut stock ((w, a, b) :: hist) needed =
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (recipeCloseV2 cut stock hist needed)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: needed) needed (memN va needed)) needed (memN va stock)) needed (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    (recipeCloseV2 cut stock hist)))))
          (memN v needed)) := rfl
    rw [hstep]
    simp only [forceWP_eq, forceCons_eq, canonV2_eq, memN_eq]
    change Bool.rec (recipeCloseV2 cut stock hist needed) _ (needed.contains (canon cut w)) =
      (if needed.contains (canon cut w) then
        let va := canon cut a; let vb := canon cut b
        let acc1 := if availB stock va then needed else addUniq va needed
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        recipeClose cut stock hist acc2
      else recipeClose cut stock hist needed)
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only [ite_true]
      rw [ih]
      congr 1
      have hadd (v : Nat) (l : List Nat) :
          Bool.rec (Bool.rec (Bool.rec (v :: l) l (l.contains v)) l (stock.contains v)) l (Nat.beq v 0) =
          if availB stock v then l else addUniq v l := by
        dsimp only [availB, addUniq]
        have haux (b1 b2 b3 : Bool) :
            Bool.rec (Bool.rec (Bool.rec (v :: l) l b3) l b2) l b1 =
            if (b1 || b2) = true then l else if b3 = true then l else v :: l := by
          cases b1 <;> cases b2 <;> cases b3 <;> rfl
        exact haux _ _ _
      rw [hadd (canon cut a) needed, hadd (canon cut b)]
def boundClosesV2 (fuel : Nat) (ws : List Nat) (hist : List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, bstock, lower, _) := bound
  match flatStartF cut bstock ws with
  | (fl, start0) =>
    forceWP (Nat.sub fuel fl) (fun rem =>
      Bool.rec false
        (match start0 with
         | [] => true
         | s0 :: sr =>
           forceList (s0 :: sr) (fun start =>
             Bool.rec false
               (Nat.blt (Nat.add (lenN (recipeCloseV2 cut bstock hist start)) rem) lower)
               (Nat.blt (Nat.add (lenN start) rem) lower)))
        (Nat.blt rem lower))
theorem boundClosesV2_sound {mask goal : Nat} {stock : List Nat}
    {fuel : Nat} {ws : List Nat} {hist : List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (hg : canon bound.1 goal = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0)
    (hstk : ∀ s ∈ stock, Avail bound.2.1 (canon bound.1 s))
    (hv : HistValid mask stock hist) (hc : WsCovered stock hist ws)
    (nd : ws.Nodup) {k : Nat} (hk : k ≤ fuel)
    (hlive : LiveBin mask goal k ws.toFinset) :
    boundClosesV2 fuel ws hist bound = false := by
  obtain ⟨cut, bstock, lower, bgoal⟩ := bound
  dsimp only at hlow sub hg hnz hstk
  apply Bool.eq_false_iff.mpr
  intro hbc
  unfold boundClosesV2 at hbc; dsimp only at hbc
  rw [flatStartF_eq] at hbc; dsimp only at hbc
  simp only [forceWP_eq] at hbc
  cases h1 : Nat.blt (Nat.sub fuel (flatCount cut ws)) lower
  · rw [h1] at hbc; exact Bool.noConfusion hbc
  · rw [h1] at hbc; dsimp only at hbc
    have hlen_lt : (recipeClose cut bstock hist (recipeStart cut bstock ws)).length + (fuel - flatCount cut ws) < lower := by
      cases hs : recipeStart cut bstock ws with
      | nil =>
        rw [recipeClose_nil]; simp only [List.length_nil, Nat.zero_add]
        exact Nat.blt_eq.mp h1
      | cons s0 sr =>
        rw [hs] at hbc; dsimp only at hbc
        simp only [forceList_eq, recipeCloseV2_eq, lenN_eq] at hbc
        cases h2 : Nat.blt (Nat.add (s0 :: sr).length (Nat.sub fuel (flatCount cut ws))) lower
        · rw [h2] at hbc; exact Bool.noConfusion hbc
        · rw [h2] at hbc; dsimp only at hbc
          exact Nat.blt_eq.mp hbc
    set needed := recipeClose cut bstock hist (recipeStart cut bstock ws)
    set S := needed.toFinset
    set vs := buildFrom cut bstock S hist
    have hvbd : BuildsBin cut bstock vs := buildFrom_builds sub hv
    obtain ⟨hvnd, hvsub⟩ := buildFrom_nodup_sub cut bstock S hist
    have hvlen : vs.length ≤ needed.length := by
      rw [← List.toFinset_card_of_nodup hvnd]
      have hsubf : vs.toFinset ⊆ S := fun u hu => hvsub u (List.mem_toFinset.mp hu)
      exact Nat.le_trans (Finset.card_le_card hsubf) (List.toFinset_card_le needed)
    have hcov_start : ∀ u ∈ recipeStart cut bstock ws,
        Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u := by
      intro u hu
      obtain ⟨w, hww, rfl, hna⟩ := recipeStart_mem.mp hu
      rcases hc w hww with hws | ⟨a, b, hmem⟩
      · exact absurd (hstk w hws) hna
      · exact Or.inr ⟨w, a, b, hmem, rfl⟩
    have hvs_start := buildFrom_covers hstk hv (recipeStart cut bstock ws) hcov_start
      (fun u hu => List.mem_toFinset.mpr hu)
    have hsup : ∀ w ∈ ws.toFinset, Avail (vs ++ bstock) (canon cut w) := by
      intro w hw
      have hww : w ∈ ws := List.mem_toFinset.mp hw
      by_cases ha : Avail bstock (canon cut w)
      · exact avail_weaken (fun u hu => List.mem_append_right _ hu) ha
      · exact hvs_start _ (recipeStart_mem.mpr ⟨w, hww, rfl, ha⟩)
    have hgnf : canon cut goal ≠ 0 := hg.symm ▸ hnz
    obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (vs ++ bstock) hsup
    rw [← flatCount_card cut nd] at hylen
    have hboth := builds_append hvbd hybd
    have hfinal : Avail ((vs ++ ys) ++ bstock) bgoal := by
      rw [← hg]
      exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
    have heno := hlow (vs ++ ys) hboth hfinal
    simp only [List.length_append] at heno
    omega
def edgeAxis (mask goal stride lm : Nat) : Nat :=
  let neg := Nat.xor mask goal
  Nat.land (Nat.lor (Nat.land (Nat.shiftRight goal stride) neg)
    (Nat.land goal (Nat.shiftRight neg stride))) lm
def edgePack (mask goal : Nat) : Nat :=
  Nat.lor (edgeAxis mask goal 1 0x5555555555555555)
    (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 2 0x3333333333333333) 64)
      (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f) 128)
        (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 8 0x00ff00ff00ff00ff) 192)
          (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 16 0x0000ffff0000ffff) 256)
            (Nat.shiftLeft (edgeAxis mask goal 32 0x00000000ffffffff) 320)))))
def sepAxis (stride lm w : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.shiftRight w stride) w) lm
def sepPack (w : Nat) : Nat :=
  Nat.lor (sepAxis 1 0x5555555555555555 w)
    (Nat.lor (Nat.shiftLeft (sepAxis 2 0x3333333333333333 w) 64)
      (Nat.lor (Nat.shiftLeft (sepAxis 4 0x0f0f0f0f0f0f0f0f w) 128)
        (Nat.lor (Nat.shiftLeft (sepAxis 8 0x00ff00ff00ff00ff w) 192)
          (Nat.lor (Nat.shiftLeft (sepAxis 16 0x0000ffff0000ffff w) 256)
            (Nat.shiftLeft (sepAxis 32 0x00000000ffffffff w) 320)))))
def orSep (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ ih => Nat.lor (sepPack w) ih) ws
theorem edgeAxis_live {mask goal stride lm k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset)
    {n : Nat} (he : (edgeAxis mask goal stride lm).testBit n = true) :
    ∃ w ∈ ws, (sepAxis stride lm w).testBit n = true := by
  unfold edgeAxis at he
  change (((goal >>> stride &&& (mask ^^^ goal)) ||| (goal &&& ((mask ^^^ goal) >>> stride))) &&& lm).testBit n = true at he
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Bool.and_eq_true, Bool.or_eq_true] at he
  obtain ⟨hcases, hlm⟩ := he
  have hpm : ∀ j, goal.testBit j = true → mask.testBit j = true := fun j hg => by
    have e := congrArg (fun x => x.testBit j) hgm
    simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
  have hnm : ∀ j, (mask ^^^ goal).testBit j = true → mask.testBit j = true ∧ goal.testBit j = false := fun j hn => by
    rw [Nat.testBit_xor] at hn
    cases hm : mask.testBit j <;> cases hg : goal.testBit j <;> simp_all
  have hsep : ∃ w ∈ ws, w.testBit (stride + n) ≠ w.testBit n := by
    by_contra! hall
    rcases hcases with ⟨hg1, hn0⟩ | ⟨hg0, hn1⟩
    · have h1 := hpm (stride + n) hg1
      have h0 := hnm n hn0
      have eq := liveBin_agrees h1 h0.1 hlive (fun w hw => hall w (List.mem_toFinset.mp hw))
      rw [hg1, h0.2] at eq; exact Bool.noConfusion eq
    · have h0 := hpm n hg0
      have h1 := hnm (stride + n) hn1
      have eq := liveBin_agrees h0 h1.1 hlive (fun w hw => (hall w (List.mem_toFinset.mp hw)).symm)
      rw [hg0, h1.2] at eq; exact Bool.noConfusion eq
  obtain ⟨w, hw, hne⟩ := hsep
  refine ⟨w, hw, ?_⟩
  unfold sepAxis
  change (((w >>> stride) ^^^ w) &&& lm).testBit n = true
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, hlm, Bool.and_true]
  cases hb1 : w.testBit (stride + n) <;> cases hb2 : w.testBit n <;> simp_all
theorem orSep_testBit {ws : List Nat} {w j : Nat}
    (hw : w ∈ ws) (hb : (sepPack w).testBit j = true) : (orSep ws).testBit j = true := by
  induction ws with
  | nil => cases hw
  | cons x xs ih =>
    change (sepPack x ||| orSep xs).testBit j = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | htl
    · exact Or.inl hb
    · exact Or.inr (ih htl)
theorem sepPack_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    Nat.beq (Nat.land (edgePack mask goal) (orSep ws)) (edgePack mask goal) = true := by
  apply Nat.beq_eq.mpr
  apply Nat.eq_of_testBit_eq; intro j
  change ((edgePack mask goal) &&& (orSep ws)).testBit j = (edgePack mask goal).testBit j
  rw [Nat.testBit_and]
  cases he : (edgePack mask goal).testBit j
  · rfl
  · simp only [Bool.true_and]
    have hlane (stride lm shift : Nat)
        (hl : (edgeAxis mask goal stride lm <<< shift).testBit j = true)
        (hs : ∀ w, (sepAxis stride lm w <<< shift).testBit j = true → (sepPack w).testBit j = true) :
        (orSep ws).testBit j = true := by
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive hl.2
      apply orSep_testBit hw
      apply hs w
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hl.1, hsw⟩
    unfold edgePack at he
    change (edgeAxis mask goal 1 0x5555555555555555 |||
      ((edgeAxis mask goal 2 0x3333333333333333 <<< 64) |||
        ((edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f <<< 128) |||
          ((edgeAxis mask goal 8 0x00ff00ff00ff00ff <<< 192) |||
            ((edgeAxis mask goal 16 0x0000ffff0000ffff <<< 256) |||
              (edgeAxis mask goal 32 0x00000000ffffffff <<< 320)))))).testBit j = true at he
    simp only [Nat.testBit_or, Bool.or_eq_true] at he
    rcases he with h0 | h1 | h2 | h3 | h4 | h5
    · obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive h0
      exact orSep_testBit hw (by
        unfold sepPack
        change (sepAxis 1 0x5555555555555555 w ||| _).testBit j = true
        simp [Nat.testBit_or, hsw])
    · exact hlane 2 0x3333333333333333 64 h1 (fun w hw => by
        unfold sepPack
        change (_ ||| ((sepAxis 2 0x3333333333333333 w <<< 64) ||| _)).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 4 0x0f0f0f0f0f0f0f0f 128 h2 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| ((sepAxis 4 0x0f0f0f0f0f0f0f0f w <<< 128) ||| _))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 8 0x00ff00ff00ff00ff 192 h3 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| ((sepAxis 8 0x00ff00ff00ff00ff w <<< 192) ||| _)))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 16 0x0000ffff0000ffff 256 h4 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| ((sepAxis 16 0x0000ffff0000ffff w <<< 256) ||| _))))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 32 0x00000000ffffffff 320 h5 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| (_ ||| (sepAxis 32 0x00000000ffffffff w <<< 320)))))).testBit j = true
        simp [Nat.testBit_or, hw])
def mapSep (ws : List Nat) : List (Nat × Nat) :=
  List.rec [] (fun w _ ih => (w, sepPack w) :: ih) ws
def forceSepPairs : List Nat → (List (Nat × Nat) → Bool) → Bool
  | [], k => k []
  | w :: ws, k => forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest)))
theorem forceSepPairs_eq (ws : List Nat) (k : List (Nat × Nat) → Bool) :
    forceSepPairs ws k = k (mapSep ws) := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest))) = _
    rw [forceW_eq, ih]; rfl
def orSepAll (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Nat.lor p.2 ih) ps
def orSepSkip (x : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 x)) ps
def orSepSkip2 (x y : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 y)) ih (Nat.beq p.1 x)) ps
theorem orSepAll_mapSep (ws : List Nat) : orSepAll (mapSep ws) = orSep ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => change Nat.lor (sepPack w) (orSepAll (mapSep ws)) = Nat.lor (sepPack w) (orSep ws); rw [ih]
theorem orSepSkip_mapSep (x : Nat) (ws : List Nat) :
    orSepSkip x (mapSep ws) = orSep (dropVal true x ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Nat.lor (sepPack w) (orSepSkip x (mapSep ws))) (orSepSkip x (mapSep ws)) (Nat.beq w x) =
      orSep (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws))
    rw [ih]
    cases Nat.beq w x <;> rfl
theorem dropVal_comm (x y : Nat) (l : List Nat) :
    dropVal true y (dropVal true x l) = dropVal true x (dropVal true y l) := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    change dropVal true y (bsel (Nat.beq u x) (dropVal true x us) (u :: dropVal true x us)) =
      dropVal true x (bsel (Nat.beq u y) (dropVal true y us) (u :: dropVal true y us))
    cases hux : Nat.beq u x <;> cases huy : Nat.beq u y
    · simp only [bsel_false]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) =
        bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [huy, hux, bsel_false, bsel_false, ih]
    · simp only [bsel_false, bsel_true]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) = _
      rw [huy, bsel_true, ih]
    · simp only [bsel_true, bsel_false]
      change _ = bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [hux, bsel_true, ih]
    · simp only [bsel_true]; exact ih
theorem orSepSkip2_mapSep (x y : Nat) (ws : List Nat) :
    orSepSkip2 x y (mapSep ws) = orSep (dropVal true y (dropVal true x ws)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (Nat.lor (sepPack w) (orSepSkip2 x y (mapSep ws))) (orSepSkip2 x y (mapSep ws)) (Nat.beq w y))
      (orSepSkip2 x y (mapSep ws)) (Nat.beq w x) =
      orSep (dropVal true y (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws)))
    rw [ih]
    cases hx : Nat.beq w x
    · rw [bsel_false]
      change Bool.rec (Nat.lor (sepPack w) (orSep (dropVal true y (dropVal true x ws))))
        (orSep (dropVal true y (dropVal true x ws))) (Nat.beq w y) =
        orSep (bsel (Nat.beq w y) (dropVal true y (dropVal true x ws)) (w :: dropVal true y (dropVal true x ws)))
      cases Nat.beq w y <;> rfl
    · rw [bsel_true]
def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi
theorem treeBlockF_eq (lo hi : Nat) (f : Nat → Bool) : treeBlockF lo hi f = treeBlock lo hi f := by
  unfold treeBlockF treeBlock
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          Bool.rec true
            (let m := Nat.shiftRight (Nat.add x y) 1
             Bool.rec (Bool.rec false (next m y) (next x m)) (f x) (Nat.beq x m))
            (Nat.blt x y)) steps) a b =
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b from
    this (hi - lo + 1) lo hi
  intro steps
  induction steps with
  | zero => intro a b; rfl
  | succ s ih =>
    intro a b
    dsimp only
    have hdiv : Nat.shiftRight (Nat.add a b) 1 = (a + b) / 2 := by
      change (a + b) >>> 1 = (a + b) / 2; rw [Nat.shiftRight_eq_div_pow]
    rw [hdiv]
    cases Nat.blt a b
    · rfl
    · cases Nat.beq a ((a + b) / 2)
      · rw [ih, ih]
        change Bool.rec false _ _ = (_ && _)
        cases (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true) _ s) a ((a + b) / 2) <;> rfl
      · rfl
theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h
def checkHintBoundV5 (goal negGoal fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (bounds : List (Nat × List Nat × Nat × Nat)) (cid : Nat) : Bool :=
  match nthBound bounds cid with
  | some b => boundClosesV2 fuel1 ws1 hist1 b
  | none => Bool.rec true false (dagPartF ws1 goal negGoal)
theorem checkHintBoundV5_open {mask goal fuel1 cid : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    checkHintBoundV5 goal (Nat.xor mask goal) fuel1 ws1 hist1 bounds cid = false := by
  unfold checkHintBoundV5
  cases hb : nthBound bounds cid with
  | some b =>
    dsimp only
    have hmem := nthBound_mem hb
    have hg := hgoals b hmem
    exact boundClosesV2_sound (hknown b hmem) (hsub b hmem) hg.1 hg.2 (hstk b hmem) hv hc nd hk hlive
  | none =>
    dsimp only
    have hdp : dagPartF ws1 goal (Nat.xor mask goal) = true := by
      have heq : dagPartF ws1 goal (Nat.xor mask goal) = dagPart ws1 goal (mask ^^^ goal) :=
        dagPartF_eq ws1 goal (mask ^^^ goal)
      rw [heq]; exact dagPart_live hgm hlive
    rw [hdp]
def hintCloseLeafV5 (goal negGoal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (sp : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec (some (cur, h))
    (forceWP (Nat.land h 3) (fun tag =>
      Bool.rec
        (Bool.rec none
          (forceWP (Nat.shiftRight h 2) (fun h' => some (cur, h')))
          (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds tag))
        (forceWP (Nat.shiftRight h 2) (fun h1 =>
          forceWP (Nat.add 3 (Nat.land h1 cutMask)) (fun cid =>
            Bool.rec none
              (forceWP (Nat.shiftRight h1 cutBits) (fun h' => some (cur, h')))
              (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds cid))))
        (Nat.beq tag 3)))
    (Nat.beq (Nat.land ep sp) ep)
theorem hintCloseLeafV5_open {mask goal cutBits cutMask fuel1 : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)} {h : Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    hintCloseLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask bounds fuel1 ws1 hist1 (orSep ws1) cur h = none := by
  unfold hintCloseLeafV5
  rw [sepPack_live hgm hlive]; dsimp only
  rw [forceWP_eq]
  cases Nat.beq (Nat.land h 3) 3
  · dsimp only
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
  · dsimp only
    rw [forceWP_eq, forceWP_eq]
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
def stepLeafV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match cur with
  | (t, dest) :: tl =>
    Bool.rec
      (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) cur h)
      (Bool.rec none
        (match states dest with
         | none => none
         | some saved =>
           Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 (insertSortedF z rest)))
             (Nat.beq saved.1 fuel1))
        (Nat.blt dest count))
      (Nat.beq tok t)
  | [] =>
    hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) [] h
theorem stepLeafV5_ref {mask goal cutBits cutMask count fuel1 z tok h : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    {res : List (Nat × Nat) × Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 (z :: rest))
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (hok : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds states
      fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur h = some res) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (cur := cur) (h := h)
    hgm hknown hsub hgoals hstk hv hc nd hk hlive
  unfold stepLeafV5 at hok
  have hor : Nat.lor (sepPack z) (orSep rest) = orSep (z :: rest) := rfl
  rw [hor] at hok
  cases cur with
  | nil => dsimp only at hok; rw [hcl] at hok; cases hok
  | cons hd tl =>
    obtain ⟨t, dest⟩ := hd
    dsimp only at hok
    cases ht : Nat.beq tok t
    · rw [ht] at hok; dsimp only at hok; rw [hcl] at hok; cases hok
    · rw [ht] at hok; dsimp only at hok
      cases hlt : Nat.blt dest count
      · rw [hlt] at hok; dsimp only at hok; cases hok
      · rw [hlt] at hok; dsimp only at hok
        cases hst : states dest with
        | none => rw [hst] at hok; dsimp only at hok; cases hok
        | some saved =>
          rw [hst] at hok; dsimp only at hok
          cases hf : Nat.beq saved.1 fuel1
          · rw [hf] at hok; dsimp only at hok; cases hok
          · rw [hf] at hok; dsimp only at hok
            cases heq : eqListN saved.2.1 (insertSortedF z rest)
            · rw [heq] at hok; dsimp only at hok; cases hok
            · rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at heq
              exact ⟨dest, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, heq⟩
def checkKeepsV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match (Bool.rec
    (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => none
  | some (c1, h1) =>
    match (Bool.rec
      (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => none
    | some (c2, h2) =>
      match (Bool.rec
        (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => none
      | some (c3, h3) =>
        Bool.rec
          (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3 h3)
          (some (c3, h3)) (Nat.blt fuel (Nat.add n 1))
theorem checkKeepsV5_at {goal negGoal ep cutBits cutMask count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hok : checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur h = some res)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c hh = some r
    | true, false => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c hh = some r
    | false, true => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c hh = some r
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c hh = some r := by
  unfold checkKeepsV5 at hok
  cases hp0 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1
    rw [hp0] at hok; dsimp only at hok
    cases hp1 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2
      rw [hp1] at hok; dsimp only at hok
      cases hp2 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3
        rw [hp2] at hok; dsimp only at hok
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, h, (c1, h1), hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, h2, (c3, h3), hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, h1, (c2, h2), hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at hok; exact Or.inr ⟨c3, h3, res, hok⟩
          · exact Or.inl rfl
def checkOpV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  forceWP (canonV2 mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWP (sepPack z) (fun spZ =>
          checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur h))
        (some (cur, h)) (memN z ws0))
      (some (cur, h)) (Nat.beq z 0))
def check4OpsV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => none
  | some (c1, h1) =>
    match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => none
    | some (c2, h2) =>
      match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => none
      | some (c3, h3) =>
        checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3 h3
theorem check4OpsV5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hop : op < 4)
    (hok : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h = some res) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z (sepPack z)
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c hh = some r := by
  unfold check4OpsV5 at hok
  have extract (rawZ op' : Nat) (c0 : List (Nat × Nat)) (h0 : Nat) (r0 : List (Nat × Nat) × Nat)
      (hz : canon mask rawZ = binOp mask op' x y)
      (hrun : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y rawZ op'
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0 h0 = some r0) :
      binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
        ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n (binOp mask op' x y)
          (sepPack (binOp mask op' x y)) spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB
          ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c hh = some r := by
    unfold checkOpV5 at hrun
    rw [forceWP_eq, canonV2_eq, hz] at hrun
    cases hz0 : Nat.beq (binOp mask op' x y) 0
    · rw [hz0] at hrun; dsimp only at hrun
      cases hm : memN (binOp mask op' x y) ws0
      · rw [hm] at hrun; dsimp only at hrun
        rw [forceWP_eq] at hrun
        exact Or.inr (Or.inr ⟨c0, h0, r0, hrun⟩)
      · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
    · exact Or.inl (Nat.beq_eq.mp hz0)
  cases hp0 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1; rw [hp0] at hok; dsimp only at hok
    cases hp1 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2; rw [hp1] at hok; dsimp only at hok
      cases hp2 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3; rw [hp2] at hok; dsimp only at hok
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur h (c1, h1) rfl hp0
        · exact extract _ 1 c1 h1 (c2, h2) rfl hp1
        · exact extract _ 2 c2 h2 (c3, h3) rfl hp2
        · exact extract _ 3 c3 h3 res rfl hok
def loopB_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, b, cur, h =>
    forceWP (getDN ws0 b) (fun y =>
      forceList (dropValF true y ws0) (fun wsNoB =>
        forceList (dropValF true y wsNoA) (fun wsNoAB =>
          forceWP (orSepSkip y ps) (fun spNoB =>
            forceWP (orSepSkip2 x y ps) (fun spNoAB =>
              forceWP (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) (fun tokAB =>
                match check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
                | none => none
                | some (cur1, h1) =>
                  loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1 h1))))))
theorem loopB_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (hok : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur h = some res) :
    let y := getDN ws0 b
    ∃ c hh r, check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c hh = some r := by
  induction rem generalizing b0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopB_V5 at hok
    rw [forceWP_eq, forceList_eq, forceList_eq, forceWP_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : b = b0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) hok
def loopA_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, a, cur, h =>
    forceWP (getDN ws0 a) (fun x =>
      forceList (dropValF true x ws0) (fun wsNoA =>
        forceWP (Nat.xor mask x) (fun nx =>
          forceWP (orSepSkip x ps) (fun spNoA =>
            match loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur h with
            | none => none
            | some (cur1, h1) =>
              loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1 h1))))
theorem loopA_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (hok : loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur h = some res) :
    let x := getDN ws0 a
    ∃ c hh r, loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c hh = some r := by
  induction rem generalizing a0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopA_V5 at hok
    rw [forceWP_eq, forceList_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : a = a0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) hok
def dagCheckNodeV5 (mask goal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (nodeHints : Nat → Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      forceWP (lenN ws0) (fun n =>
        Bool.rec
          (Bool.rec
            (Bool.rec false
              (forceW (Nat.xor mask goal) (fun negGoal =>
                forceW (Nat.sub fuel 1) (fun fuel1 =>
                  forceSepPairs ws0 (fun ps =>
                    forceW (orSepAll ps) (fun spAll =>
                      forceW (nodeHints (Nat.add i 1)) (fun h0 =>
                        match loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist n 0 (cursors (Nat.add i 1)) h0 with
                        | none => false
                        | some _ => true))))))
              (Nat.blt n 17))
            true (Nat.beq fuel 0))
          false (memN goal ws0)))
def stepRootV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec
    (match cur with
     | (t, dest) :: tl =>
       Bool.rec
         (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) cur h)
         (Bool.rec none
           (match states dest with
            | none => none
            | some saved =>
              Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 ws)) (Nat.beq saved.1 fuel))
           (Nat.blt dest count))
         (Nat.beq tok t)
     | [] =>
       hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) [] h)
    (some (cur, h)) (Nat.blt (Nat.add fuel 1) (lenN ws))
def loopRootsV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, tok, cur, h =>
    forceList (subsetWordsF stock tok) (fun ws =>
      match stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states ws tok cur h with
      | none => none
      | some (cur1, h1) =>
        loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem (Nat.add tok 1) cur1 h1)
def dagCheckRootsV5 (mask goal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (rootHint : Nat) (stock : List Nat) (fuel : Nat) : Bool :=
  match loopRootsV5 goal (Nat.xor mask goal) ep cutBits cutMask count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur rootHint with
  | none => false
  | some _ => true
theorem loopRootsV5_at {goal negGoal ep cutBits cutMask count fuel : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (hok : loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem t0 cur h = some res) :
    ∃ c hh r, stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock tok) tok c hh = some r := by
  induction rem generalizing t0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV5 at hok
    rw [forceList_eq] at hok
    cases hp : stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock t0) t0 cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : tok = t0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) hok
theorem dagAllNodesV5 {mask goal cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal (edgePack mask goal) cutBits cutMask bounds count
      (dagTrace mask stock fuel forest) cursors nodeHints i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    obtain ⟨hv, hcov⟩ := dagTrace_valid htr
    dsimp only at hv hcov
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeV5 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, forceWP_eq, lenN_eq, memN_eq] at hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hchk; exact Bool.noConfusion hchk
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      cases hcg : ws.contains goal
      · rw [hcg] at hchk; dsimp only at hchk
        have hrem0 : Nat.beq rem 0 = false := beq_false_ne hrem_pos
        rw [hrem0] at hchk; dsimp only at hchk
        cases h17 : Nat.blt ws.length 17
        · rw [h17] at hchk; exact Bool.noConfusion hchk
        · rw [h17] at hchk; dsimp only at hchk
          rw [forceW_eq, forceW_eq, forceSepPairs_eq, forceW_eq, forceW_eq] at hchk
          cases hloop : loopA_V5 mask goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
              (dagTrace mask stock fuel forest) rem (Nat.sub rem 1) ws.length (orSepAll (mapSep ws)) ws (mapSep ws) hist
              ws.length 0 (cursors (Nat.add i 1)) (nodeHints (Nat.add i 1)) with
          | none => rw [hloop] at hchk; exact Bool.noConfusion hchk
          | some resA =>
            have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
            have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
            obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
            obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
            have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
            have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
                ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
                  ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
                  ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
                  binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
                  LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                    (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
              by_cases hlt : ia0 < ib0
              · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
                  by simp only [hlt, ite_true]; exact hea0,
                  by simp only [hlt, ite_true]; exact heb0,
                  by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
              · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
                have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                    dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
                  ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
                exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
                  by simp only [hlt, ite_false]; exact heb0,
                  by simp only [hlt, ite_false]; exact hea0,
                  by rw [hea0, heb0, hopEq],
                  by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
            obtain ⟨cA, hA, rA, hB⟩ := loopA_V5_at (a := a) (Nat.zero_le a) (by omega) hloop
            obtain ⟨cB, hB', rB, hO⟩ := loopB_V5_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
            simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
            set x := ws.getD a 0
            set y := ws.getD b 0
            set z := binOp mask op x y
            have hznz : z ≠ 0 := hzeq.symm ▸ hz0
            have hznm : ws.contains z = false := by
              cases h : ws.contains z
              · rfl
              · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
            rcases check4OpsV5_at hop_lt hO with hz' | hcm | ⟨cK, hK', rK, hK⟩
            · exact hznz hz'
            · rw [hznm] at hcm; exact Bool.noConfusion hcm
            · have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
              have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
              have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
              have hzNotW : z ∉ ws := fun hm => by
                have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
              have hdropComm : dropVal true y (dropVal true x ws) = dropVal true x (dropVal true y ws) :=
                dropVal_comm x y ws
              set rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
              have hv' : HistValid mask stock ((z, x, y) :: hist) :=
                ⟨⟨op, hop_lt, rfl⟩, hcov x hxM, hcov y hyM, hv⟩
              have hcov' : WsCovered stock ((z, x, y) :: hist) (z :: rest) := by
                intro w hw
                rcases List.mem_cons.mp hw with rfl | hw'
                · exact Or.inr ⟨x, y, List.mem_cons_self⟩
                · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hw').1).1
                  rcases hcov w hwm with hst | ⟨u, v, hm⟩
                  · exact Or.inl hst
                  · exact Or.inr ⟨u, v, List.mem_cons_of_mem _ hm⟩
              have hnd_u : (z :: rest).Nodup :=
                List.nodup_cons.mpr ⟨fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1,
                  dropVal_nodup (dropVal_nodup nd)⟩
              have hset_u : (z :: rest).toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
                ext w; simp only [rest, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, ← dropVal_toFinset]
              have hlive_u : LiveBin mask goal k' (z :: rest).toFinset := by rwa [hset_u]
              have hset_s : (insertSorted z rest).toFinset = (z :: rest).toFinset := by
                ext w; simp only [List.mem_toFinset, insertSorted_mem, List.mem_cons]
              have hlive_s : LiveBin mask goal k' (insertSorted z rest).toFinset := by rwa [hset_s]
              have hlen' : (insertSorted z rest).length =
                  ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) :=
                list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
              have hcard' : (insertSorted z rest).length ≤ rem := by
                have hnd_s : (insertSorted z rest).Nodup :=
                  insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
                have := liveBin_card_le hlive_s
                rw [List.toFinset_card_of_nodup hnd_s] at this; omega
              have h2len : 2 ≤ ws.length := by
                have hsub2 : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
                  intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
                  · exact List.mem_toFinset.mpr hxM
                  · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hyM
                have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
                have hc := Finset.card_le_card hsub2
                rw [List.toFinset_card_of_nodup nd] at hc; omega
              have hka := checkKeepsV5_at hK keepA keepB
              have finish {tok' hh' : Nat} {c' : List (Nat × Nat)} {rr : List (Nat × Nat) × Nat}
                  (hstep : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
                    (dagTrace mask stock fuel forest) (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c' hh' = some rr) : False := by
                obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                  stepLeafV5_ref hgm hknown hsub hgoals hstk hv' hcov' hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
                exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
              cases keepA <;> cases keepB
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
                · rw [hdropComm] at hst; exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
                · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk
def nodupB : List Nat → Bool
  | [] => true
  | w :: ws => !memN w ws && nodupB ws
theorem nodupB_spec {l : List Nat} (h : nodupB l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons w ws ih =>
    unfold nodupB at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', memN_eq] at h
    exact List.nodup_cons.mpr ⟨fun hm => by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.1, ih h.2⟩
theorem kn_nil : KnownBin [] := fun _ h => nomatch h
theorem kn_cons {m : Nat} {s : List Nat} {l g : Nat} {bs : List (Nat × List Nat × Nat × Nat)}
    (h : LowerBin m s g l) (hs : KnownBin bs) : KnownBin ((m, s, l, g) :: bs) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h
  · exact hs b hb
def checkSliceMetaV5 (mask goal ep : Nat) (stock : List Nat)
    (bounds : List (Nat × List Nat × Nat × Nat)) : Bool :=
  Nat.beq (Nat.land goal mask) goal &&
  !Nat.beq goal 0 &&
  stock.all (fun w => Nat.beq (canon mask w) w) &&
  nodupB stock &&
  Nat.beq ep (edgePack mask goal) &&
  bounds.all (fun b =>
    Nat.beq (Nat.land mask b.1) b.1 &&
    Nat.beq (canon b.1 goal) b.2.2.2 &&
    !Nat.beq b.2.2.2 0 &&
    stock.all (fun s => availB b.2.1 (canon b.1 s)))
theorem lowerDagV5 {mask goal ep cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hknown : KnownBin bounds)
    (hroots : dagCheckRootsV5 mask goal ep cutBits cutMask count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) (nodeHints 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal ep cutBits cutMask bounds count
      (dagTraceF mask stock fuel forest) cursors nodeHints i = true)
    (hmeta : checkSliceMetaV5 mask goal ep stock bounds = true) :
    LowerBin mask stock goal (fuel + 1) := by
  unfold checkSliceMetaV5 at hmeta
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmeta
  obtain ⟨⟨⟨⟨⟨hgmB, hgnzB⟩, hcs⟩, hndB⟩, hepB⟩, hbdB⟩ := hmeta
  have hgm : Masked mask goal := Nat.beq_eq.mp hgmB
  have hgnz : goal ≠ 0 := fun h => by rw [h] at hgnzB; exact Bool.noConfusion hgnzB
  have snd : stock.Nodup := nodupB_spec hndB
  have hep : ep = edgePack mask goal := Nat.beq_eq.mp hepB
  have hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact Nat.beq_eq.mp h.1.1.1
  have hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨Nat.beq_eq.mp h.1.1.2, fun h0 => by rw [h0] at h; exact Bool.noConfusion h.1.2⟩
  have hstkB : ∀ b ∈ bounds, stock.all (fun s => availB b.2.1 (canon b.1 s)) = true := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact h.2
  subst hep
  have hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s) := fun b hb s hs =>
    availB_spec.mp (List.all_eq_true.mp (hstkB b hb) s hs)
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  unfold dagCheckRootsV5 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  cases hrl : loopRootsV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count fuel bounds
      (dagTrace mask stock fuel forest) stock (2 ^ stock.length) 0 (cursors 0) (nodeHints 0) with
  | none => rw [hrl] at hroots; exact Bool.noConfusion hroots
  | some resR =>
    obtain ⟨c, hh, rr, hsr⟩ := loopRootsV5_at (tok := tok) (Nat.zero_le tok) (by omega) hrl
    rw [subsetWordsF_eq] at hsr
    have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
    have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
    have hcard : (subsetWords stock tok).length ≤ fuel + 1 := by
      have := liveBin_card_le hlive'
      rw [List.toFinset_card_of_nodup hnd] at this; omega
    have hnw : Nat.blt (Nat.add fuel 1) (lenN (subsetWords stock tok)) = false := by
      rw [lenN_eq]
      cases h : Nat.blt (Nat.add fuel 1) (subsetWords stock tok).length
      · rfl
      · have hlt' : fuel + 1 < (subsetWords stock tok).length := Nat.blt_eq.mp h
        omega
    have hcov0 : WsCovered stock [] (subsetWords stock tok) :=
      fun w hw => Or.inl (subsetWords_subset stock tok w hw)
    have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (fuel1 := fuel) (hist1 := []) (cur := c) (h := hh)
      hgm hknown hsub hgoals hstk trivial hcov0 hnd (k := k) (by omega) hlive'
    unfold stepRootV5 at hsr
    rw [hnw] at hsr; dsimp only at hsr
    cases c with
    | nil => dsimp only at hsr; rw [hcl] at hsr; cases hsr
    | cons hd tl =>
      obtain ⟨t, dest⟩ := hd
      dsimp only at hsr
      cases ht : Nat.beq tok t
      · rw [ht] at hsr; dsimp only at hsr; rw [hcl] at hsr; cases hsr
      · rw [ht] at hsr; dsimp only at hsr
        cases hltc : Nat.blt dest count
        · rw [hltc] at hsr; dsimp only at hsr; cases hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest dest with
          | none => rw [htr2] at hsr; dsimp only at hsr; cases hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; dsimp only at hsr; cases hsr
            · rw [hf] at hsr; dsimp only at hsr
              cases heq : eqListN saved.2.1 (subsetWords stock tok)
              · rw [heq] at hsr; dsimp only at hsr; cases hsr
              · rw [eqListN_eq, beq_iff_eq] at heq
                exact dagAllNodesV5 hgm hknown hsub hgoals hstk snd hnodes fuel dest saved
                  (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (heq ▸ hlive')
def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)
def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))
def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    forceWP (Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask) (fun code =>
      unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc))
def unpackCursorV5 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      unpackListAux data (Nat.shiftRight entry sizeBits) w wMask tokBits tokMask (Nat.land entry sizeMask) [])
def unpackHintV5 (index data idxW idxMask lenBits lenMask : Nat) : Nat → Nat :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      forceWP (Nat.land entry lenMask) (fun hlen =>
        Bool.rec
          (Nat.land (Nat.shiftRight data (Nat.shiftRight entry lenBits)) (Nat.sub (Nat.shiftLeft 1 hlen) 1))
          0 (Nat.beq hlen 0)))

def m_0 : Nat := 0x4444444400000000
def s_0 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_0 : Nat := 0x4044400000000
def ep_0 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_0 : Nat → Nat := fun _ => 0
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_0 : Nat → Bool := dagCheckNodeV5 m_0 g_0 ep_0 1 1 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0 nh_0
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV5 m_0 g_0 ep_0 1 1 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) (nh_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 ch_0 = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → ch_0 i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV5 (kn_nil) rc_0 nc_0 (by decide +kernel)

def m_1 : Nat := 0x5500550000000000
def s_1 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_1 : Nat := 0x100150000000000
def ep_1 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_1 : Nat → Nat := fun _ => 0
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_1 : Nat → Bool := dagCheckNodeV5 m_1 g_1 ep_1 1 1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1 nh_1
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV5 m_1 g_1 ep_1 1 1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) (nh_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 ch_1 = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → ch_1 i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV5 (kn_nil) rc_1 nc_1 (by decide +kernel)

def m_2 : Nat := 0x5050505000000000
def s_2 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_2 : Nat := 0x10105000000000
def ep_2 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_2 : Nat → Nat := fun _ => 0
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_2 : Nat → Bool := dagCheckNodeV5 m_2 g_2 ep_2 1 1 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2 nh_2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV5 m_2 g_2 ep_2 1 1 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) (nh_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 ch_2 = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → ch_2 i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV5 (kn_nil) rc_2 nc_2 (by decide +kernel)

def m_3 : Nat := 0x5000500050005000
def s_3 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_3 : Nat := 0x100010005000
def ep_3 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_3 : Nat → Nat := fun _ => 0
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_3 : Nat → Bool := dagCheckNodeV5 m_3 g_3 ep_3 1 1 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3 nh_3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV5 m_3 g_3 ep_3 1 1 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) (nh_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 ch_3 = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → ch_3 i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV5 (kn_nil) rc_3 nc_3 (by decide +kernel)

def m_4 : Nat := 0x3333000000000000
def s_4 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_4 : Nat := 0x113000000000000
def ep_4 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_4 : Nat → Nat := fun _ => 0
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_4 : Nat → Bool := dagCheckNodeV5 m_4 g_4 ep_4 1 1 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4 nh_4
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV5 m_4 g_4 ep_4 1 1 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) (nh_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 ch_4 = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → ch_4 i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV5 (kn_nil) rc_4 nc_4 (by decide +kernel)

def m_5 : Nat := 0x5555000000000000
def s_5 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_5 : Nat := 0x115000000000000
def ep_5 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_5 : Nat → Nat := fun _ => 0
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_5 : Nat → Bool := dagCheckNodeV5 m_5 g_5 ep_5 1 1 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5 nh_5
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV5 m_5 g_5 ep_5 1 1 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) (nh_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 ch_5 = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → ch_5 i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV5 (kn_nil) rc_5 nc_5 (by decide +kernel)

def m_6 : Nat := 0x222200002222
def s_6 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_6 : Nat := 0x200000222
def ep_6 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000000000000000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
def cur_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_6 : Nat → Nat := fun _ => 0
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_6 : Nat → Bool := dagCheckNodeV5 m_6 g_6 ep_6 1 1 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6 nh_6
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV5 m_6 g_6 ep_6 1 1 1 bds_6 (dagTraceF m_6 s_6 3 f_6) (cur_6 0) (nh_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6 : treeBlockF 0 1 ch_6 = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → ch_6 i = true := fun _ h1 h2 => treeBlockF_at nb_6 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagV5 (kn_nil) rc_6 nc_6 (by decide +kernel)

def m_7 : Nat := 0xaa000000aa
def s_7 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_7 : Nat := 0x20000002a
def ep_7 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_7 : Nat → Nat := fun _ => 0
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_7 : Nat → Bool := dagCheckNodeV5 m_7 g_7 ep_7 1 1 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7 nh_7
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV5 m_7 g_7 ep_7 1 1 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) (nh_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 ch_7 = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → ch_7 i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV5 (kn_nil) rc_7 nc_7 (by decide +kernel)

def m_8 : Nat := 0xff000000000000
def s_8 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_8 : Nat := 0x17000000000000
def ep_8 : Nat := 0x600000000000000120000000000000014000000000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_8 : Nat → Nat := fun _ => 0
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_8 : Nat → Bool := dagCheckNodeV5 m_8 g_8 ep_8 1 1 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8 nh_8
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV5 m_8 g_8 ep_8 1 1 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) (nh_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 ch_8 = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → ch_8 i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV5 (kn_nil) rc_8 nc_8 (by decide +kernel)

def m_9 : Nat := 0xf0f000000000000
def s_9 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_9 : Nat := 0x107000000000000
def ep_9 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_9 : Nat → Nat := fun _ => 0
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_9 : Nat → Bool := dagCheckNodeV5 m_9 g_9 ep_9 1 1 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9 nh_9
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV5 m_9 g_9 ep_9 1 1 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) (nh_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 ch_9 = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → ch_9 i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV5 (kn_nil) rc_9 nc_9 (by decide +kernel)

def m_10 : Nat := 0x3300000033000000
def s_10 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_10 : Nat := 0x100000013000000
def ep_10 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_10 : Nat → Nat := fun _ => 0
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_10 : Nat → Bool := dagCheckNodeV5 m_10 g_10 ep_10 1 1 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10 nh_10
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV5 m_10 g_10 ep_10 1 1 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) (nh_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 ch_10 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → ch_10 i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV5 (kn_nil) rc_10 nc_10 (by decide +kernel)

def m_11 : Nat := 0xcc00cc
def s_11 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_11 : Nat := 0x4004c
def ep_11 : Nat := 0x480000000000000000000000000004000800000000000000000000000000040040
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
def cur_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_11 : Nat → Nat := fun _ => 0
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_11 : Nat → Bool := dagCheckNodeV5 m_11 g_11 ep_11 1 1 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11 nh_11
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV5 m_11 g_11 ep_11 1 1 1 bds_11 (dagTraceF m_11 s_11 3 f_11) (cur_11 0) (nh_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11 : treeBlockF 0 1 ch_11 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → ch_11 i = true := fun _ h1 h2 => treeBlockF_at nb_11 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagV5 (kn_nil) rc_11 nc_11 (by decide +kernel)

def m_12 : Nat := 0xcc000000cc00
def s_12 : List Nat := [0x440000004400, 0xc0000000c00, 0xcc00]
def g_12 : Nat := 0x40000004c00
def ep_12 : Nat := 0x480000000000000000000000000000000000000004000000080000000000000000000000040000004000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_12 : Nat → Nat := fun _ => 0
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_12 : Nat → Bool := dagCheckNodeV5 m_12 g_12 ep_12 1 1 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12 nh_12
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV5 m_12 g_12 ep_12 1 1 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) (nh_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 ch_12 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → ch_12 i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV5 (kn_nil) rc_12 nc_12 (by decide +kernel)

def m_13 : Nat := 0x2222000022220000
def s_13 : List Nat := [0x202000002020000, 0x22000000220000, 0x22220000]
def g_13 : Nat := 0x2000002220000
def ep_13 : Nat := 0x220000000000000000000000002000000200000000200000200000000000000000000000000000000000000
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_13 : Nat → Nat := fun _ => 0
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_13 : Nat → Bool := dagCheckNodeV5 m_13 g_13 ep_13 1 1 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV5 m_13 g_13 ep_13 1 1 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) (nh_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 ch_13 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → ch_13 i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV5 (kn_nil) rc_13 nc_13 (by decide +kernel)

def m_14 : Nat := 0x3030000030300000
def s_14 : List Nat := [0x1010000010100000, 0x30000000300000, 0x30300000]
def g_14 : Nat := 0x10000010300000
def ep_14 : Nat := 0x1020000000000000000000000010000000200000000000000000000000000000000000000010000010000000
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_14 : Nat → Nat := fun _ => 0
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_14 : Nat → Bool := dagCheckNodeV5 m_14 g_14 ep_14 1 1 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV5 m_14 g_14 ep_14 1 1 1 bds_14 (dagTraceF m_14 s_14 3 f_14) (cur_14 0) (nh_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 1 ch_14 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → ch_14 i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagV5 (kn_nil) rc_14 nc_14 (by decide +kernel)

def m_15 : Nat := 0xf00f0000f00f
def s_15 : List Nat := [0x500500005005, 0x300300003003, 0xf0000000f, 0xf00f]
def g_15 : Nat := 0x10070000500f
def ep_15 : Nat := 0x400800000000000000000000000000000000000000000000000000001002000000000000100400005000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb25935b2a73294c80f 7 127 3 7 6 63 9 511
def nh_15 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_15 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 7 (dagTraceF m_15 s_15 4 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 7 bds_15 (dagTraceF m_15 s_15 4 f_15) (cur_15 0) (nh_15 0) s_15 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 7 ch_15 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 7 → ch_15 i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0xcc330000cc33
def s_16 : List Nat := [0x441100004411, 0x3300000033, 0xc0300000c03, 0xcc33]
def g_16 : Nat := 0x41300004c33
def ep_16 : Nat := 0x482000000000000000000000000000000000000004020000080000000000000000000000041000004000
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cc_16_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8428408027657417407217207016846616606416406215a45a05a05625605415025005004c24c04a1462460270032001 0x106901fd00269201c24094681d53038a205124030680b0d0329205c240d280184c02c200283402848134d0221a0513009240100c0081203424058280b0c018980283403868050500a1001920020482a938532509a4611c84228f8431d07a360dc64155181e9b0092e0709409118101d00c36010337c8fee91ddb6379fc67384fe549bc752f81a4efb0fde61db88375a066a70bd30159e427200462b06c020b8000f 12 4095 5 31 10 1023 19 524287
def cc_16_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9866094650942508ca308c221791e0781e0709c0701b15d09e24090240901c870148050000000000 0xe030c020d8242c14d834e144dc3cd4346824b8341414b824c134bc4cb4445024fd4af946f53af1360925ec4ee84ae446d042cc3ec83ac436b0320825a24c9e40653434346244953c913469243044 10 1023 4 15 10 1023 16 65535
def cc_16_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xf01e0382700dc3a0f21640c81886d25a0b0350aa0521a4140632c41881102203a5740d89b0341642b0c0b000 0xc04cbe3cbc24ba1c88248b34b4449624ac340a14ac24b134ae4caa442824a634a03c9c34a0249c24a3349e4c9a44963c841c0a24962d842a94269225902488340a1488240a248b3486448424b33d833aef36eb35e534e24ede4ddc4cd24ace46ca45c244b842b63eb23da82d582aa42698258e248c1e821d 11 2047 5 31 9 511 16 65535
def cc_16_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9a09438c48a18815b75a05435404e34e04e036c3603222a42a02622412402211c31c01a11620a60a00a00a0005000000 0x112307f4c1f920849020a3080501f534454b1141c97d3a5b4a94d1a4b429192a2e467a8f91a3d8a4f47935894b6192585129f0467b0f96c3d7b0b9e82977089d42172080f01a030599044780f1281463111d83c49091c03d6d0e9a036660d58834740b9cc2d58074c01a53059441548051103450051c1346c1115c2c4f09110346b05110246b091b5346c111a82468091581c4e051993460131683c550b1342443071682d430a99026630958824 12 4095 5 31 10 1023 18 262143
def cc_16_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xe01b8741e61cc1791d93a0740e81c0b4254aa0530a60444880f11642c0504a01021842844088008410001000 0x9e0d27d44900d2742445081153460131b04414092994aa551a913ea34f5e935414c8f52a0849a884ea112a80469c10a6c367a0d4c82a9a09a641e41076554c8f8d20c348ed12423493492084484091b4207f0d23d247e09110348d05242408e8c230407d0d0c020880d01414870c010146d081fa347f4920c14444d20414 11 2047 5 31 10 1023 18 262143
def cc_16_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x8818808808807e57e07a27817617034564214013e13e03e03a23a03813233203203200f20c10a1081061041040040002 0x2c34be0f6d83abd0daf035bb0d1fc240b051fc340b0d2e144b70d2d824d9536d54ae051b7945db513684ed9137603ed60f7543c9c0eb4c36d10d730345c0cb1c2d340ab1426bf096e824b907ad41d5f8d2ba305f8e2b5247e092b634aed12b12484092cf4ab2d1ac64eb092abe46ab90a663e598f6a93da94d4892da8496903aa30e5ec36590c5ec269b09574149f0c1e024760d174387f0927814 12 4095 5 31 10 1023 18 262143
def cc_16_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xd4f50d429ca42639824281200801f1749765856058160454f23c0f0384a4280911c8701846014405 0xdf26670d2f049ba3edc1eeb8b67c55a826d212e68932c3a701ac60b62056ec297144d01a5f091fc498614d7a2480d328598424d422648730429a544d0262f8f320598024b70e3f8d3407b6e3acf1b670d7346992240b0a648d32e89943cc81a0d0931889862cc112618d304698944be26610f300696c1c 10 1023 4 15 9 511 17 131071
def cc_16_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xba0ba0ba09729419219018e18e08e08646326205e25455215204e24e04a24244204014003c2382361341077060003000 0x3d34e6ce9b029360322a5e3d80472ff8d55718bf94d7ea8a2a4f5f89abe84a7c892e4119b220b90367c06ae10d1be222e0302e850b8510be1e240340d048fa539f2a6b8d455aa84a64e90a9b0fd2a0724cf8119c622bdc3e50874f60d8d2190e82a7a84cf40796a0ebba3440848edd10d9223c52440068840913e183b9243f0487f091d80a1b34076c60eb100fa120e030738480b051cc20028145c478b8071c7a72e74d7949ab09252922bc24177c7aea8d5d2a6899457427ae54d5c8273684d7207ce30e5c019378316d860a50a8f8130f81a0482ce11319e122f414 12 4095 5 31 10 1023 19 524287
def cc_16_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xf417baf05e0bc1782d15a0ac5316604c090510a10c20803001f0be0782d11a0340680c093287008208400800 0x4a74a9468d2793a4d254964690485084da10932a83d4486a220b63e14c7825160431a132322044e348786912d121ca2441248b85116092169244c24894610a4d2171a43c14868290b482212043a30862810a4d110120441443a68104920c26414440a0491cd3a37a5463468ae851492a2323425468427d084ba0e1e8c8390f06b040c55216a18250782a60d115d181824c 11 2047 5 31 10 1023 19 524287
def cc_16_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xe41c0780700e01c02a7540a8140a32c608c1089f13e07c0f81d1305220400708e01c0380510a014020402000 0x492309f49b3d916391ecf2399dc6b208c65ea34bd367f09ae8114541ece8399c86a340c6651a4342498e890c4d220924d8289a8490b49264124c63085248e70d02e0a399440b2492d0f2581a068249bc9b269263122cd24199c7b308d65ea74bd3e84a4d2e13474248984595882fd0f5ca1a85415924610b492441248a349268910492461448424 11 2047 5 31 10 1023 19 524287
def cc_16_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xf05b97706c1d43a0740680d01796d15a0b4160682500a0130a604a1941205e33c0742e05b0b606c0d8162816 0x2a40c52814af6895a532b29e54418a48295cd12171a42e34ad47b598eab11b55e35ab46952490fc1254a34aa689534a2a29221024a60314a052991a52a34a6e8945532889e1752ca5831490528fa21fa343f469458f6891d50e36a146b418d2c9a6d874ab5e8d69d16cda25964eb249b638fac31ec812dafa555d49ab692d55245585b500aa9e14d3828a404d46096801217021 11 2047 5 31 10 1023 19 524287
def cc_16_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xd81d80b52b21b01ae1a64a60a41a408127e17c17c07c07826e54174003a33a03433403401cc1c01631601220c3082004 0x1804cbc69d64d36f7255ea49b9c8d64906e71b5e6359f29b33516389edfd358109aef1152e1edf839be86a9c0c6d91a5aa44b146162d12209217428420485f0f2f7a75eb4db968b61d0af3235ca45bc47d618f6529ec51359325b77495661ea44355805b760a6ea129a421b1479628f1d81a2342475a888c4d0d82224034b784972d3ac7a6dce4eb2c9b738fae51cdae32b4c63668c2e2a6c61459ea7b304d65096c4525b809aa11252822db8418087aea0d56416a2c25b64995849286125aa4caba4942092d11f59e3d9225b604aabc9357125ab248ae0b6a81553426a384b41092c5a256924a28490b490fc1258b44aca4944092169253024b068910492a61452c24 12 4095 5 31 10 1023 19 524287
def cur_16 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec ([]) (cc_16_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_16_10 (Nat.sub p 320)) (cc_16_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_16_8 (Nat.sub p 256)) (cc_16_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_16_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_16_5 (Nat.sub p 160)) (cc_16_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_16_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_16_2 (Nat.sub p 64)) (cc_16_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_16_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_16_0 : Nat → Nat := unpackHintV5 0xa00a8009e0a50a9402500920a480900a18a8602180840a1008209e0a7219c807009c006c1188a5c197005a09680561130a46189a00290002 0x15540554155510115440454114440501145144545 14 16383 6 63
def hc_16_1 : Nat → Nat := unpackHintV5 0xa22a60a8e29f907c09c0c6e09b806e01b806e017905c0940c4e093804e013804e00aa4280870c1c007001a08680180838a0c0800c0000000 0x5555455555515555555155555554114415555551555 14 16383 6 63
def hc_16_2 : Nat → Nat := unpackHintV5 0x90024008a19f0e7c01d867409d007401d007401c827009b826e01b806e01b806c09b006a09a0260212183a38d843600d803600c060a9800a 0x155551554555555555555554555555051554 14 16383 6 63
def hc_16_3 : Nat → Nat := unpackHintV5 0xaa0148327084b0c9018ecd1c84368a6910c8297862c0c4c308841082200434306410c80190032005e18a4610901e0c38106040a080c2000600000000 0x5555555455545555455155555555555555555555555555555555555555551555555555555555555555555 15 32767 6 63
def hc_16_4 : Nat → Nat := unpackHintV5 0xd603580d01b010be0ae0686c9e8c665198054494824828f0c3c00f003a08e803808a10260870a1c00682102810c040010002080800008000 0x55555455555555455515555555554555551555555555554515555 14 16383 6 63
def hc_16_5 : Nat → Nat := unpackHintV5 0xa8014e0a981510896311e3a34246808d011419dd3388c6b18c8397862b105408a80150028864c14921920117b2291846307460b8c101c14300880004 0x555555555555554555555051555555555555555555445551555555455155555555555555555555555555 15 32767 6 63
def hc_16_6 : Nat → Nat := unpackHintV5 0xdc568331195989e74c1a2210848023461718990463211108074832411402b0102080040020010006102080840400200100080002 0x1555555555555555554555555555555555555555555555555555555554 13 8191 5 31
def hc_16_7 : Nat → Nat := unpackHintV5 0xbc15721ae014fb2991926322c8420e7c20f609e032fb25528a8093c5248c4900900920023823f207c08e451c8038046628b46138c0d6812201050008 0x555155554551555555555555555555555545555555545551555555545555555555551451555155154555555555555555 15 32767 6 63
def hc_16_8 : Nat → Nat := unpackHintV5 0xd832d24b20a98ca602980a40a900a20a60a921a480900a18a8602180840a100820a0807e11d0a6e1988c62018025628da02a3078c1038010 0x555055051155555545551114015541555454111440155555555555555 14 16383 6 63
def hc_16_9 : Nat → Nat := unpackHintV5 0x89150829f083b0c6e20d031592280c50009e09285238647008c090451f0638187000dc1190a22403a2860508100f0412302010400080010002000010 0x15555455555554555550051155555554555111505555150144044545555455555555455 15 32767 6 63
def hc_16_10 : Nat → Nat := unpackHintV5 0xde0b702da0b602d803600d60b502cc22d18b012c00b002c00ac127108461f867e01f807e01f807a11b8c5e417805e015884e20f902660026 0x45555555555555555555555555555555555555555555555555541155 14 16383 6 63
def hc_16_11 : Nat → Nat := unpackHintV5 0xd91da242e19590cac1948428435002991d2241e19390c6c18d60984a30025b1482d0f441c0a34105e28a46118c17302038343030e040802180010000 0x5555555555554551555555555555554555555555555555455155455455555555515515455555555555555555555555555555555515555545 15 32767 6 63
def hc_16_12 : Nat → Nat := unpackHintV5 0x2 0x1 4 15 2 3
def nh_16 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_16_12 (Nat.sub p 384)) (hc_16_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_16_10 (Nat.sub p 320)) (hc_16_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (hc_16_8 (Nat.sub p 256)) (hc_16_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_16_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_16_5 (Nat.sub p 160)) (hc_16_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_16_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_16_2 (Nat.sub p 64)) (hc_16_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_16_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_16 : Nat → Nat × Nat := unpackForestF 0xbea6b7d0e6fa1a8063fbae9d75d36eb235d63ebaa4b750a6ea128063bb747d6e8e6dca6db84db78496e104031bdb24ca068d6a93281a2d9e3eb3c7b40d1281275024da047d62d12811ed8344a02555ed12809357344a024b568f6ad1d55a36ab46b568d2809254744a8a51528d2a2925002aa0053400a293a253234a48314a8d2920a50026a3e8940096831ed063aa0c6d418d6831a5002400c67399367322ce6399cc6b390e6721a8053f95c9b350a26a124ae4195c7b3209263184ae3595a7d2b136581e4b03495882014de3da547b468f49d1e92a3d234874490851228d2421247a428f0531e0940297c134e82695191323220413468b0511609209a14124a89849128c2092342a40878290a8c21a0a4294085a410a4d208a34112e8207b051320a224103100a4efc935f922bf2397e46afc535f8a2bf1350087ef4539e8a6bd0467a07cf40d9e8133d01e00876e3935e29238e4171c7aee491d7183b01475880e38d5c6a6b8d3d73848e6101c69ab8c3e71872010ddc2262d5466f898b5515b81f3703d5aa88b51396a26ad43e6ba88b50f56a1e350445a86cd25116a1ab343d6686ccd0d59a1a2d43464288c80f1921a320345a85ac61116a133014461868c00f1821a300345a84abb0f5761b2ec355d868b50916a0f2d9445b068b60916a0e8043354694a8d1951272a24a5448cacd115b1a2b12454484a84f5509aaa1250085e9952932a32653e4ca7a991393225264464ea889e0d13a12264424c86c99099320f0042b3d69c7ad292aa61eb4649a487ad08f5252324047a488c8c11a0a230403d48c7a4f4f496a2034438607a494f4251f640418287d8c1020a1f5403f2607e480fa9a1e8463d05c7a0a402139e03c20a6c760f0829a9cc2e3985a414d082271c1342089a41130d49a1a844358486a09082251a0242088c664d08222988263104a6209082221744c2e8785d090ba0e104422087c5a110821e955342a89856090aa221042d29868410989a9a14024268984e0909a22104252405a480989012920242084841078849a110242108842090820e80423162942c518589d0b1361609c2c12858230d5441a878360d06a1a0b0421607c2c0e8581b0b534168982e0905a220b0320083602938052509e4c13c8002918489e0913401484028f8051d07f480fe80028d838a60714401464165003292059300b8481610004a30413009a6810480221a040300126c021281a1202930058600a0d004230083a03868044800a10010240106c02064020b8000f 9 10
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 384 (dagTraceF m_16 s_16 6 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 384 bds_16 (dagTraceF m_16 s_16 6 f_16) (cur_16 0) (nh_16 0) s_16 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_0 : treeBlockF 0 32 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_1 : treeBlockF 32 64 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_2 : treeBlockF 64 96 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_3 : treeBlockF 96 128 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_4 : treeBlockF 128 160 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_5 : treeBlockF 160 192 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_6 : treeBlockF 192 224 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_7 : treeBlockF 224 256 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_8 : treeBlockF 256 288 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_9 : treeBlockF 288 320 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_10 : treeBlockF 320 352 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_11 : treeBlockF 352 384 ch_16 = true := by decide +kernel
theorem nj_16_1 : ∀ i, 0 ≤ i → i < 64 → ch_16 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_16_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_16_1 h1 h2)
theorem nj_16_2 : ∀ i, 0 ≤ i → i < 96 → ch_16 i = true := block_join nj_16_1 (fun _ h1 h2 => treeBlockF_at nb_16_2 h1 h2)
theorem nj_16_3 : ∀ i, 0 ≤ i → i < 128 → ch_16 i = true := block_join nj_16_2 (fun _ h1 h2 => treeBlockF_at nb_16_3 h1 h2)
theorem nj_16_4 : ∀ i, 0 ≤ i → i < 160 → ch_16 i = true := block_join nj_16_3 (fun _ h1 h2 => treeBlockF_at nb_16_4 h1 h2)
theorem nj_16_5 : ∀ i, 0 ≤ i → i < 192 → ch_16 i = true := block_join nj_16_4 (fun _ h1 h2 => treeBlockF_at nb_16_5 h1 h2)
theorem nj_16_6 : ∀ i, 0 ≤ i → i < 224 → ch_16 i = true := block_join nj_16_5 (fun _ h1 h2 => treeBlockF_at nb_16_6 h1 h2)
theorem nj_16_7 : ∀ i, 0 ≤ i → i < 256 → ch_16 i = true := block_join nj_16_6 (fun _ h1 h2 => treeBlockF_at nb_16_7 h1 h2)
theorem nj_16_8 : ∀ i, 0 ≤ i → i < 288 → ch_16 i = true := block_join nj_16_7 (fun _ h1 h2 => treeBlockF_at nb_16_8 h1 h2)
theorem nj_16_9 : ∀ i, 0 ≤ i → i < 320 → ch_16 i = true := block_join nj_16_8 (fun _ h1 h2 => treeBlockF_at nb_16_9 h1 h2)
theorem nj_16_10 : ∀ i, 0 ≤ i → i < 352 → ch_16 i = true := block_join nj_16_9 (fun _ h1 h2 => treeBlockF_at nb_16_10 h1 h2)
theorem nj_16_11 : ∀ i, 0 ≤ i → i < 384 → ch_16 i = true := block_join nj_16_10 (fun _ h1 h2 => treeBlockF_at nb_16_11 h1 h2)
theorem nc_16 : ∀ i, 0 ≤ i → i < 384 → ch_16 i = true := nj_16_11
theorem lb_16 : LowerBin m_16 s_16 g_16 7 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xf000f00000f000f0
def s_17 : List Nat := [0x5000500000500050, 0x3000300000300030, 0xf000f0, 0xf000000000f0]
def g_17 : Nat := 0x100000300070
def ep_17 : Nat := 0x1000000000400000000000000000000000000000000000001000003000200000100000000040
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb1e54b327d13969924c4a6000f 7 127 3 7 10 1023 13 8191
def nh_17 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_17 : Nat → Nat × Nat := unpackForestF 0x33eb2c33933233133000f 3 9
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 7 (dagTraceF m_17 s_17 4 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 7 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) (nh_17 0) s_17 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 7 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 7 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0xff00ff0000000000
def s_18 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_18 : Nat := 0x100150000000000
def ep_18 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_18 : Nat → List (Nat × Nat) := fun _ => []
def nh_18 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 0 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 0 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0x6060606060606060
def s_19 : List Nat := [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060]
def g_19 : Nat := 0x4000204060
def ep_19 : Nat := 0x20402000000040000040400000004000200020000000000000000000000000000000000000000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cc_19_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xc49807005e1bc160ec0580b0160291d20a41406805009c311620440804f85f03e07c0f81f03e06c8d801d001 0x8a38431a204e0fa68703c389c1d920d87868342f24160b0a8483030161011d2086803d3c1c980a08064702d20149a069202c8012380718498fe347716378519c14fe0276ed3a6c9bad4d95a66a92f5295a449d1a46783f321d980dca0664c2f24158d09c4846201f0e0d8205c0826000f 11 2047 5 31 10 1023 17 131071
def cc_19_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xf1f0f0c6c0b9b8b18d7a78786a6868685a2e2821202020202020040000000000 0xfc28fa39f631f136d53574395c31cd38c138ea4ce640d538e04cdc40ce30c030ce3cbc30c23cbd30d63eb23dd13ec932c43eb832b12ca3489f40983c9430 8 255 3 7 10 1023 16 65535
def cc_19_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a3468d1320c056a14282624080 0x13538989a4b0e25068fd387ca4480a23848f548889443491e268d644 7 127 3 7 10 1023 17 131071
def cur_19 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_19_2 (Nat.sub p 64)) (cc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_19_0 p) (Nat.blt p 32)
def hc_19_0 : Nat → Nat := unpackHintV5 0x8f2a3828e0234289221488029fc27d11ec47721b1661597485b1164453312d049111483f30d542c4894e2408884201074618283d20170002 0x0 14 16383 5 31
def hc_19_1 : Nat → Nat := unpackHintV5 0xa21500a78528a902470a2891028233f11f04f807c03d09e80f407a03449984c065272048f8474436218189942920c40410108004 0x0 13 8191 5 31
def hc_19_2 : Nat → Nat := unpackHintV5 0x149272468848e29b12e84d0728c214419019803000 0x0 11 2047 4 15
def nh_19 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_19_2 (Nat.sub p 64)) (hc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_19_0 p) (Nat.blt p 32)
def f_19 : Nat → Nat × Nat := unpackForestF 0x252712934941c4a0d00c7f1c288e12018ec0c6f0d288692018cc0a7e053b7e143c8e5e462f136029d37931bc80dc4c6e20014dd747cb93e671e2e4c9707cbe3c5e982e0c80a6cb12c0299814bc0a5697484ba0250f12860052702919f8e0fc687d383e9a010fcd4907138341e1a0d0087604372b24150b0a84804330217810ac76903b401c9e0e4c0084e2e3816900a4d00846041f020d839201c800e3807180105c0826000f 7 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 78 (dagTraceF m_19 s_19 5 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 78 bds_19 (dagTraceF m_19 s_19 5 f_19) (cur_19 0) (nh_19 0) s_19 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 32 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_1 : treeBlockF 32 64 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_2 : treeBlockF 64 78 ch_19 = true := by decide +kernel
theorem nj_19_1 : ∀ i, 0 ≤ i → i < 64 → ch_19 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_19_1 h1 h2)
theorem nj_19_2 : ∀ i, 0 ≤ i → i < 78 → ch_19 i = true := block_join nj_19_1 (fun _ h1 h2 => treeBlockF_at nb_19_2 h1 h2)
theorem nc_19 : ∀ i, 0 ≤ i → i < 78 → ch_19 i = true := nj_19_2
theorem lb_19 : LowerBin m_19 s_19 g_19 6 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xffff000000000000
def s_20 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_20 : Nat := 0x117000000000000
def ep_20 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_8, s_8, 4, g_8), (m_5, s_5, 4, g_5), (m_4, s_4, 4, g_4)]
def cc_20_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_20_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_20 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_20_1 (Nat.sub p 32)) (cc_20_0 p) (Nat.blt p 32)
def hc_20_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_20_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_20 : Nat → Nat := fun p => Bool.rec (hc_20_1 (Nat.sub p 32)) (hc_20_0 p) (Nat.blt p 32)
def f_20 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 43 (dagTraceF m_20 s_20 6 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 43 bds_20 (dagTraceF m_20 s_20 6 f_20) (cur_20 0) (nh_20 0) s_20 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_0 : treeBlockF 0 32 ch_20 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_1 : treeBlockF 32 43 ch_20 = true := by decide +kernel
theorem nj_20_1 : ∀ i, 0 ≤ i → i < 43 → ch_20 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_20_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_20_1 h1 h2)
theorem nc_20 : ∀ i, 0 ≤ i → i < 43 → ch_20 i = true := nj_20_1
theorem lb_20 : LowerBin m_20 s_20 g_20 7 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_8 (kn_cons lb_5 (kn_cons lb_4 (kn_nil))))) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xffff00000000
def s_21 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_21 : Nat := 0x155700000000
def ep_21 : Nat := 0x4200000000000004020000000000001002000000000000155400000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cc_21_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_21_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_21 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_21_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_21_0 p) (Nat.blt p 32)
def hc_21_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_21_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_21_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_21 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_21_2 (Nat.sub p 64)) (hc_21_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_21_0 p) (Nat.blt p 32)
def f_21 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 64 (dagTraceF m_21 s_21 5 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 64 bds_21 (dagTraceF m_21 s_21 5 f_21) (cur_21 0) (nh_21 0) s_21 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 64 ch_21 = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 64 → ch_21 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 64 → ch_21 i = true := nj_21_1
theorem lb_21 : LowerBin m_21 s_21 g_21 6 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xff00ff00000000
def s_22 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_22 : Nat := 0x17005700000000
def ep_22 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xf0f0f0f000000000
def s_23 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_23 : Nat := 0x10105000000000
def ep_23 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xf0f0f0f00000000
def s_24 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_24 : Nat := 0x107050700000000
def ep_24 : Nat := 0x400000000000006000200000000000000000000000001020002000000000104050400000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xcccccccc00000000
def s_25 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_25 : Nat := 0x4044400000000
def ep_25 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0x3333333300000000
def s_26 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_26 : Nat := 0x113111300000000
def ep_26 : Nat := 0x1000000000000012000200000000010200020000000000000000000000000110111000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xaa00aa00aa00aa
def s_27 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_27 : Nat := 0x200020022002a
def ep_27 : Nat := 0x20002800000000000000080000000000000000000200020000000800020002002200200000000000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x5050505050505050
def s_28 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_28 : Nat := 0x10105010105050
def ep_28 : Nat := 0x1000400000001040000040400010004000000000000000000000000000101000101000000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def nh_28 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x5555555500000000
def s_29 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_29 : Nat := 0x115155500000000
def ep_29 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_5, s_5, 4, g_5), (m_2, s_2, 4, g_2), (m_0, s_0, 4, g_0)]
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_29_1 (Nat.sub p 32)) (cc_29_0 p) (Nat.blt p 32)
def hc_29_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_29_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_29 : Nat → Nat := fun p => Bool.rec (hc_29_1 (Nat.sub p 32)) (hc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 43 bds_29 (dagTraceF m_29 s_29 6 f_29) (cur_29 0) (nh_29 0) s_29 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 ch_29 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 43 ch_29 = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_5 (kn_cons lb_2 (kn_cons lb_0 (kn_nil))))) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x666600006666
def s_30 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_30 : Nat := 0x44600004666
def ep_30 : Nat := 0x422000000000000000000000004200000020000004020000020000000000000000000000000000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9239209018c28c08a18a08817c67c07c07c07257207207207206a46a06816616036005c25c05a15a0581523276032001 0x11248201303e1a074140d078180d0340a060140da48191302e220403c0505803070140e80c1a0a82c14054260a0444c080780f0b01c0e01814020280749016260283403078040900c0a0101403a4805130061a0252d012543f4987a928e9241c09c3613464260c04515084290f8481e88c3c0f0741c0d82c1a84834068640c0b812168201e0103b778fee319d8d3faea67564be9695ce12781a46f00fdd419b842f6b056bd09d10119e81f340364105c02098000f 12 4095 5 31 10 1023 19 524287
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xd4323c83209b26094632795e0781e0655724d11240500400f12d0b02489020480110400882004401 0x684c5069f0b391f6e3dcc7988d6f19502d8854e899b12a624f03dd87790a4e2c6849bc9261e32342c582870b0e8a1ad42da05730a0c3c60498c92e264a3c5c6830f2c120c14b0297c92e265a3cac6938f04124e14a24931325223e348478209210a0814 10 1023 4 15 9 511 15 32767
def cc_30_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x7c57c07827427217016e16e06a26a06625e45c15c05825425215014e14e04a24a0462460460403384361341077060003 0x568d2fa996124941a4c05030797424a4265c0e1782088108e12574f23029543c0812584c2b24150308a12068d030794424a426500e1782088108c924b0f23829243c0812044823841181098984a482406114240e0e070732c9d9242c71f628eb046d7a32b6a75a50aca754d368497084b6789d38429a1d440da185c302d860f42065f824f411740835130a869002c 12 4095 5 31 10 1023 17 131071
def cc_30_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xf45e83c0f239e5382704c194320630c608c110620440805001f0b836c2b90590a0140188300600c018020802 0x1f53c46051f5247e8d1f14c4c0521e4e8690a163a848da0d4e8250a053e804e9fd367b4c9a52e094b5d42a740a50c26090850c166a05438146e08100143e09038286d0f11c146d091b9346c1316024070401d242e130403c1f0d1e54e78509dd3a764d9d52e744b5092502489cc4e72109c43e700e9bc366b0c9a82642095a41e020759e38668d18740574912c24 11 2047 5 31 10 1023 18 262143
def cc_30_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xd4189310620c0370ae05a1b41606634a194128250405800f09e03a1702c8c3b0600c01041082004000400000 0x143349f264f11160493634981e4b0d260492c24999a4b9325489263c0f16450711c49262d8a154909a444b20248c1e2385230488e248d9a459322849473d899d5dcdae66b6d34b42759136b8995845a621528fa8c7b442e9d16ce0b1ac5534269412c789034451c1e890e87c91fa401f28 11 2047 5 31 9 511 17 131071
def cc_30_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x9616976806236205c35c05c044c4404213e23453403403402a52621e41a21811801801610e40e00c1063060022020001 0x8d0734f4ed2d0b3e4ece90afa3e8e8f7353d804e58135cb4c7292dc5497044ec010afc3ea50f6fc2ebe0a6ec22b9086d820760691016b1132f03c92052c04cba0f24424b50facc3daf0f2b435ab0cae02eb70b6841d6e06a6c16990564014b5092801c98052cd34a40f27c2c970922c1ca40b62c2ab109ac025af092303c96052b534aa132782c95092303ca80523024a8092ad34aa132a42ca709230248d4d2904c93092803c470528024 12 4095 5 31 10 1023 18 262143
def cc_30_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xdc3b07606c0d43a07406047a4f01e0382700e01a13025c2b81512053c2780d11a02c4390608c010410810801 0xbc092e8348d08038188d4d2a84c0f0b16024e053b7d42de4fb753dbe4d62532774a93526dc13b6c42da0daf835d90b9c02ad80987822d707a241dd54e351348c0f34414c41334038ab0832524490532234cc5307d344809130146e083253c460531c3c470507e30c848318304505232348c4f30c14c45330938ab082352c 11 2047 5 31 10 1023 18 262143
def cc_30_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x8e08e08a28058008007e17647417407407026656604704604604604604602ae2a02a02a02a0281261241240012000000 0xfd8f186123ff4c55498fe4a1f892308347c8482ed11eca43e03829028f4491e89e144147b4982e531ea9e3cd3428048efd360126b4e3d7dc72fa8d5cd18bdd4d32a7af24e5e29aa093177882e00a982131e41a2782cef535be9d301363c2544e499de26bb83e6d874ed0d94c193b02e39054eb0985411042343f240104f1d3a73a34273c9ce6909af1f28e3d72a7ae44d4c696b8d297124a7b485bc1d374395f86ca30c57e1336825 12 4095 5 31 10 1023 19 524287
def cc_30_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xec7d8391720e03a8f31660c83902e25c0b8160ac0561ac1506434808c310610c20841081c28d618028412001 0x2391a47d4c848291b4f08c0a46d248e4691a532100a45d3c2302917492311a4594c8aa884c052201e43834882490e492231a43c4c86889090f210160381c85c68464908c924252d842550749a0c92c15248f47b198ea6d1b4d23598c692f53a5aa6ca54c93a8b2150a409f4793d8ea5d194b4f60ec501a8983312062180b42815820280d046040a2ab447fc91010e188123f524 11 2047 5 31 10 1023 19 524287
def cc_30_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c19a19819809428a55d75c056356050350050038c3803613222852802802801e51a21240e20c10c00c00a1024020001 0x12648238964712c63848550518c9a151249d0981f0d0b0125234ea3e854493a87214f23e8ec7b3f53a7ca14f53e9027b3d4ba7894cd9229a24331482761e9c0393006b390c5c816b14254203a5305658a64dd3c838292b5326a9e418149827d2e4f6549e4a13593265334ba64969f81d8c0351105a160ac14149824917062200a4ba348fa791a4b22c0c43c148fa5b1a4aa58934ad25952491b4f21c0a4a23492a99150621a0a46d3c918291b492469249a3492a9924062440a46d24 12 4095 5 31 10 1023 19 524287
def cc_30_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x8e072e7207207207207017004d24c04c04a14814804804613e43c13c01921801801421401401020c20a1081080042002 0x162936a91d4fa36b129b614faa09d5813690a64860b4b412a081daf8335e05454088403cae69d5bd0ab52756642a747d1e8f6a69d549399ea6d1e4c67a9353d257287aca0d4c616d6029ab84a6b0866e924d5348e2411c8d24aa603818260280f0b2ab2755242a9c7d528f6791ac6632a8a9d5050a9e9b4f135a725d194b50a16964254003b4d066980a87811a5071490d2369e51814a1299454e24c9046e348da794105284a650138 12 4095 5 31 10 1023 19 524287
def cc_30_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c29259209208e284584065064064064064064048e4804613e43c13c03c03822e52e02e02a2205200010000000000000 0xb827946492df265163492a997f062fc0a4083c6884901531a09a2a84cbd8597a092eda6dda41b729b484f6fa9cdf135a82635c4b68892c004d6987b790e6f01ab6c317485acf096eda6dda4dada7b434d6b296dd529ba24b21485d01eb38357305b730a6e412a9821b802925d12db245bd38a12496b092d71e50424b6e9925932809a5b028b5048f90f0ba0a3e14c2e2482e132ce1e59834b169b6e936911eda639b446b598c6c4a0d552a9fa4cf7134ca1ed9439b206a720c50e0e96c15 12 4095 5 31 10 1023 19 524287
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec ([]) (cc_30_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_30_10 (Nat.sub p 320)) (cc_30_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_30_8 (Nat.sub p 256)) (cc_30_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_30_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_30_5 (Nat.sub p 160)) (cc_30_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_30_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_30_2 (Nat.sub p 64)) (cc_30_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_30_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_30_0 : Nat → Nat := unpackHintV5 0xdc1b40cc042e86ba02e80ba02e80b612b88a6225907e61f807e01f807e01e066a39a806a019065639484520148052014804c189a60290002 0x115555555555555555555555551555515555545555551415115115115 14 16383 6 63
def hc_30_1 : Nat → Nat := unpackHintV5 0x9e44a2a218f8c64c3109804bc25c12d09604a0838c1b08d806823401a00d00680340124080840020010007080980020000000000 0x155555555555555555455555555555555555555555 13 8191 5 31
def hc_30_2 : Nat → Nat := unpackHintV5 0xda2b680d80b38ac42ae0cb802e00b60ad80b40a910a0128009e0a50a8a29f8c7e01f807c09f007a09e807a01b8c5e4148c46304b40a2000a 0x545445555555555505115555555555555555155155451555555555555 14 16383 6 63
def hc_30_3 : Nat → Nat := unpackHintV5 0x980930026004a867c64f219d05370c6818c4317062d825a04a6393462290430886010c0200638206a187190e001c0036086810a0c0a2814000490002 0x54555555451555545545555555555555555555555555155554555555555145555555555545555 15 32767 6 63
def hc_30_4 : Nat → Nat := unpackHintV5 0x87010a11e4c398c6b20d019a0034006800d00198233006210bc215882518431c8211040208041007c18ad3140623143a305c60b0215041c382060010 0x15555555555555555555555555555555555545555551415154555555555555555555 15 32767 6 63
def hc_30_5 : Nat → Nat := unpackHintV5 0xe032b34a42268a922220a7c31c0c5861582540948250093824c091082c60a822a00a022800a002800a00280068e1a0050604400040000000 0x55451455555555555555555555555555555555455555555555555155555 14 16383 6 63
def hc_30_6 : Nat → Nat := unpackHintV5 0x7b18ea31d0139826b20c8397082c86406480010001f823e047c00f411c0a33145250a01118a1d183a007010e001b042640442088010041628185000c 0x15555555555555555554555555555145555115555555554555555554144555554 15 32767 6 63
def hc_30_7 : Nat → Nat := unpackHintV5 0xa6014c02941500a9a1934026414a0a930526024c049028d150e31dd03a066c20cc317882c0c46488618f851e823c046c30c06148e212010c8143000a 0x55455515515515545144014105554555555455555551411045515555555555555555554515555554554 15 32767 6 63
def hc_30_8 : Nat → Nat := unpackHintV5 0xda1b30ec813200c803086be12f80be02f80ba12a9092623068c023008c023008811f0c6c41b006c019085c2131034603a60e003020228002 0x45555551555555555555555555555555555555555555555141554554 14 16383 6 63
def hc_30_9 : Nat → Nat := unpackHintV5 0x7f14f231cc634946804c62925a228840147820dc5188c2b183e607810e821c0436086810c8215101260201040007040e001c0038007000e000070000 0x555551551555555454515555555555555555555555555555555515555555555555 15 32767 6 63
def hc_30_10 : Nat → Nat := unpackHintV5 0xa2192092343440a87050c09fc73b905e64b619585280c4a18920920120103d0c6c38b880ab215002a00501098213002408345040a06080c00141000a 0x555551411055455155555555555545155555545545555555555545555555555555545155555445550511 15 32767 6 63
def hc_30_11 : Nat → Nat := unpackHintV5 0xa005362a5464a8094051e2a2463ca0760cdc41a0630105a189091200238242148209040208040047628d461a8034045e28a460ca0160c1c402060010 0x155155555155440141145055545555554555141105555155155155555155451005045055545555554 15 32767 6 63
def nh_30 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (0) (hc_30_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_30_10 (Nat.sub p 320)) (hc_30_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (hc_30_8 (Nat.sub p 256)) (hc_30_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_30_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_30_5 (Nat.sub p 160)) (hc_30_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_30_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_30_2 (Nat.sub p 64)) (hc_30_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_30_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_30 : Nat → Nat × Nat := unpackForestF 0xbf0317e052f09cde135bd0597a092f01cde03500c7f72936e494dc925b9053720940319dc014b7a7164936d5a65a828b5c796a092c91cd9235b3079660d2c81cd903500a7f5e536bc9f57936af0335e0540299d5f4eabe855793aaf2155c29ab84a014be992753242a647d4c8f698a753142a626d4c4ba980cd301500a57490e2921a4e74e9ce85460528a9c4e64e9cc8540532820a501389ca9d3950a72974e5299c87b3a1327218805279ba79048da6a9e412359925d324b6091a4c1248229d2e8d208a6ca9269524b2a49208a64a2348228b228d244a64881891a492205208a14113e8fa99044f6089746a348da491a5320896c56348ba49155322aa24101a82033040621b1a44124868990e4921a224101685c69040560a96c152a82a4d054960a924101400a4702052021c3c64d7e698fc4a1fb1e3f12478c72f18d5f2123e03878a9af3931e69e3d13c79a68f14e5e29a8043f7589aeb0f9d61b3ac2e7584c010cdc5a738b427149ce2909c49eb893571252e24940217b5d4e6ba84d74f9ae9eb5c4e6b884d70d9ae1735c266b83c010ada89c351345f69cbed09a20a340385f49cbe9097c9eb314c5f262be4b5929e3192063878c60c17c92b094c61828c24e17c272f8425f05cbe0a40213af03c44a6cba0f1129aadc2e5b85a894d16a122244e59a68891355e132bc2557848891315a9a2244553a68a71314e162a0245384889109121f2904c4487a890b93c9a280244f0989e1111216a242c4d868890992a9a260244a898960912a22224254805a900992012a40244484889079149a23024450988a091120e804233dc9c7b908f71d1ee363da9c7b508f69f1ed3a3da6c7c8d0fa921f14c3da640107cd2a71a54234a74694d8d2971a52d3489c69108d21f1a43a3486c6c4d0da121b04c3486469098d20f0041b33470668d0852710a422147c428e8c3a010a362fa98428c8ba12170382129c42508849d151302ba7854480aa1e150302126c50130a212140382109c42108841d115302587845480921e1143023040460408a12108362103c42064020b9002c0124c3e0b004928ec1e1d83a02490720a0084e1ba4802134660b0cc15198280213062920084515a482b130561e0b0141586802108041f0952413828251304a220083d010781f490420a07c4c0f868020e83a0a008360ba481a0502e26060140b888020d4260b04c1509828020d01c260383c070580e07004190082e050980a0d004168081e01a4806050062601014018680207402098000f 9 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 384 (dagTraceF m_30 s_30 6 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 384 bds_30 (dagTraceF m_30 s_30 6 f_30) (cur_30 0) (nh_30 0) s_30 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 64 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_2 : treeBlockF 64 96 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_3 : treeBlockF 96 128 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_4 : treeBlockF 128 160 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_5 : treeBlockF 160 192 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_6 : treeBlockF 192 224 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_7 : treeBlockF 224 256 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_8 : treeBlockF 256 288 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_9 : treeBlockF 288 320 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_10 : treeBlockF 320 352 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_11 : treeBlockF 352 384 ch_30 = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 64 → ch_30 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nj_30_2 : ∀ i, 0 ≤ i → i < 96 → ch_30 i = true := block_join nj_30_1 (fun _ h1 h2 => treeBlockF_at nb_30_2 h1 h2)
theorem nj_30_3 : ∀ i, 0 ≤ i → i < 128 → ch_30 i = true := block_join nj_30_2 (fun _ h1 h2 => treeBlockF_at nb_30_3 h1 h2)
theorem nj_30_4 : ∀ i, 0 ≤ i → i < 160 → ch_30 i = true := block_join nj_30_3 (fun _ h1 h2 => treeBlockF_at nb_30_4 h1 h2)
theorem nj_30_5 : ∀ i, 0 ≤ i → i < 192 → ch_30 i = true := block_join nj_30_4 (fun _ h1 h2 => treeBlockF_at nb_30_5 h1 h2)
theorem nj_30_6 : ∀ i, 0 ≤ i → i < 224 → ch_30 i = true := block_join nj_30_5 (fun _ h1 h2 => treeBlockF_at nb_30_6 h1 h2)
theorem nj_30_7 : ∀ i, 0 ≤ i → i < 256 → ch_30 i = true := block_join nj_30_6 (fun _ h1 h2 => treeBlockF_at nb_30_7 h1 h2)
theorem nj_30_8 : ∀ i, 0 ≤ i → i < 288 → ch_30 i = true := block_join nj_30_7 (fun _ h1 h2 => treeBlockF_at nb_30_8 h1 h2)
theorem nj_30_9 : ∀ i, 0 ≤ i → i < 320 → ch_30 i = true := block_join nj_30_8 (fun _ h1 h2 => treeBlockF_at nb_30_9 h1 h2)
theorem nj_30_10 : ∀ i, 0 ≤ i → i < 352 → ch_30 i = true := block_join nj_30_9 (fun _ h1 h2 => treeBlockF_at nb_30_10 h1 h2)
theorem nj_30_11 : ∀ i, 0 ≤ i → i < 384 → ch_30 i = true := block_join nj_30_10 (fun _ h1 h2 => treeBlockF_at nb_30_11 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 384 → ch_30 i = true := nj_30_11
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0x3030303030303030
def s_31 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_31 : Nat := 0x10101010301030
def ep_31 : Nat := 0x1020002000001000000000000010000000200020000000000000000000000000000000000010101010001000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xcccc0000cccc
def s_32 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_32 : Nat := 0x44400004c4c
def ep_32 : Nat := 0x480800000000000000000000004000000000000004000000080800000000000000000000044400004040
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x3333000033330000
def s_33 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_33 : Nat := 0x113000013330000
def ep_33 : Nat := 0x1220000000000000000000000012000000200000010200000200000000000000000000000110000010000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_10, s_10, 4, g_10), (m_14, s_14, 4, g_14), (m_13, s_13, 4, g_13)]
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_33_1 (Nat.sub p 32)) (cc_33_0 p) (Nat.blt p 32)
def hc_33_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_33_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_33 : Nat → Nat := fun p => Bool.rec (hc_33_1 (Nat.sub p 32)) (hc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_33 : Nat → Bool := dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 43 bds_33 (dagTraceF m_33 s_33 6 f_33) (cur_33 0) (nh_33 0) s_33 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 ch_33 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 43 ch_33 = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_10 (kn_cons lb_14 (kn_cons lb_13 (kn_nil))))) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xaaaa0000aaaa0000
def s_34 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_34 : Nat := 0x2000002220000
def ep_34 : Nat := 0x220000000000000000000000002000000200000000200000200000000020000022200000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x5555000055550000
def s_35 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_35 : Nat := 0x115000011150000
def ep_35 : Nat := 0x1000000000000000000000000014000000040000010400000004000001100000111000000000000000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0x5500550055005500
def s_36 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_36 : Nat := 0x100150011005500
def ep_36 : Nat := 0x1000400000001400000044000000000000000000010004000000000001001000110000000000000000000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xff000000ff00
def s_37 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_37 : Nat := 0x150000005f00
def ep_37 : Nat := 0x4a00000000000000000000000000000000000000040000000a0000001000000000000000150000005000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xff000000ff
def s_38 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_38 : Nat := 0x570000007f
def ep_38 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000005400000040
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xf0f00000f0f0
def s_39 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_39 : Nat := 0x105000005070
def ep_39 : Nat := 0x402000000000000000000000004000000020000000000000000000001000000000200000105000005040
def bds_39 : List (Nat × List Nat × Nat × Nat) := []
def cc_39_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_39_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_39 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_39_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_39_0 p) (Nat.blt p 32)
def hc_39_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_39_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_39_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_39 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_39_2 (Nat.sub p 64)) (hc_39_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_39_0 p) (Nat.blt p 32)
def f_39 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_39 : Nat → Bool := dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 64 (dagTraceF m_39 s_39 5 f_39) cur_39 nh_39
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 64 bds_39 (dagTraceF m_39 s_39 5 f_39) (cur_39 0) (nh_39 0) s_39 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 32 ch_39 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_1 : treeBlockF 32 64 ch_39 = true := by decide +kernel
theorem nj_39_1 : ∀ i, 0 ≤ i → i < 64 → ch_39 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_39_1 h1 h2)
theorem nc_39 : ∀ i, 0 ≤ i → i < 64 → ch_39 i = true := nj_39_1
theorem lb_39 : LowerBin m_39 s_39 g_39 6 :=
  lowerDagV5 (kn_nil) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0x333300003333
def s_40 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_40 : Nat := 0x111300001333
def ep_40 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000111000001000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0x3300330033003300
def s_41 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_41 : Nat := 0x100110013001300
def ep_41 : Nat := 0x1200020000001000000000000000000000000000010000000200020000000000000000000100110010001000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xcc00cc00cc00cc00
def s_42 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_42 : Nat := 0x40000004c00
def ep_42 : Nat := 0x48000000040000004c000000000000000000000004000000080000000000000000000000040000004000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xf000f000f000f000
def s_43 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_43 : Nat := 0x100010005000
def ep_43 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000100010005000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xcc00cc00cc00cc
def s_44 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_44 : Nat := 0x400440004004c
def ep_44 : Nat := 0x800000040000000480000000000000000000400000004000800000000000000000004004400040040
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xffff0000
def s_45 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_45 : Nat := 0x13370000
def ep_45 : Nat := 0x240000000000000204000000000000133200000000000010040000
def bds_45 : List (Nat × List Nat × Nat × Nat) := []
def cc_45_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_45_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_45 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_45_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_45_0 p) (Nat.blt p 32)
def hc_45_0 : Nat → Nat := unpackHintV5 0xa142548910a03a70c952850a142240810203460c1220405080400000 0x0 7 127 2 3
def hc_45_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3870c983054a1120344881020405081020402 0x0 7 127 2 3
def hc_45_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_45 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_45_2 (Nat.sub p 64)) (hc_45_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_45_0 p) (Nat.blt p 32)
def f_45 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_45 : Nat → Bool := dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 64 (dagTraceF m_45 s_45 5 f_45) cur_45 nh_45
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 64 bds_45 (dagTraceF m_45 s_45 5 f_45) (cur_45 0) (nh_45 0) s_45 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 ch_45 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 64 ch_45 = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 64 → ch_45 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 64 → ch_45 i = true := nj_45_1
theorem lb_45 : LowerBin m_45 s_45 g_45 6 :=
  lowerDagV5 (kn_nil) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff00ff
def s_46 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_46 : Nat := 0x37007f
def ep_46 : Nat := 0x480000000000000000000000000004000800000000003200200000000000040040
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xf0f0f0f0
def s_47 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_47 : Nat := 0x10305070
def ep_47 : Nat := 0x40400000000000200020000000000000000000000000103000200000000010005040
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
def cur_47 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_47 : Nat → Nat := fun _ => 0
def f_47 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 1 (dagTraceF m_47 s_47 3 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 1 bds_47 (dagTraceF m_47 s_47 3 f_47) (cur_47 0) (nh_47 0) s_47 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47 : treeBlockF 0 1 ch_47 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 1 → ch_47 i = true := fun _ h1 h2 => treeBlockF_at nb_47 h1 h2
theorem lb_47 : LowerBin m_47 s_47 g_47 4 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xcccccccc
def s_48 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_48 : Nat := 0x44c4c
def ep_48 : Nat := 0x4c480000000000040000000000000004080800000000000000000000000000044040
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xff000000ff000000
def s_49 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_49 : Nat := 0x100000013000000
def ep_49 : Nat := 0x1200000000000000000000000000000000000000010000000200000001000000130000000100000010000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xff000000ff0000
def s_50 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_50 : Nat := 0x17000000370000
def ep_50 : Nat := 0x20000000000000000000000000000000000000000600000004000000120000003200000014000000040000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xf000f000f000f0
def s_51 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_51 : Nat := 0x10005000300070
def ep_51 : Nat := 0x20002000000040000000400000000000000000000000000000000000100000003000200010005000000040
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
def cur_51 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_51 : Nat → Nat := fun _ => 0
def f_51 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_51 : Nat → Bool := dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 1 (dagTraceF m_51 s_51 3 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 1 bds_51 (dagTraceF m_51 s_51 3 f_51) (cur_51 0) (nh_51 0) s_51 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51 : treeBlockF 0 1 ch_51 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 1 → ch_51 i = true := fun _ h1 h2 => treeBlockF_at nb_51 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 4 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xf0f00000f0f00000
def s_52 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_52 : Nat := 0x10000010300000
def ep_52 : Nat := 0x1020000000000000000000000010000000200000000000000000000000100000103000000010000010000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xf0f00000f0f0000
def s_53 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_53 : Nat := 0x107000003070000
def ep_53 : Nat := 0x200000000000000000000000006000000040000000000000000000001020000030200000104000000040000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x4444444444444444
def s_54 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_54 : Nat := 0x4044400044444
def ep_54 : Nat := 0x400000000440000044400004004000040000000404000004000000000000000000000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x55550000aaaa
def s_55 : List Nat := [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa]
def g_55 : Nat := 0x155500000a2a
def ep_55 : Nat := 0x40000000200000040000000a0800001000000000200000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := []
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a19343061234349263d88d5d2a549882a109800f 7 127 3 7 10 1023 14 16383
def nh_55 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_55 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4ce3469210a884c00f 3 10
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 10 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 10 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 10 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 10 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_nil) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xa0a0a0a0a0a0a0a
def s_56 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_56 : Nat := 0x2000202020a0a
def ep_56 : Nat := 0x2000a0800000000000008080002000200000000000000000000000000020002020200000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := []
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_56 : Nat → Nat := fun _ => 0
def f_56 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 1 (dagTraceF m_56 s_56 3 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 1 bds_56 (dagTraceF m_56 s_56 3 f_56) (cur_56 0) (nh_56 0) s_56 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 1 ch_56 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 1 → ch_56 i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 4 :=
  lowerDagV5 (kn_nil) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0x5a5a00005a5a
def s_57 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_57 : Nat := 0x105200005a5a
def ep_57 : Nat := 0x4a0800000000000000000000004200000000000000000000000000001002000000000000000000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := []
def cur_57 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1ec351f4250f42b27d8d5ad5951d1540f 7 127 3 7 6 63 10 1023
def nh_57 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_57 : Nat → Nat × Nat := unpackForestF 0xfa75fa1b4ca5d5a2b0aa0f 3 6
def ch_57 : Nat → Bool := dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 10 (dagTraceF m_57 s_57 4 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 10 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) (nh_57 0) s_57 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57 : treeBlockF 0 10 ch_57 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 10 → ch_57 i = true := fun _ h1 h2 => treeBlockF_at nb_57 h1 h2
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV5 (kn_nil) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xc0c0c0c0c0c0c0c
def s_58 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_58 : Nat := 0x4040400040c0c
def ep_58 : Nat := 0x8080000040000000c080004000000040000000000000000000000000000000000000004040400040000
def bds_58 : List (Nat × List Nat × Nat × Nat) := []
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_58 : Nat → Nat := fun _ => 0
def f_58 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 1 (dagTraceF m_58 s_58 3 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 1 bds_58 (dagTraceF m_58 s_58 3 f_58) (cur_58 0) (nh_58 0) s_58 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 1 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 1 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 4 :=
  lowerDagV5 (kn_nil) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x55aa000055aa
def s_59 : List Nat := [0xaa000000aa, 0x112200001122, 0x50a0000050a, 0x55aa]
def g_59 : Nat := 0x15020000552a
def ep_59 : Nat := 0x402800000000000000000000000000000000000004020000000800001002000000200000000000000000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cc_59_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8e08a28626706606416406216206206205e25e05e05c15c05a15245205205204e24e04e04c14c04a142442026e032001 0x1e4d00a0c07d280e8583d928751d0d54e192943151860a10ad3e14274274d84c990092d1289421118401d0703601042130c012100442407838110d01e1a04d4409078100d01c1601c3402838070900a1202534040980611008160694a0ca8c184e82e9b0092d0b09c151282823034420607c0b0e8141b00c320105b7c8fee91ddb6379fc67324ee5499c4d2b81a46fb0fde61db88375a066a70bd30159e427200461b07c02098000f 12 4095 5 31 10 1023 19 524287
def cc_59_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x8cbf1f0f16a34184c05ca552090412010080391c0d245201006430180c052280d0281001 0xfc24da4c39249044f818f034b23c11247c34ec18dd288c24de34e638e234d94839388844d13ccd34b5287824b634be4cba44b13811287434a94ca5443c148d243c289138883c1414 9 511 3 7 10 1023 16 65535
def cc_59_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xf01e0382700dc3a0f40661c4588300e00bc351690d20a4148242c4288110210ba4740d89b0341642b0c0b000 0xc04cbe3cbc2cba1c88248b34b444a02cb034aa3ca634aa24a624ad34a84ca444a03c841c0a24a02d842a9e269c259a2492340a1c92249734944c9044082c88340a1c88240a248b348644842cb33d833aef36eb35e534e24ede4ddc4cd24ace46ca45c244b842b63eb23dae2ea22d982c8e2506228c1e821d 11 2047 5 31 9 511 16 65535
def cc_59_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9a09438c48a18815b75a05435404e34e04e036c3603222a42a02622412402211c31c01a11620a60a00a00a0005000000 0x112307f4c1f920849020a3080501f534454b1141c97d3a5b4a94d1a4b429192a2e467a8f91a3d284e62931874a6192185129f0467b0f96c3d7b0b9e82977089d42172080701e170499044780f13c1c63111d83c4e0b1c03d6d0e9a036660d58834740b9cc2d58079581d4d0712c1509049103455071c1346c111502c4a09110346b07110246b091b5346c111a82c680914c1c49051993460131683c520b1202443071682d430a99026630958824 12 4095 5 31 10 1023 18 262143
def cc_59_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xe01b8741e61cc1791d93a0740e81c0b4254aa0530a60444880f11642c0580910e21822844088008410001000 0x9e0d27d44900d2742c45081153460131b044040b2994aa551a913ea34f5e935414c8812e1848a884ea112a80469c10a6c367a0d6682e0b08a641e4107655408f8d20c348ed124234934a2084484091b4207f0d23d287e09110348d07242408e8c230407d0d22434050707c2c8806024106d081fa347f4920c18444d20418 11 2047 5 31 10 1023 18 262143
def cc_59_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x8828808808617e47e07a27817617034564214013e13e03e03a23a03813233203203200f20c10a1081061041040040002 0xbc0903c1cbc0d2f944bd0f2ec340e0b1fc240f071fc340f0d2e144b70d2d82cd9536d54ae051b7945db513684ed9137603ed60f7543c9c0eb4c36d10d730345c0cb282ec40b6fc2cba0943422b907ad41d5f8d2ba305f8e2b5287e092b634aed12b12884092cf4ab2d1ac64eb092abe46ab90a663e598f6a939a94c6a12926486903aa30e5ec36590c5ec269b09574149f0c1e024760d174387f092781c 12 4095 5 31 10 1023 18 262143
def cc_59_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0f40d028ca0253942327d1f07c1e1709665455054150415003c4d2340c1300b1194511405014005 0x6f9333869822cdd1f6e0f75c5b3e2ad413690973449961ec90ee0072f82a2612b8a2680d30c58fe24c80e6bd1240698e2cbd126a11318397814d2a2681317c798a2cbb125b871fc69a03db71d678db386b9a34cb22640b318499034c61a64d130c998e3cc51a5b0703c69863db61d610db046b8034 10 1023 4 15 9 511 17 131071
def cc_59_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xba0ba0ba09729419219018e18e08e08646326205e25455215204e24e04a24244204203e23a2381361341077060003000 0x3d34e6ce9b029360322a5e3d80472ff8d55718bf9497ea82fc4e46098be84a7c892e4119b220b90367c06ae10d1be222e0302e850b8510be1e2403407058fa539f2a6b8d455aa84a64e90a9b0952e0d244f8119c622bdc3e50874f60d8d2193d42e0a844f40796a0ebba3440848edd10d9223c52840068840913e183b9283f0487f091d80e1b34076c60eb100fa123a02407838240b1ce0c04c105c478b8071c7a72e74d7949ab09252922bc24177c7aea8d464a4ba54173272e54c5c8273684d7207ce30e5c019378316d860a50a8f8130841e0c824e11319e123081c 12 4095 5 31 10 1023 19 524287
def cc_59_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0599730660c4588310620bc5516a0350680c8590320640b89702c1580b0150a244408811006e08208400800 0x2409a47c3891c8922522169c484388f0691c062360a224241e038884d0769645c4c8b088040b253a54a34692495068ca3aa74694a8ca8d1850a0c96aa83d4386a3a0b4500ec54198a02a0b0461a984312c848290c8d2131a4374485a590a062100a44b4a88e8d068ea20a743d4a8728d0750a0c96aa43d4306a260760a0cc10150182260d115d181824c 11 2047 5 31 10 1023 19 524287
def cc_59_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xf01d0b81700e01b0b12e20c4178aa2d406a0d0190b20640c81903202dc580911012003843202200200000000 0x93c713c4f218944e8249d469260a279a24953885a513b0a272123a0341f838e75107c964d83c9a8680e0b27da6cf74596c85248ea709f4693a9ba6d0f4ca5a96bf84d7308a3d0b4640ecd0199982a150461a984c74d9868b2d92a5e9f4613a9726d074ca5a96bf44d7288a30076580ccac1506823278e2469e431249304927d1245264953c85a490c4a2401247c34 11 2047 5 31 10 1023 19 524287
def cc_59_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xf41e07b0f41e81d03a06a5cc5792d15a0b0360282500a0130a604a1941205e33c0742e05b0b606c0d8162816 0x57b44864690c8d2b91ed6e3aad46d598d6b11a4312ca502956d12169654418a4829534a0fc1254e34aa689524a2a29221024a60314a052991a52a34a6e8945532889e1752ca5831490528fa21fa343f469458f6891d50e36a146b418d2c9a6d874ab5e8d69d16cda25964eb249b638fac31ed7d2aaea53574a2aa9341d215585b500aa9e14d3828a404d46096801217021 11 2047 5 31 10 1023 19 524287
def cc_59_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xda1da0b72b41b21b01a84a80a61a608328017e17e07e07a27054374203c33c03633603601ec1e01831801420e30a2005 0xc0265e34eb269b7b92af524dce46b2483738daf31acf94998a837f4e63098c084d7788a970f6fc1cdf4354e0636c8d2d52258a30b16890b4a0ba14210242f8797bd3af5a6dcb45b0e857991ae522de23eb0c7b294e62498ddd2987a42b30f5221aac02dbb05375094d210d8a3cb1478ec0d11a123ad44462686c111201a5bc2cb969d63d36e7275964db9c7d728e6d7195a631b34611a526e2a0cf53998263284a62290dc04d5089294116dc20c043d7506ab20b51612db24cad25143092d52656528a1049688facf1ed812aaf253584a2ac93435215705b540aa9a1351c25a084962d12b89451424862507e092c5a256d28a2049530a2981258344ae4995b8f2a41452c24 12 4095 5 31 10 1023 19 524287
def cur_59 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec ([]) (cc_59_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_59_10 (Nat.sub p 320)) (cc_59_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_59_8 (Nat.sub p 256)) (cc_59_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_59_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_59_5 (Nat.sub p 160)) (cc_59_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_59_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_59_2 (Nat.sub p 64)) (cc_59_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_59_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_59_0 : Nat → Nat := unpackHintV5 0xe403882d82ae20ae2a90a9a2a40a8041f827231c027001c007001c007001c00604178252314025001400500140050014004a189a40290002 0x451451100505515555155555455555554555541555450440514515115 14 16383 6 63
def hc_59_1 : Nat → Nat := unpackHintV5 0xe45a2b40662b95702d15a0b053aa704e0985031f13e0784f01d130a600c017122c404698b21602842a823004 0x15515545515555154555544114510 11 2047 4 15
def hc_59_2 : Nat → Nat := unpackHintV5 0x86021808019c8e7201b066a09a02660998066019806601902640188260096084060f823e00f803e00f803038b042c00b002c009860098000 0x1155545545555555555555551555554505 14 16383 6 63
def hc_59_3 : Nat → Nat := unpackHintV5 0xaa0148327084b0c9018ecd1c84368a6910c8297862c0c4c308841082200434306410c80190032005e18a4610901e0c38106040a080c2000600000000 0x5555555455545554551555555555555555555555555555555555555555554555555555555555555555555 15 32767 6 63
def hc_59_4 : Nat → Nat := unpackHintV5 0xd603580d01b010be0ae0686c9e8c665198054494824828f0c3c00f003a08e803808a102608980240868a102810c040010002080800008000 0x115555515555555545155555555545555551555555555115555555 14 16383 6 63
def hc_59_5 : Nat → Nat := unpackHintV5 0x96052c025804b0096011e3a34246808d011419dd3388c6b18c8397862b105408a80150028864e0c922920117b2291846307460b8c101c14300880004 0x1555554555555141555555555555555555445515555554551555555555555555555555555555 15 32767 6 63
def hc_59_6 : Nat → Nat := unpackHintV5 0x7f29e4c73319d8603974655414c451111583f30dd03418c843200b882a20890166054214084c213004c013004c0120848011084020c20018 0x555555555555555555155555555555555555555555555555555555554555555555 14 16383 5 31
def hc_59_7 : Nat → Nat := unpackHintV5 0xbe0d722ae014fb2991926322c8420e7c20f609e032fb25528a8093c5248c4900900920023823f207c08f801e8238146628b46138c0d6812201050008 0x551555545515555555555555555555555551555555554515555555545555555554455551555151545555555555555555 15 32767 6 63
def hc_59_8 : Nat → Nat := unpackHintV5 0x8104f829f003e007b04ea31d013a007304dc29a062c2053149c2918822823f187c08f801f003e007c00f801f003b0c6640b460da415181e302070010 0x45555555155554404405154555455555554151555555510405555555555555555 15 32767 6 63
def hc_59_9 : Nat → Nat := unpackHintV5 0xf61bb0aea0ba80ea03a02de2b48cd203402c62ae8c9a8240a8629d906a31906544120c249078614284041000382042808200080000000000 0x145151555554555540451014545555155555505455555441550155145101554 14 16383 6 63
def hc_59_10 : Nat → Nat := unpackHintV5 0xdc0b682da03680d80b582ce22d98b40ad00b012c00b002c00ac127108461f867e01f807e01f807a11b8c5e417805e015884e20f902660026 0x15555555555555555555555555555555555555555555555555510555 14 16383 6 63
def hc_59_11 : Nat → Nat := unpackHintV5 0xda1da442e59598cad194a4288350829a1d2441e59398c6d18d80988a30825c1484d0f841c8a35106028a86120c18302238383038e050804180410002 0x15555555555515455555555555555551555555555555551545555155155555555514551555555555555555555555555555555555455555514 15 32767 6 63
def hc_59_12 : Nat → Nat := unpackHintV5 0x2 0x1 4 15 2 3
def nh_59 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_59_12 (Nat.sub p 384)) (hc_59_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_59_10 (Nat.sub p 320)) (hc_59_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (hc_59_8 (Nat.sub p 256)) (hc_59_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_59_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_59_5 (Nat.sub p 160)) (hc_59_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_59_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_59_2 (Nat.sub p 64)) (hc_59_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_59_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_59 : Nat → Nat × Nat := unpackForestF 0xbea737d0e6fa1a8063fbae9d75d36eb235d63ebaa53750a6ea128063bb747d6e8e6dca0db84db78596e104031bdb24ca068d6a93281a2d9e3eb3c7b40d1281275024da047d62d12811ed8344a02555ed128094d623dac475588dab11ad6234a025156d12809354744a9c69514a2a2925002aa0053400a293a253234a48314a8d2920a50026a3e8940096831ed063aa0c6d418d6831a5002400c6733d3667a2ce7449c8513a8d272124cd3e99a6d350f26a1a4cc199982a014ee57a6caf4595a7d2b4da5696cac199582a014ce29a54534692e89260924a9e4524a8f4891e5223c1c47d348f8711e0d228a746c188d8291452a28a3451428b09916112280cc501500a5704d2a09a34114e822950451a11a2432348425908062131a4201482285044b6080cc101500a46fc935f922bf2397e46afc525f8a0bf1390087ef4539e8a6bd0467a07cf40d9e8173d01e00876e3935e29438e4171c7aee4a1d7183b01c75880e38d5c6a0ba02473830e34e5c698b8c3e71872010ddc2262d5466f898b5515b81f3703d5aa88b51396a26ad43e6ba88b50f56a1e350445a86cd25116a1ab343d6686ccd0d59a1a2d43465888b50b98aa23203462878c60d18a1a2d42d6007ac00d9801ab00345a858bb511761e2f0345d868b50956a0f2d9445b068b60b16a0e8043354694a8d1951272a24a5448cacd115b1a2b12854484a84e55098aa1290085e9952932a32653e4ca7a991393225264464ea889e0d13a16264424c86c990b9320f0042b3d69c7ad292aa01eb4649a507ad08f5252324047a508c8c11a0e230403d48c7a4c5121a220183d2527a484f4251f640418307d8c1020c1f5403f2607e480fa9a1e8463d05c7a0a402139e03c20a6c760f0829a9cc2e3985a414d082271c1342089a41130d49a1a844358486a0b082251a0242088c664d08222988263104a6209082221744c2e8785d0b0ba0e104422087c5a110821e960342085c524d0aa121484c298485211082169342d2684c4d0949a121042c24268481309212120442084a41078849a1102421088420b0820e804231f8483e06039250f0341d8301c8e86d1c0da341bc683652038a70cd3c19a681c52838a307142164982c9105b1a0b1380e27c2953052a20713a0e26c1c4c838250893811a48220f038230703a0ea501e4d03a16070360083e0252804a30093a0126c02138042500846072880e0f0221a03834078680e0b004210083e01074020d8089a0104c03848041100a120102c01064020b402098000f 9 10
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 384 (dagTraceF m_59 s_59 6 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 384 bds_59 (dagTraceF m_59 s_59 6 f_59) (cur_59 0) (nh_59 0) s_59 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_0 : treeBlockF 0 32 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_1 : treeBlockF 32 64 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_2 : treeBlockF 64 96 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_3 : treeBlockF 96 128 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_4 : treeBlockF 128 160 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_5 : treeBlockF 160 192 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_6 : treeBlockF 192 224 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_7 : treeBlockF 224 256 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_8 : treeBlockF 256 288 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_9 : treeBlockF 288 320 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_10 : treeBlockF 320 352 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_11 : treeBlockF 352 384 ch_59 = true := by decide +kernel
theorem nj_59_1 : ∀ i, 0 ≤ i → i < 64 → ch_59 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_59_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_59_1 h1 h2)
theorem nj_59_2 : ∀ i, 0 ≤ i → i < 96 → ch_59 i = true := block_join nj_59_1 (fun _ h1 h2 => treeBlockF_at nb_59_2 h1 h2)
theorem nj_59_3 : ∀ i, 0 ≤ i → i < 128 → ch_59 i = true := block_join nj_59_2 (fun _ h1 h2 => treeBlockF_at nb_59_3 h1 h2)
theorem nj_59_4 : ∀ i, 0 ≤ i → i < 160 → ch_59 i = true := block_join nj_59_3 (fun _ h1 h2 => treeBlockF_at nb_59_4 h1 h2)
theorem nj_59_5 : ∀ i, 0 ≤ i → i < 192 → ch_59 i = true := block_join nj_59_4 (fun _ h1 h2 => treeBlockF_at nb_59_5 h1 h2)
theorem nj_59_6 : ∀ i, 0 ≤ i → i < 224 → ch_59 i = true := block_join nj_59_5 (fun _ h1 h2 => treeBlockF_at nb_59_6 h1 h2)
theorem nj_59_7 : ∀ i, 0 ≤ i → i < 256 → ch_59 i = true := block_join nj_59_6 (fun _ h1 h2 => treeBlockF_at nb_59_7 h1 h2)
theorem nj_59_8 : ∀ i, 0 ≤ i → i < 288 → ch_59 i = true := block_join nj_59_7 (fun _ h1 h2 => treeBlockF_at nb_59_8 h1 h2)
theorem nj_59_9 : ∀ i, 0 ≤ i → i < 320 → ch_59 i = true := block_join nj_59_8 (fun _ h1 h2 => treeBlockF_at nb_59_9 h1 h2)
theorem nj_59_10 : ∀ i, 0 ≤ i → i < 352 → ch_59 i = true := block_join nj_59_9 (fun _ h1 h2 => treeBlockF_at nb_59_10 h1 h2)
theorem nj_59_11 : ∀ i, 0 ≤ i → i < 384 → ch_59 i = true := block_join nj_59_10 (fun _ h1 h2 => treeBlockF_at nb_59_11 h1 h2)
theorem nc_59 : ∀ i, 0 ≤ i → i < 384 → ch_59 i = true := nj_59_11
theorem lb_59 : LowerBin m_59 s_59 g_59 7 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0x5555555555555555
def s_60 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_60 : Nat := 0x115155511155555
def ep_60 : Nat := 0x1000400000001440000044400014004000040000010404000004000001101000111000000000000000000000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) (nh_60 0) s_60 7 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 7 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV5 (kn_cons lb_29 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xff00ff00ff00ff00
def s_61 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_61 : Nat := 0x100150013005f00
def ep_61 : Nat := 0x12004a000000140000004c0000000000000000000100040002000a0001001000130000000100150010005000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 5, g_43), (m_49, s_49, 5, g_49), (m_37, s_37, 5, g_37), (m_18, s_18, 5, g_18), (m_36, s_36, 5, g_36), (m_42, s_42, 5, g_42), (m_41, s_41, 5, g_41), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3)]
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV5 0x119 0x339f 3 7 1 1 6 63 7 127
def nh_61 : Nat → Nat := unpackHintV5 0x815900810000 0x2673cd6f7ac38c9919c0180f39d770e2c79333231319c6b1bc60c69 16 65535 8 255
def f_61 : Nat → Nat × Nat := unpackForestF 0x339f 1 6
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 3 7 bds_61 2 (dagTraceF m_61 s_61 7 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 3 7 2 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) (nh_61 0) s_61 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 2 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 2 → ch_61 i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV5 (kn_cons lb_43 (kn_cons lb_49 (kn_cons lb_37 (kn_cons lb_18 (kn_cons lb_36 (kn_cons lb_42 (kn_cons lb_41 (kn_cons lb_1 (kn_cons lb_3 (kn_nil)))))))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xf0f0f0f0f0f0f0f0
def s_62 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_62 : Nat := 0x10105010305070
def ep_62 : Nat := 0x1020402000001040000040400010004000200020000000000000000000101000103000200010105010005040
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_14, s_14, 4, g_14), (m_43, s_43, 5, g_43), (m_39, s_39, 6, g_39), (m_3, s_3, 4, g_3), (m_47, s_47, 4, g_47), (m_51, s_51, 4, g_51), (m_19, s_19, 6, g_19), (m_17, s_17, 5, g_17)]
def cc_62_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x880c20a1010808403e11e82f407613b01d02e80720b90198ccc06603109802b045802c01504a805402a0140490448023040c4001 0x54340a2881e0903922049440da481a0901e2605d280709815050269e0623b0b466144ec2499845230687c0f4e41c98834240ec961990c209a0304e02a88094d00da901652056be08d4c0eaf011360106d67d3ecba5d7f47ae6875b93eb125d3e47a2c87368fe651dcba37954672353a42a5c79438a285004edda99ba52b73a46e113db225b1847540868e0fd141d9fc373b0666d0bcc61587c27058460307c02098001f 13 8191 6 63 10 1023 19 524287
def cc_62_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xdc1b83516a0d03a0340661cc190720621997302604638c1105f1bc1742e81d03a0740e0572ae05c0b8141814 0x1f4507a491da5070d01b25068d42145182d4603507ed39e34274939c93d6e4d5a9254a139981663141814c280c098305d141694c240c088304c141325054949494e50509385e4a1491a4e44909083ec317efc53bcd7aeb53b6d4ad34eb0d2eb343a0d0a724e9890a395e8854d91525e52d6143564cd204e401088020 11 2047 5 31 11 2047 18 262143
def cc_62_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xb82d1b428594e508ca2180a007c5f07c1e15a1514150034cd0340c13008420080188601084001000 0x82582e4519ed3a315180541504eb2d3a595e7e54aca4c300c0b820ae4a0b0307c5429250ab17aa45292579e152625257141a64aa8926765427a5290579d1525213918429a8f9404e4410a5144968fa4a32904f9383e8d182294c7cd421b4876d39b1354c139a016 10 1023 4 15 11 2047 18 262143
def cc_62_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xa04ca61148844205006b34192c86432174b858a3510883d1e0e270349a0c23d1c0a84204 0xfca2234d11289f134f222590d2ce85e642fba7fbd0d026de84ef01b770b3ac6dc944e29a6f4d3a69dce4ee0a5ee50f204bb124d61269093386d6742d525e890f329d944ec81b62d62ae810d50b9b054d4306910960 9 511 3 7 10 1023 17 131071
def cc_62_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8190320640b4b682a1d409c7382704e09c13825144346288110220386684d01a034050ca01401c638060806 0x276294e2529b4653257a5ca92592d9924a4e058fd1ecba352504d244e64498ca0369304d200929e29d335fa56bd4897e8929d0a4fa0486b48f67d1dcf2379a46b3057a58a94a85e8f0a4cc0a890134683c8c06d160d21d28c3d60836b90c97211af41a52812bd024f626294425f854a70493600af3d04d 11 2047 5 31 11 2047 19 524287
def cc_62_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x98660892207cdf07c1d2741d0741b26c192605805896054550540f61685014050140500c82100800 0x2b434be492d44cac112f424b4132ac44bb092e524b8092d53bb44cecb429313a484caf4a2444cad052c23bae8ceb13bab4cea923900fb0f4fbfd1ef24bba90ede3b8f53ad84eb30f2c436a90d27344a3910a4249bd10a034 10 1023 4 15 10 1023 18 262143
def cc_62_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c23084a10841d4741b26c1b0649725495054150541504511044110440d416050140320c0300c003 0x1bc49374126fa4bdc487b613b681668149cb283ac4ef5499e792bca2479c4ef2499e8460cf6d99cd8334b665c60ca6d992d8320b66c35cd76a3a8d434d2e69250d12a1984ef1c99e2944c40898558304ae6005c 10 1023 4 15 11 2047 19 524287
def cc_62_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42b2ac2b0ac2b09d2709c27090e409024084e1078cff3c0f0348942408120080200802001704001 0x78944fe269f9183ecb67d06cf90c1ee4d3d81c7a834f26a5e29687010f7952de0b4360cbfdaffeb5bf86afe8d4fccaf78136e30bfb816f1c2bdd0536e07ed00ecb01b8c833ee02bd654ae4297615ee20bf6e14fa80af40155e49bcc8ff951bf213be3267c44ae541f70024 10 1023 4 15 11 2047 19 524287
def cc_62_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8f20c8311c42e3b82b3ac28382200801f17c1f07c1f06d1b06c1a1591605816054523480f303c00 0x90136220378f815210271f83d8d0351d0258c03d1b8351a8258b23a1ba36198368eb498e3438db418ca3f8b9274b03f190278a81789134884608796c8706c8686082834821448593485038848348282483352822523902d811525f0523603a89b5f88b5b86357843538395e819367205f6f85b660575e0533803f3503b178370e83380815 10 1023 4 15 11 2047 20 1048575
def cc_62_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xf41e83b1703e01c03806658a3102204407c6f05e036354ca815026234c680d01a02865009082804000400000 0x9f1399e931a02369f8259e0249c3529395e8d152628523f042a2453a1b5fa135ea0a5e9da529315e8c9527305f618535084f3e8432d03d9d03b9c8379b8353a02d270259a8289a02599824610519845e9295e6085298c5296a4d9215e7285f5f8539784d2ca423e04296a4e961285004f3d84326035958252582d93825240159283d9134e94a4f942439312f921274c02f40027238179112c 11 2047 5 31 11 2047 20 1048575
def cc_62_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xe83a0ca2b7ac2b09d27094a50942328c2127c9785c1525413248520409002980a000000000000000 0x28927d7a35942bd1c54a36a829c4fae86a5f09e831f44d3b7fa665e135481fa20370503f5a93a22a5bf543aca5110525f8a0d553baa2670e0adf411c353b7ca6757d72ada8d4f50a92a10c4edf099d445ca80a10a4edec99cff4ea64853ed327ba6524189e47d4a4ee9099c243b7a8674704e77a753a4e84296f450d4427a1447a68514b0968c120201f 10 1023 4 15 10 1023 19 524287
def cc_62_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x162c3c70a942850a1405 0x16991652af5a0453084f1d542cc9c5925cb1ca162542c22e58050 7 127 3 7 10 1023 19 524287
def cur_62 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_62_11 (Nat.sub p 352)) (cc_62_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_62_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_62_8 (Nat.sub p 256)) (cc_62_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_62_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_62_5 (Nat.sub p 160)) (cc_62_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_62_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_62_2 (Nat.sub p 64)) (cc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_62_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_62_0 : Nat → Nat := unpackHintV5 0x8e0011784a2c82c54058a8011143e1a08c2f058322d06402068640d007fc1efd029c2b7b850070a00dac6992a3284a14ca3e98c09250ca004a3fc047e414d428901a718a780a274001400000 0xda3416bdc21bd97dac7bb9bd9b5ec7b000005ac000631ac6000001736000017b8000053300d1a000010000015400031d500000001000000000810200c00dbd3b3f66e945ec555f3e01400050004016f0557aa8d5445518316b41055460aaaaaa802aaaab2aa000288ac5826d414600aa0a00aaa80000000aa000aaaa00200000026c0000404080010018c6318c63 19 524287 8 255
def hc_62_1 : Nat → Nat := unpackHintV5 0x994165b0a94826500291c2640079000237098d40a2f068b40a270678915dd0576c09b6256b029ac006545d890c5ec39700b59c255e0957009530943519040940010f907308dc00c2 0x37b1934d80306824c8000a07006a70220006bb46ad9e2f6376355a8c7bdc1b4da6dadb002d5ed5b2c0ba5c0bb04d800a000a0b080001600b569c027cf80180c631ad18d9e380e1c58b2aa02160c 18 262143 8 255
def hc_62_2 : Nat → Nat := unpackHintV5 0xd3aae607b16354f789a5acc41e493324808991c4c0215230805840041c09bda2d78e58e62b81d0d9e8680434021014ff12535922cd9120856662b00118807c20076e0007 0xb66ac01e701a340e2c80160007823ef69b0381b38b9acc0000068d00d9000072260b5ade346ad68d6be164b5bd21ae1fb1635ef984d6b411a8c6ad711bd9053d7ed7a08a73bc1e56c39ce7507d1ceb473d4403d8030018c635018ce000c88007bd8cd80f6346ab6782d99c020f3981c632000e4c 17 131071 7 127
def hc_62_3 : Nat → Nat := unpackHintV5 0xb24155b496b402d4c1ca0c8d40416629e4715477d66ef009c21c3147062800c50017d8caf6055be2e84b350900212003f2327d014ee8b9db02364525696087a585db20ac0e0bc9c17800002f 0xd8f7b1644f47b51a50230005cf8154036882d3600b507800d1a0000000aa000aaaa0000000000000a000aa3468000009b000400000008001001830020a3cb1cea7384f39ce07aa4439c631a34e75ad62cada3a5def72ec59c0f005554700aa668019c0e718eaaa61c8700eb1611ba0a58337b11a1bdcfda000050008b1000001ef5af40631a340000016a0f80068d059100000003e7c00031cf1c0000011b00000000004004018008f6ad679c586c56b99e782c 19 524287 8 255
def hc_62_4 : Nat → Nat := unpackHintV5 0xae6355c40ab602d620aa269f44c0266a34cd0091c7f1310a2382c390e872010e4021309c02246a75ebed6157a62575836d425ad2ca60f93b11272044786c8e011120a19490328004a9a80095 0x12d63b58bd8de088f5ade3468c688b58800c631850030da20200142aaa01b44101036b0368002ca01decf4007800280040110005cc0055cb860aa8c6a31a8d1a0026d41558b1418800002a8002aaa80000000002a802a802aaaa000000002a8002aaa800800000000002a8002aaa8009b000000000010800010100104007cf80555040d80275fb7dbdbbd86e5b62cdac1e82f555555562c5ac4011a30591036a00a0800aab2aa0aaaaaaaaa00aa026d62c44 19 524287 8 255
def hc_62_5 : Nat → Nat := unpackHintV5 0xff003fc00f8c67de05f3843c905f1c0bae19da11b6305d78170856be83a7c7e9c03270009883a620096c1e560594415e56c4cec90f243d864b046208b88002188783f2306894001a 0xdec4686f7b41e6f64f400001f3e018c68d000dec0002a800063aa00000000788c01ea00f3bce003468de338100041c00d8778e366f60000f78000c6378c000000e00000000738000c6319c000d8001c00000004080001006006e6000ec58b05a6c593007cf8068d000079cebdcf59b0dcbad82e05ee7ec5ee5848f62d73f6b1 18 262143 8 255
def hc_62_6 : Nat → Nat := unpackHintV5 0xb3c056700ac18cd32519bca905725e0aa3546d69e0ad0c31653ca5c6e3fcbc6a950d2829a0053360a64824bc8c96b0e2cc0a56830a884931200c1a216c142c810382104e22074280d810001b 0x4dec46800001ce78f00d1a00001c0001540015554000000000000e739c0006319c6703600000070000004080380800c18000000aa000aaaa0000000000000739ce78f00c63468000007dec580001ce738000c6338ce000000070000000e739c0006719c63000000000000aa00018ea800000020000001540015554000000037bd86d1bb077b05ef62c368dd83b160020000007000800e739c06300040006319c6700000d80001c0079bd87784fdeddede1bd824f 19 524287 8 255
def hc_62_7 : Nat → Nat := unpackHintV5 0xb7e0569866cc0758f09b140b5f832af1055905aa80b53c169f884f14e9c61d3840a4ca448b0e88690f0e01b3ae36502628a2986cd0b25967af27856480707e918e81519838066cc0b8100017 0x6f68e1364f0def73dd8dd833f7bdef72aa88be7c3551822aac59b45af0557aa8d555558b1f3f68d55820cf5c82b55aaaaaaa35555576aaa22aacaaaaaaaaa8a2aa9ce30628d54608ab2b160a35560aa0c620ad5eb55553c795551aaaaab3b55511555551aa9ceab3df2aaa28a34e0755824139d695556a95551aaaaaab3b4e88aaaaacaa739ceab54aaa8a2c16fb7b167417bdac1bb583b17b583bdac1d8b00004009800004738000300118c63381b0000000e00006f68d0 19 524287 8 255
def hc_62_8 : Nat → Nat := unpackHintV5 0x8f5990b931e73035a746b400c254584802b851570009e4fd0fad1f9263ee047805ced829d20939a0a72014d78c9af003540a68c1cc50c92e5c25c004b80097000ea441d400299100c4700018 0x1114e0755468c01daaaaa3546a8d5555655400044382823050404550055055400000001003620703a73c785554000000554f33cceaaaaaaaa8213261c1114e07639d76ca3555540ea301aa9ceaa35665760710055a150011103681c0ea718c6aa750010e086c6ede9d9e6f68c4d86f7b763760ef76f68e955511f3e1aa8c11551ac588de0aaf551aaaab163c6ac0527ae415aad5555551aaabb55551aa22aacaaaaaaaa35514dede9d 19 524287 8 255
def hc_62_9 : Nat → Nat := unpackHintV5 0x9de009de009c81699b2d9811a9671a965029164f84fc77f7587966172f67679b661c5d61a025d248531a14df5247c6342e4e351dd3054c2ae572ae00256582560021b3b1aa71158520ba9e0546600054 0x280e70a3cb1cea156de3d726e56f78b082441a356b5adeb18d3a70e3e751e3cb6d6951a355463518d651a9ceaf1e4f7c8c6800002a8002aaa8000000029c0e29047554e739d56a955556a9554e739d56a93aaaaaaaaaaa7aa5b6aa9d1155653aaaaaaaaaa9ce73aad52a8a8aaaa2873ab6ce1c3aaaa9d62c01688b1e2aaab557ad55115554f1e5555b6aaaaaaaaaa9cea2a2acf7caa703b1e5db29d55558b27aad52aa755555539ce755aa55381d6082738d1a73aea939d39e3d552adb8f1154a8ce8d3aacb2d33431a9ce73ad55514231a2234686c46831d4e0002a06c631518c0e73c780014e0718c63a39c636db281d503a346a9d5b620c60318c67038c6319ce0030601c000401541555500000000001005507600aaaa0080810070100000000000006035539d546ac8a12bb58b0ef0500559eb8000011681b4 20 1048575 8 255
def hc_62_10 : Nat → Nat := unpackHintV5 0x9fe7a99f5f8c4db7d5ef7934273f54694ab640545dc645d7055cb0c5616a50d544ab624416a37fc2327582d1562c30e2546f24b0924b0023d0e238051b7810ffb80d8270bc1c064580105400b050000b 0x41190e1cef8f6de739c68d18d62c3bc000007cb8068d0581b582c1a803b540381d3a73ce67a678622aa8c6a31a8d1a00084e61303820ca8e073a739d3cc2d850078f1c67039c633a319d18e38e00381ce0101c018000014cc0346800000002a8002aaa800000000005b00aa000102000063aa004063000000000000000000550005555000000000000003c78e9d018c68d00000dee7800001e3c00031c71c0000000000000aa000aaaa00000000000000000078f000000c71c7000001e3c00031c71c0000000000020000007000b678f00c60008000c71c7000000000000001ce703d5221ce318d1ab160000550000c754000000008d70400b50000068d0058b20202160cdc2c87b381e00aaa381d6b02a19c0e718ea86b19c0f4016eaa8f533400ce0738c755530e400208288a0066e6441f73d3bc9edb3bcf32239d128e71a3562ca4e776f03ed04a39d5e70dec0 20 1048575 8 255
def hc_62_11 : Nat → Nat := unpackHintV5 0x11a98a0d28370aa638a897ef505aa1b3582b6b041d5057ac000af 0x381d04939d576c7555562c3bc000007cb8154103682d19a0ec140381d595554e82aaaaaaaa802820820704400005500055550000000007600013000ea7020e00002aa0080c60346800000000000002a802a8002a80000000000002a8002aaa80000000000802a8002aaa8000000000000000002a800002aaa800002a8002aaa800000000008003b03800400aa08c00100055550000000000000 19 524287 8 255
def nh_62 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_62_11 (Nat.sub p 352)) (hc_62_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_62_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_62_8 (Nat.sub p 256)) (hc_62_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_62_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_62_5 (Nat.sub p 160)) (hc_62_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_62_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_62_2 (Nat.sub p 64)) (hc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_62_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_62 : Nat → Nat × Nat := unpackForestF 0xb4245b404500b4fb313800b4bb025cb0250b0150b005cb005000b47aea35ae83500b4300a4faca4eac92800a4ba835ca8351aa13baa133a8350a8150a805ca805000a47a324ea3028a6242a3025a393ba4818a3933a3813a302400a439bc539bb5f9bb5e9ba5e9e2369e0259e9399e9319e0249ba529b83b9b8379c3529b83500a3f99828998259982400a3b97c529845e9784d00a3795a4e959289582500a339224f92243938259212f9283d921270094e9112c0094b8f9368f815009438ab498ab438ab418d0358aa3f8c03d8a9278b23a8a8170094280b5f8913480b5b86c608696c8686c8686080b5784934848388483480b538095e8235282824822528093681152808150093b7735f7f1347735b7cc607c96c7c86c7c860773577a9347a8387a834773537715e78b5278a5a771367795277015009337515e75952750150092b74015009237123f712377113b711337112b0084f700246d24b6e9246e8246d2436d04e6d02c0084b63b5c63b516a93b6a93363b5063a5c63a506395066c6066b6c66b606696c6393b644606436c643606416c6393300847621446204454b4f605606015c6005c54b475e9245e82454a4b5d82454a435c1245c02454a3b5484e5a13b5a1335483c59342548365523b5792855233568145513b5513355123548340084347c5347b5f47b5e47a5f51a4447a5347a4f47a4347a3b47a374dc524da524da3247a354c9254795e4ba35479524785e4803648026489394893148024478520083f4583c45836458340083b404524025f435604325c4025341b5e41a524024d4093d4015e008373f1443bb4f3e1343bb433b84e3ca423b8363b82c008333aa363734e3724e38944389343714b37934371430082f35924358243224b3482432243338363214e3204e320360082b313581045f30348104531035e103532e451103521034e2ca4c1034b2b9281034328c5e28c522892a29250289261034227a521024e26a3e102422423e25144242322413e1015e22c602294c1015321b4819c5119b5119b5019b4e1ec501e92419b421da5019a4e1993d1c340199351b250199251a3501981610152184501814c1014b16c501694c101431013312a521294e129421285e13250128521004e10a4e10a421083e10042008270f0240624b0d2440d1240d0240624308a3b0b92808a330a8140893b0993c0893308923061340713907131068240604e008230235f04934023530215e02b5202a52021360081f01036008130001f 9 11
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 3 7 bds_62 362 (dagTraceF m_62 s_62 8 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 3 7 362 bds_62 (dagTraceF m_62 s_62 8 f_62) (cur_62 0) (nh_62 0) s_62 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : treeBlockF 0 32 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_1 : treeBlockF 32 64 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_2 : treeBlockF 64 96 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_3 : treeBlockF 96 128 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_4 : treeBlockF 128 160 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_5 : treeBlockF 160 192 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_6 : treeBlockF 192 224 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_7 : treeBlockF 224 256 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_8 : treeBlockF 256 288 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_9 : treeBlockF 288 320 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_10 : treeBlockF 320 352 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_11 : treeBlockF 352 362 ch_62 = true := by decide +kernel
theorem nj_62_1 : ∀ i, 0 ≤ i → i < 64 → ch_62 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_62_1 h1 h2)
theorem nj_62_2 : ∀ i, 0 ≤ i → i < 96 → ch_62 i = true := block_join nj_62_1 (fun _ h1 h2 => treeBlockF_at nb_62_2 h1 h2)
theorem nj_62_3 : ∀ i, 0 ≤ i → i < 128 → ch_62 i = true := block_join nj_62_2 (fun _ h1 h2 => treeBlockF_at nb_62_3 h1 h2)
theorem nj_62_4 : ∀ i, 0 ≤ i → i < 160 → ch_62 i = true := block_join nj_62_3 (fun _ h1 h2 => treeBlockF_at nb_62_4 h1 h2)
theorem nj_62_5 : ∀ i, 0 ≤ i → i < 192 → ch_62 i = true := block_join nj_62_4 (fun _ h1 h2 => treeBlockF_at nb_62_5 h1 h2)
theorem nj_62_6 : ∀ i, 0 ≤ i → i < 224 → ch_62 i = true := block_join nj_62_5 (fun _ h1 h2 => treeBlockF_at nb_62_6 h1 h2)
theorem nj_62_7 : ∀ i, 0 ≤ i → i < 256 → ch_62 i = true := block_join nj_62_6 (fun _ h1 h2 => treeBlockF_at nb_62_7 h1 h2)
theorem nj_62_8 : ∀ i, 0 ≤ i → i < 288 → ch_62 i = true := block_join nj_62_7 (fun _ h1 h2 => treeBlockF_at nb_62_8 h1 h2)
theorem nj_62_9 : ∀ i, 0 ≤ i → i < 320 → ch_62 i = true := block_join nj_62_8 (fun _ h1 h2 => treeBlockF_at nb_62_9 h1 h2)
theorem nj_62_10 : ∀ i, 0 ≤ i → i < 352 → ch_62 i = true := block_join nj_62_9 (fun _ h1 h2 => treeBlockF_at nb_62_10 h1 h2)
theorem nj_62_11 : ∀ i, 0 ≤ i → i < 362 → ch_62 i = true := block_join nj_62_10 (fun _ h1 h2 => treeBlockF_at nb_62_11 h1 h2)
theorem nc_62 : ∀ i, 0 ≤ i → i < 362 → ch_62 i = true := nj_62_11
theorem lb_62 : LowerBin m_62 s_62 g_62 9 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_14 (kn_cons lb_43 (kn_cons lb_39 (kn_cons lb_3 (kn_cons lb_47 (kn_cons lb_51 (kn_cons lb_19 (kn_cons lb_17 (kn_nil)))))))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0x3333333333333333
def s_63 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_63 : Nat := 0x113111313331333
def ep_63 : Nat := 0x1220022000001000000000000012000200200020010200020200020000000000000000000110111010001000
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 7, g_33)]
def cur_63 : Nat → List (Nat × Nat) := fun _ => []
def nh_63 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 1 1 0 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_63 g_63 ep_63 1 1 bds_63 0 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_nil)) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xcccccccccccccccc
def s_64 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_64 : Nat := 0x4044400044c4c
def ep_64 : Nat := 0x48080000044000004c480004004000040000000404000004080800000000000000000004044400044040
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_32, s_32, 5, g_32), (m_25, s_25, 5, g_25), (m_42, s_42, 5, g_42), (m_44, s_44, 5, g_44), (m_48, s_48, 5, g_48), (m_58, s_58, 4, g_58), (m_12, s_12, 4, g_12), (m_11, s_11, 4, g_11)]
def cur_64 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b0a0e80a02177c9f0785e0691a0681a05cd705856054550505405014035cd0340c1288a006401 0xe9497931281eb15199497141d9394131d036181e912b61235a50b4515242a94e41429c52935e895e5a5069445c507c5e7452635e5252495e4152393520342b4f1b43e34fcb43c24eba42a143813b3133101e0812001f 10 1023 4 15 11 2047 16 65535
def nh_64 : Nat → Nat := unpackHintV5 0x12482a21a7c3c0786a0ef9541bfb33017e5e61cbcc014d2ca95055200aa241d15af22605434188680108052010f3e02279828ea889cb0a2ccca58414b0801570a1a7081b598003680000 0x19c786c7801c671abde0002cd8f0363c00e338c5000160030039ce7004e9d4000000b800000c6318c009b3668d18000000c2601bda000e681b45ef19ce30400037b16f98c6bb5e0f519ce35eab166f7b367def73dec38c6717b1cc6357aec147319ce71af558b37b581ee0399c671a0aaaaac16b5ad6339c60000001c6718002aaa80000000807019c671a0a9d1802c5830e2c4 19 524287 8 255
def f_64 : Nat → Nat × Nat := unpackForestF 0xe9490b4fd139d0360b430a4e0a42ac51a94e09438c528b5e895e093b3c5e3c5269443b5e5c503a52395e3952393509331b4f20341b43081e0812001f 5 11
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 3 7 bds_64 30 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 3 7 30 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64 : treeBlockF 0 30 ch_64 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 30 → ch_64 i = true := fun _ h1 h2 => treeBlockF_at nb_64 h1 h2
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_32 (kn_cons lb_25 (kn_cons lb_42 (kn_cons lb_44 (kn_cons lb_48 (kn_cons lb_58 (kn_cons lb_12 (kn_cons lb_11 (kn_nil)))))))))) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xff00ff00ff00ff
def s_65 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_65 : Nat := 0x1700570037007f
def ep_65 : Nat := 0x20002800000040000000480000000000000000000600020004000800120002003200200014005400040040
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_11, s_11, 4, g_11), (m_46, s_46, 5, g_46), (m_50, s_50, 5, g_50), (m_22, s_22, 5, g_22), (m_51, s_51, 4, g_51), (m_8, s_8, 4, g_8)]
def cur_65 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b09d27090e408c63071dc0701936419060580601715c107401003c4d2340d0340c1288a006401 0xea5d8a55c24582357b46da46514a7234cb5d8b55c345aa3a6a36b952413aab56a256285a72447244945a8c5683567a5a6a56185a6042495c524b4247204c2a3b1a37e347d24bb2479a3b5a37393a3136104a0846001f 10 1023 4 15 11 2047 16 65535
def nh_65 : Nat → Nat := unpackHintV5 0x7b203928fc587d0a4e761f2d1d9307b7255ae16d00f43c9a003ce43a641d2f859407c88323d0ef9ca7b82bdc01e414c0e349ed2441522008c0a2d718b76800b60000 0x802135ac4004055015384d62c5ab4000004e9c1b3993162802c260003013a709835acd68b15aa8306aaaa7069c9cd9ce732739a0ad556b3060d55553ace63140550630018c6317a8aaaaaa00000080002a8000002aaace6700005000780000a73a739ce0022a8022a802a8008002000080a000c41830e8aa9d3a03 17 131071 7 127
def f_65 : Nat → Nat × Nat := unpackForestF 0xea5d0b47da460a4bbb5dbb45b9520a47a356a2560a3b645a64566356625a7244625660420a37424b495c4247093a09361a3b204c1a37084a0846001f 5 11
def ch_65 : Nat → Bool := dagCheckNodeV5 m_65 g_65 ep_65 3 7 bds_65 30 (dagTraceF m_65 s_65 7 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 3 7 30 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) (nh_65 0) s_65 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65 : treeBlockF 0 30 ch_65 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 30 → ch_65 i = true := fun _ h1 h2 => treeBlockF_at nb_65 h1 h2
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_11 (kn_cons lb_46 (kn_cons lb_50 (kn_cons lb_22 (kn_cons lb_51 (kn_cons lb_8 (kn_nil)))))))) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xffffffff00000000
def s_66 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_66 : Nat := 0x117155700000000
def ep_66 : Nat := 0x1440000000000016004200000000010604020000000001121002000000000114155400000000
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 7, g_20), (m_29, s_29, 7, g_29), (m_23, s_23, 5, g_23), (m_18, s_18, 5, g_18), (m_26, s_26, 5, g_26), (m_25, s_25, 5, g_25), (m_22, s_22, 5, g_22), (m_24, s_24, 5, g_24), (m_21, s_21, 6, g_21)]
def cur_66 : Nat → List (Nat × Nat) := unpackCursorV5 0x13098486411188442030078bc1e0e1703443801 0x3230cd11d30791092028d3e3fe8ef637b8ce93f94ee13764cd52f44acd27148c01f 9 511 4 15 10 1023 14 16383
def nh_66 : Nat → Nat := unpackHintV5 0xacedba17b7945d28d76e816c1726f0636f054fe74cc833cffd318b723ddb16bd20fd6e03cc10003c00000 0xaaaaab52aac7b673d1ce75559ceb5ad635bd63a7384000000000001555563dbaa55558f54aa739cf5550e7d08000000000002aaaaad4aa73ace7a8f2a9de719ce719ce73d39c2000000000000aaaab1edaa9ce73d508000004002aaaaad547955565d52aace75d55439f4200000000045c001555554631aaace75ad6b9735caaa338f6738c6739de378c400000000000155554e739d54671ec6318c6318d55546718e18c731c318c4000000000001555554631aa9e678e73c739ceaa73ace718c671bc6f188000000000002aaaa9ce73aa8ce3d8c6318800000000c5555559ceb55518c6319c6318c6aaaa358c70c6398e18c62000000000000cb82aaad52aaacba8f552aabc6f1d0f7554f1000000000000555559d39546318e87b18e955546b18c6718c6f1d42000000000000aaaaaaf5bcef3bd6ab3a70c635578de3aa863a188000000000002aaaabdef7aad54fb62000000010aaaab54aaa318c7554355559751eaa870800000000001170555555100000000 20 1048575 8 255
def f_66 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
def ch_66 : Nat → Bool := dagCheckNodeV5 m_66 g_66 ep_66 3 7 bds_66 16 (dagTraceF m_66 s_66 8 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 3 7 16 bds_66 (dagTraceF m_66 s_66 8 f_66) (cur_66 0) (nh_66 0) s_66 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66 : treeBlockF 0 16 ch_66 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 16 → ch_66 i = true := fun _ h1 h2 => treeBlockF_at nb_66 h1 h2
theorem lb_66 : LowerBin m_66 s_66 g_66 9 :=
  lowerDagV5 (kn_cons lb_20 (kn_cons lb_29 (kn_cons lb_23 (kn_cons lb_18 (kn_cons lb_26 (kn_cons lb_25 (kn_cons lb_22 (kn_cons lb_24 (kn_cons lb_21 (kn_nil)))))))))) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0xffffffff
def s_67 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_67 : Nat := 0x13375f7f
def ep_67 : Nat := 0x4c4800000000002400200000000002040a0800000000133200200000000010045040
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_45, s_45, 6, g_45)]
def cur_67 : Nat → List (Nat × Nat) := fun _ => []
def nh_67 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_67 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 1 1 0 bds_67 (dagTraceF m_67 s_67 6 f_67) (cur_67 0) (nh_67 0) s_67 6 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_67 g_67 ep_67 1 1 bds_67 0 (dagTraceF m_67 s_67 6 f_67) cur_67 nh_67 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_67 : LowerBin m_67 s_67 g_67 7 :=
  lowerDagV5 (kn_cons lb_45 (kn_nil)) rc_67 nc_67 (by decide +kernel)

def m_68 : Nat := 0xffff0000ffff0000
def s_68 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_68 : Nat := 0x117000013370000
def ep_68 : Nat := 0x1220000000000000000000000016000000240000010600000204000001120000133200000114000010040000
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 7, g_20), (m_33, s_33, 7, g_33), (m_49, s_49, 5, g_49), (m_35, s_35, 5, g_35), (m_50, s_50, 5, g_50), (m_34, s_34, 5, g_34), (m_53, s_53, 5, g_53), (m_52, s_52, 5, g_52), (m_45, s_45, 6, g_45)]
def cur_68 : Nat → List (Nat × Nat) := unpackCursorV5 0x13098486411188442030078bc1e0e1703443801 0x3240cd51d40795092028d3e4fe92f647b90e94f952e147650d52f44acd27148c01f 9 511 4 15 10 1023 14 16383
def nh_68 : Nat → Nat := unpackHintV5 0xab9f09c9f08e2e785f83762fd687db5d0b74fed24906e3cfc12f4db23db716bd20fd6e03cc10003c00000 0xb5ad555554637ec635ac631aaaac635aceb9675caaf7bde0000002000000aaa31bf6318c6aa318d55546b18c631aacdef98c638671c0020000000000318d5555546358c6318c6f5519c70c6386318d55ef7bc0000004000001554635ed546318d556b5ac00400016002aaad6318c6f5555ad6aaaa318d631ad566f7cd675cb3ae0010000000165c002a55555558c6b39cf33bce755876c63a18c6aaa78f00000008000002aa8c631aac3b754ab550e5555a753eaa0010000000000a95555546f18c631cc6318d546338c750e553c7800000040000015546318d561db55aa001000000855558c6b55aa872aad547955569d4faa80040000000008b82abe6f9aa9d6719c673aaaad478f2aacfb673d1ce70010000000000557bdef555aa559f6eaa5d43a55558f540020000000000aa739c6719d6aaaaf7bdeab51e3caa739ce7a9f00080000000002a9ce73aaad52ac7b60020000010aaf9be6aab54aab553e9750e955563d50008000000001170555555001000000 20 1048575 8 255
def f_68 : Nat → Nat × Nat := unpackForestF 0x193c64b191f354190c54f152c547795054314bc52b149ca34148c01f 4 10
def ch_68 : Nat → Bool := dagCheckNodeV5 m_68 g_68 ep_68 3 7 bds_68 16 (dagTraceF m_68 s_68 8 f_68) cur_68 nh_68
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 m_68 g_68 ep_68 3 7 16 bds_68 (dagTraceF m_68 s_68 8 f_68) (cur_68 0) (nh_68 0) s_68 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68 : treeBlockF 0 16 ch_68 = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 16 → ch_68 i = true := fun _ h1 h2 => treeBlockF_at nb_68 h1 h2
theorem lb_68 : LowerBin m_68 s_68 g_68 9 :=
  lowerDagV5 (kn_cons lb_20 (kn_cons lb_33 (kn_cons lb_49 (kn_cons lb_35 (kn_cons lb_50 (kn_cons lb_34 (kn_cons lb_53 (kn_cons lb_52 (kn_cons lb_45 (kn_nil)))))))))) rc_68 nc_68 (by decide +kernel)

def m_69 : Nat := 0xffff0000ffff
def s_69 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_69 : Nat := 0x155700005f7f
def ep_69 : Nat := 0x4a28000000000000000000000042000000200000040200000a0800001002000000200000155400005040
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_21, s_21, 6, g_21), (m_32, s_32, 5, g_32), (m_39, s_39, 6, g_39), (m_37, s_37, 5, g_37), (m_40, s_40, 5, g_40), (m_6, s_6, 4, g_6), (m_12, s_12, 4, g_12), (m_57, s_57, 5, g_57), (m_16, s_16, 7, g_16), (m_55, s_55, 5, g_55), (m_30, s_30, 7, g_30), (m_59, s_59, 7, g_59)]
def cc_69_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9609609609609608c56166006005a35a05a05815805805424c44c04a14244013c23c0382380361360303300284033001 0x3c92475208e15e1b28c34511722fadc5b586beacd6d55ad283574f6ac92d4d15a7a134b3f68e78d0ce12b1995f322b66251cb0a19513f25276444dc7c998c856172d8204d0583609a5d116b42095855ab8a236122ac1e4d8201806a500a4700e500302e032300a68c0a908191c0404c066880ed14151d021360b68e128e80ca10113ac469f86d2f0527de247b747f6a8dec0a7d794bae26f3a4ce6095c99278f09ef011db81fb08371804e1c07c040b8001f 12 4095 5 31 11 2047 19 524287
def cc_69_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8d1c9c8c8c8a5a0a0a0a084808080808080646052494848482c282813100901 0x7c933d8a9da49e920f2179b08cd044ddac6cd5354a9a054c0a65e512e2696814ad2a5252212494a4ca0ae4e4d26029224c80984613212790244 8 255 3 7 11 2047 17 131071
def cc_69_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x88441e8f0783c1b6d15dae170b85c2e12a8944205008040158a050280d052280d0603003 0xc0d62fb54bc952e854aeda2d254b21527254af1b1db643c192a4609ad429a6ca4582886c97176725c9b191d364989525a4c94490e86488d6242448e52230447c912245c86491eb4082972005c 9 511 3 7 11 2047 18 262143
def cc_69_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb82b3ac2b0ac283731c06c5b06c183601806016249102400f13c0c3300b12c092240811100400000 0x200b63f9547e028f8db1ecb63d0148e6a71a97e312ea7a558a49b1291e1922c123f812a6fa4cde4958c826774baeadb1c11a3a06c718b4e0959d9ab39a577248ade8d5aca0b392566468d6d35951b3513666280cc931901e32030686a0ce97194a03183c6d49ad88f5a498b1127 10 1023 4 15 11 2047 19 524287
def cc_69_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xa9e0a801f17c1d26519058d514c8f43c0e1380c2300a2208801c461180600cc300c03000c0000000 0x50b459746d4056a7c9d179367e0ac5a0dab1abd53459646d4c55a889b3e8576908a580dc0c12cf0159c0bb34569e82b4d956790ae04096640ab28459507b2e05590224a9426308d2c5098823ca03d1403b2517a452ac8245884a838092111f3e1298b8bc3609221274385e1a0490adb2113641834 10 1023 4 15 11 2047 19 524287
def cc_69_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0b62ab2a0a46909ca34849d4741a36817350d31485203cce12ccb02c0b01d0701c07001c0000000 0x87110e424740f8581ec0d4efd53ac4cef85fbd1753c5591136244786115cc3f38094541fbb176e75a8315aeb568215db045b80d6ad310c05aa931b6135c83d0b05ed05d36154d425b2934da453409ace45b1114cc27320dcc427ad5b2a154a44d02024ab1341c25a1056a65da89169c5d7f116975aa4959a845a30f4bc352e0941015 10 1023 4 15 10 1023 18 262143
def cc_69_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xc2791b3c9202000 0xc81357c455e0971a4d5f9157426c791714455c09d6c278a1570845 6 63 2 3 10 1023 18 262143
def cur_69 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_69_6 (Nat.sub p 192)) (cc_69_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (cc_69_4 (Nat.sub p 128)) (cc_69_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (cc_69_2 (Nat.sub p 64)) (cc_69_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_69_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_69_0 : Nat → Nat := unpackHintV5 0xc3408c3002c2008c040eb8042ac45e91cd4918028fc0e89c3082c3882c007904e790007740e6947045d1c45c0042c183d02e3a8143184830c06308022fc062f0062ec0228434224300bcb40005e00000 0x2b50d40ac35511ac0c0eb2cb05030302b2cb0c30c30c30d4238c22cb830c30c30c30c35679db6c1c1c30c30d55554350d55555acaeb1c075c70dac0800c281c30c4070b8b835c30001c00102bac5c8b2e0d30c70c79d31c4470c4544d300c4c34c301c9c131c1c7071c0c071c701e1c71cb1e0c31c71c30d514555506b05007aebaeb0b0b83076bacaeb00c00008b2e0000555acacb42020000881454080c2801c054000130c3000000b020000c000000000000555504001ae38c30c30e79db6c30d54355 20 1048575 9 511
def hc_69_1 : Nat → Nat := unpackHintV5 0xd506d402cf0ac90cc606c2089f469f009a0a950a8e0e801c70205c28550e550053044f083d243c0234102b122a02250a200a1810130a0e0a090a06060502000a 0xad8b6b0c3430c31102b2cb0555434b82b40eb00eb075ac701c1d4c132e6c1d1b1d60e2db1ca0d56c714dbad074711db1ac46b1c6b471 16 65535 7 127
def hc_69_2 : Nat → Nat := unpackHintV5 0xf80af10ee31cd320ce0ac90ac40ac106b616904c8f028a0a8902840a791648624506420641024100400230202d062c0229062110181217020f100a0a050a000a 0xad2b0eb02e0d6b8b8f3e4adac45dad7150d0c35d78b2e1407075446b14ad8c5e7575cb2e2d7a5c35c07171c75daeb5230d9d4325862db5b4eb4b9b6b12b62d 16 65535 7 127
def hc_69_3 : Nat → Nat := unpackHintV5 0xccc10c702ec540ec4806c2c0ebcc309fce89fc009684a96402940128e82c848508480082c0e77c585ccd84dc78434544300242c023745c3740034418338063340232806300142a42e01d4401c000000e 0x21cacb81c9f8acf1acac3acac31cac77c7ac553cb7e3cb83cf030df0c303033c307c701c003c00c00506b553d555006846835c38f070744566b2eb8b97ab3c36b3cb8f2e0cfa0e1c71e592bac5ca3950ea81c1d3930d556aa3a2a854f0c3aaaa0ea3d34cfa4ea8878a0d34c35556b65655554f2c3cf254f0c32cb0cb07070d3d554f2e3cb830e0c71c793e5440b3c7072c078f2e8793e556b1ebaeb2b2baeb0b0b8307aeb4b0b3cb2cb0b8f2cb953c33c32c30cb2c30e0cb2e3cf3cf2c2c72c2c78b2cb834c3553d65955ad5554b07 20 1048575 9 511
def hc_69_4 : Nat → Nat := unpackHintV5 0xe8046cf0c8cf000c5c4ac5c00b8c6892534918068984088c067f44c664c864c0c5e434554483f4b03b81e378202c8582b00c2383c1e8281d8081c80810462100020dc120c00e0682c03c1603c000001e 0x21c7c140c31c1651d90a0032aa0f0070a21b071c0c2a0020eaa8784a64351c7069651c2e2e000300005f47079d31c7c8b2e410c15350c74744d300c3030c30c072704c7071c0cac030c071c701e1c71cb1e0030c3113534343471c11c751d430020020c0c0083a22c022cb803540000410c000000002c0800030c30c03000000000032b004d40010d0d002bac0030ac33c145400b8b80033c0015414000020b000000c03c33c3000000000006b00055554023cbacf40d035eb1142e2e0d75c30c1c1c3115aeb030c0c042b4f4300d55c307d0acac0d54030c3ac33c15ac13d4342acbacaeb8b9f83aeb3d1c2b01aeb2b3c 20 1048575 9 511
def hc_69_5 : Nat → Nat := unpackHintV5 0x9700e49014206211030007c6293e3001db8b0cf4f46063a251591288008a84e45400203138d217c4dcda1b05f0d80005f8642f802110360880003c83c1e40006447032000150200a800006270000180000000000 0x4306b570c42e2e1107075d5f50d0c30cf2d78f2e0f3c00030c03ac30c30cf0c171c07000f00300d575113d0c34341a22a0c0c0c3a07075f63e8c7c9550d4e07076650d36aa3a2a8a830c30e83aeaa833d34cfa4ea8878a0c30c33d699a594343535343cf0f2c35433e541c1cb3d2d4b434b0b3cb2cb0b8f2cb830c30c30c33c3aa830e83acf3cf3cb0b1cb0b1e2cb2e0c30c33d3d2d4b2d64b2d0d0d4d400b8b80033c0003c143002e2e0c30000f004f40000020b00000300f0cf0c0ac000000f00000100f4f4350000004c33c302b0001c001c00001c0801c00c0004d3d0d41c001c00400000000700130003832e000000086c00004c0064b435002eacf0709780c00cfa3c7072c030e3cb83878b1eabacfac2000020ac35c323c0070700ac801c5f48f1c8ac7170a03aa07031c39431c3 21 2097151 9 511
def hc_69_6 : Nat → Nat := unpackHintV5 0xd8003164ac5802d04688ab948da3f13038c4058880016 0xe2e000cb000050c0014b430c000012d0002ac000b00003020cb8000000000000004092d0d4002ae822e000cf2a8faa0e3e80020821c284c0c4f298f6963d4354c1002e2e050d00004f4300000082c003ac00030c30c300000000000000403d3d0d0d008f2eb3c32b1c00 18 262143 8 255
def nh_69 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_69_6 (Nat.sub p 192)) (hc_69_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (hc_69_4 (Nat.sub p 128)) (hc_69_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (hc_69_2 (Nat.sub p 64)) (hc_69_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_69_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_69 : Nat → Nat × Nat := unpackForestF 0x6404dc548b8c937142280b4f01697841140527deb53bd2a77a17ef42e80a47bb0bb70d5ae5ad5c0350147f6c134051bda05db148b64936c4228094f01296024deb4b64f357ab09b3cd169d2ed3a45a70bb3c55a8dad51a56a307b3c4da7da2cf95a9f2753c0540499ce05d992ad3456a640a8092b9702b2850a54a14a03d0124f2517a412ac82450109ef2d4de52fbca5d8b8bcf2935e523c3a4e870bcf29160db641a6c83068f28fde4a9bf16c7e2a8fc051e499bd36c7a2d8f4051e49580847774baded59d1b63a06c6f4aede915c22d382566f46a020fd8926b123d6a69ad44d98898b1b50634b8cc9318ca03203063078c449c041baeb585d6a8ba951742a0cc5f198b6b2951642a0cb5f578d832d6c65ad28c60514d8a258144360cb57196ac9c9712a32252544a4989449065a9a3244462908c11065a7a1c5c4324832d2d012e2005c1968e7c930f62a0cb433949272904e42f0ca56346b068d50d12a1a054192be3256c64a39694c2d2885a4d0b40a0c9432b4a8324fc99261315c262684c050649d91a4c23098324dc849e10244192663492469208d15e1a28c34510642b00827162d82c1b03dab87a36134ba1e55841ad082560f26c0207c31280605c0268e14d18091d0404c0468a0cd10111d0213602284044e8040b8001f 8 11
def ch_69 : Nat → Bool := dagCheckNodeV5 m_69 g_69 ep_69 4 15 bds_69 201 (dagTraceF m_69 s_69 8 f_69) cur_69 nh_69
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV5 m_69 g_69 ep_69 4 15 201 bds_69 (dagTraceF m_69 s_69 8 f_69) (cur_69 0) (nh_69 0) s_69 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_0 : treeBlockF 0 32 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_1 : treeBlockF 32 64 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_2 : treeBlockF 64 96 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_3 : treeBlockF 96 128 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_4 : treeBlockF 128 160 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_5 : treeBlockF 160 192 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_6 : treeBlockF 192 201 ch_69 = true := by decide +kernel
theorem nj_69_1 : ∀ i, 0 ≤ i → i < 64 → ch_69 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_69_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_69_1 h1 h2)
theorem nj_69_2 : ∀ i, 0 ≤ i → i < 96 → ch_69 i = true := block_join nj_69_1 (fun _ h1 h2 => treeBlockF_at nb_69_2 h1 h2)
theorem nj_69_3 : ∀ i, 0 ≤ i → i < 128 → ch_69 i = true := block_join nj_69_2 (fun _ h1 h2 => treeBlockF_at nb_69_3 h1 h2)
theorem nj_69_4 : ∀ i, 0 ≤ i → i < 160 → ch_69 i = true := block_join nj_69_3 (fun _ h1 h2 => treeBlockF_at nb_69_4 h1 h2)
theorem nj_69_5 : ∀ i, 0 ≤ i → i < 192 → ch_69 i = true := block_join nj_69_4 (fun _ h1 h2 => treeBlockF_at nb_69_5 h1 h2)
theorem nj_69_6 : ∀ i, 0 ≤ i → i < 201 → ch_69 i = true := block_join nj_69_5 (fun _ h1 h2 => treeBlockF_at nb_69_6 h1 h2)
theorem nc_69 : ∀ i, 0 ≤ i → i < 201 → ch_69 i = true := nj_69_6
theorem lb_69 : LowerBin m_69 s_69 g_69 9 :=
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_21 (kn_cons lb_32 (kn_cons lb_39 (kn_cons lb_37 (kn_cons lb_40 (kn_cons lb_6 (kn_cons lb_12 (kn_cons lb_57 (kn_cons lb_16 (kn_cons lb_55 (kn_cons lb_30 (kn_cons lb_59 (kn_nil)))))))))))))) rc_69 nc_69 (by decide +kernel)

def g_70 : Nat := 0x117155713375f7f
def ep_70 : Nat := 0x12204a280000144000004c4800160042002400200106040202040a0801121002133200200114155410045040
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_66, s_66, 9, g_66), (m_61, s_61, 8, g_61), (m_60, s_60, 8, g_60), (m_27, s_27, 5, g_27), (m_69, s_69, 9, g_69), (m_68, s_68, 9, g_68), (m_63, s_63, 8, g_63), (m_24, s_24, 5, g_24), (m_62, s_62, 9, g_62), (m_48, s_48, 5, g_48), (m_65, s_65, 8, g_65), (m_64, s_64, 8, g_64), (m_1, s_1, 4, g_1), (m_29, s_29, 7, g_29), (m_67, s_67, 7, g_67), (m_3, s_3, 4, g_3), (m_28, s_28, 5, g_28), (m_6, s_6, 4, g_6), (m_46, s_46, 5, g_46), (m_23, s_23, 5, g_23), (m_11, s_11, 4, g_11), (m_54, s_54, 5, g_54), (m_31, s_31, 5, g_31), (m_2, s_2, 4, g_2), (m_56, s_56, 4, g_56), (m_26, s_26, 5, g_26), (m_19, s_19, 6, g_19), (m_22, s_22, 5, g_22), (m_25, s_25, 5, g_25), (m_47, s_47, 4, g_47)]
def cc_70_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x7e37e07e07837807237206e26e06a26a06816806806615c55c05c05a15a05a05a05a05a04a84a0481480442348039001 0x104650fb680734a0ec550e3580634a0d36804b6005b480a3720c3580b3600207608824089460a45f04a4a09a47092460802606a540756f0656305c6e0526e04a620425f03a570186602d700234701a3a0f56f0dd630cc6f0bc5f0ac5707b620334a01066c2c5fc1c5bbfc57bdc53b035fafb57adb4fab347a1a5f9ea5b9ba578ba538324f7c24b73a476aa436323b5a2375385f468573904f2d0471c0371082f008270003f 12 4095 5 31 11 2047 20 1048575
def cc_70_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc1782b2560ac1581b83606c0c0d80300546a81312604c080d00200384700e01632c0580b01601c801c00000 0x205727e9f9f25c7a912c56fab58ea46ea718e9462a316e84539a9be5a638e97e2a5b8495de2537693dd24372199bc656c9913246691559a544a919226c629917d7e509f97254599c95a6c48d754b5550d3d356f4b58d246e47189ad6f6558d846f5b17d54574e9b91246 11 2047 5 31 11 2047 18 262143
def cc_70_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8bab8b17f7871707062606059585858584a483a38383823201918180a080100 0x2fe72bc9b2e460df58b6b6fd2d772a6fc298eea3bb68decc68af162b3548094e7c689cd92436e98972557e9316242728c9722672871820a44 8 255 3 7 11 2047 18 262143
def cc_70_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c44621107dbe1f0f871b81c0d24fa61307c3c18cc060300f470381c08c40201002c1001 0xfc9b1f62abe2547b48cf35f9e13f3ba54758e4e91622e3744b6f8368afe9bde931bb23b7346ed6d35c5a3b83455f476dd5a1aeb03535c6c8dcd7189a9b73326f644c6d15a19db2b335d648dac69b1892330254 9 511 3 7 11 2047 19 524287
def cc_70_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c2618ce3088620882207cdf07c1d2741d06c9b0684fb3c0c3300a2280a0280a0280370c0300c003 0x13d5c2823e4fb7d9d68b369f266b84c37d976bb2a9f251364947c914f91f1c299b6d1b4fa168f3893e6925cb24793487208ee391b9c8360204d10d7631aabca3b888d91519222b743d6386ac5009bdf531c2a5f844a70519205b2c0345 10 1023 4 15 11 2047 19 524287
def cc_70_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xa42729c2709c27089620882025a96058160545505414150140489204809915050140320840200000 0x5fc58be6a8ea17ef01d5d837ba06d720d2deb7db46ec4adf855af02b3ded63b88c5501be3833b985f5b0af6a136c5a2d735dac4f95691951aed9b4fb268f6093ebd25d6a47aa487528eea11bd234e9f49f3091e491cd2c7ca46f80a09a8ab802026 10 1023 4 15 11 2047 19 524287
def cc_70_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xa5e90a4290916409024084d896018054d50505404c5304c11240500400e212840088200441000400 0xe16dbc0d9775aeefb55ac0db28194fc1beec6edc8c5b6d9aac379e835d98dfb098b5d2572c6fe38cfc4dbb79376d246aa0df2619cf023eb025d44c9a61972412e8a54cf4f99a953302abc04fc9adf9098b4ab7e856bceacf9758f29375486f900ceec17d742be3825c58d16e1370e2c60c70 10 1023 4 15 11 2047 19 524287
def cc_70_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xb82c2b02c0b029386201802007c5a5681735c1615816049120481203cc781c0340c0030000000000 0x7fc6e7f4627e46f7da627d24a8246f814678026e7ea465786f4d067228477c8257a8457ab4576b4d7bb477b3457a047220377956876d607505d785707746e76c625706f4b86775d6e7536f74b5579d6278b6f77b677635d5686f4b0677405d2103770a7c6ea6c732646c8257227c7026c6da44 10 1023 4 15 11 2047 20 1048575
def cc_70_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8360d8360d4750b260c801d3741a36819164190641904d92148120480f31a4600cc300842000800 0x8d9469145f904538fb5f8f34f8eb47081538e14b8d1438c93b9ad6f99d639946f97c5f9645785b5e93a463d05f3085725847920258c0248835d8b355250378846c8a464848458947c8856e87d6b8756386d625886f4e867240378546284b6f8434d8ac6e89b6f88b678634585a625806f4e06783845238377fa6c82a647e02581a7c7fb5d80b55 10 1023 4 15 11 2047 20 1048575
def cc_70_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9042e110880c01f2e36cb0d72a349241207b3c1e0aa5028140a026100802410048200200 0xa0c5f9fc579f2469dc7c9cd709e36d9d34f9c347918249b46595a4691024908249a455952469002494a448f82498a54980558f0249726c942449686d930258e82495d6f9556394b6e943563d85f310579345792a4a91b5590b45 9 511 3 7 11 2047 20 1048575
def cc_70_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xe4790dcadab42b2ac2927e9f0749d06c9a1681a0681a06812848111440f23c0f03482b0801104001 0x1782faec6298263af46ea4a6fa0a6b9d26797a635986f51867ae0451682f0b827ad0471602fac56e96a63acd62a3a6f9fa6b9c267962635906f50867ab85d1502f0a827a7365aab55a6b65a9b45a6364a846fa7c63a745fa6c53a635e4084f3384727035a5464a4568a2865a335da2b47aa46fa9463a8b6fa5b55a4b4fa3b4771242a20553f84f3284726837a1254a026c 10 1023 4 15 11 2047 20 1048575
def cc_70_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x7c77c078264a6216016006005a35a05815805805805425404e34c14a14814804424404404213a43a0381380380098004 0xb8b6ea9a6f9a2635f2352b0351a02f0e827beb4d6623bbcb6fbf345a926f99a6365a3b5ea37be0452a8371902f0d827bbb54b8b44bc57cbac68bbb54bad6cb947cb8b44b7d7ca6354b6a68b5254b6b6cb4a50b525cb3824b3a54b4b64b427c94a44b3024b257cbd46fbcc63bb45fba45bb9c57b8453a8a6f99263b725fb625bb5a57b2a5389a4f8224b78a4772a43b185f2a05db1057b08554484f368471802f0c82788a4f8124b77a4771a43 12 4095 5 31 11 2047 20 1048575
def cc_70_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x28b4091229005328140a005 0x5df6eaacdf3698c6e1788027c3ebad38eef5b7e2355aa4df3598da51db1237c30aa580dc6a1787827c268ad08ed851be0b6dc0cd9809819d1db0237 9 511 4 15 10 1023 19 524287
def cur_70 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_70_12 (Nat.sub p 384)) (cc_70_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_70_10 (Nat.sub p 320)) (cc_70_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_70_8 (Nat.sub p 256)) (cc_70_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_70_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_70_5 (Nat.sub p 160)) (cc_70_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_70_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_70_2 (Nat.sub p 64)) (cc_70_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_70_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_70_0 : Nat → Nat := unpackHintV5 0xd04338c9ed95c2b9cdb57f4fae49cda10f4f98ea098ba352837e0975937b6fbd756a2d64621e045fb8995899c8513dd74b816f492896432d7f3be9d13419f42cf5c927e14522cd451b5ddc198c7415850210195b0a6d6b030dd80000c3000000 0x60c1d0fdf40c1d40e8183060cb83060c78f1e3c183aa060c183063c183060c1833e0c1831e0c1831e0c783060c783460c183060c19706c8306a0c1a8341a0d06800e8183060c5830e0c187161c587161c5830e0c183060c5a0c1a010000031780000082006f000740e1e3e060c997060c1d03063c19b060c193064c183064c1a7060c193060c1930683418300e2c38b0e1c383062c8001103783a01d03363c79706c8341a0d068307540c183818f060e8183064c183065d40001d030e2c38b0e2c38b41834187060c183062c00000000000000183aa1fbc18307503a066c78f2e0c1832e0c183060ea8183060c18f063c183066c1a3060c19f060c183060cf83060d183060c183065c1b20d068306835060c19f50683400740c38b0e2c183062c187060c38b0e2c187060c183062d060d00800000018bc0004100378003a06503265c99706c8341a0d068307540c183060c783060cd830740e065d40001d030e2c38b0e2c38b41834187060c183062c00000000000000183060e8183060cd831e0c1d17df40c1d44cb932e0c1d503060c1833e0c183060c19f060c183060c783060d183060c983060c197065c1b20c1a0d4183067d41a0d0683400740c183062c187060c38b0e2c38b0e2c187060c183062d060d008000018bc00000410037800f363cd932e4cb83c7973e9f4da3d2e934d83371b8d832e5c78f1e0cb972e0c78f263cb9750000e2c38b0e2c38b0e2c38b45874387162c387162c0000000000000079b1e6cd83271b89832e5cb932e4cb8f1e5f78f1e5cb8f1e3cd9b371b8d9b363c78f1e6cd93260cf9b366cd9b067c993368cb97264c9932e5cfa7d368f49835360d4ba4d0038b0e2c38b0e2c387162c387162c38b0e2c387162c387162d161d003600000000082006f001e3c78f265c9971e3c1e7d3e8f47a5d26a7069e4f27063c18f1e3c78f1e5c193264c9972ea0001c587161c587161c587168b0e870e2c5870e2c5800000000000000f063e1f0f063c78f1e3c78f265c9971e3cb8f1e3c78f1e5f79b3e7e371f763c7833e3c78f1e3c7831e3c79f1e3c78f1e3c78f2e5c993264cb973e9f478f067d478347a8f47a5d26801c587161c38b161c38b161c587161c587161c38b161c38b168b0e8000f1780000000082006f000740cb971e5f78f2e3c79f3e0d069b366c78f364cd93360c19b773c983065c9932e801c587161c5871611bc00036203a066c78f360c197760c183060d06a8306ec1bb065c1972e0c183060c1a007161c5870e0c5870611bc00001803a060c1d503064c9931e4c793360c1d03064c997264c983060c1b00d068306a0c1a83506a0e8187161c5870e2c5870e2c5870e2c387168306804000000000000551b1e3cdd17760c1aaa817013970e2c38b0e1eaaa8d97765d551555606006f366cd9b2e9cd9740a060cd83060dd83060cb83060c183500002a838b0e2c38b0e2d5438b0e2c183062c187060c1d030740cbbb2e0cfb1f01a0d0683419f3eed1831eec783465cb83065d40001d030e2c38b0e2c38b41834187162c387062c008de000000000080003070fdf03a060c197260c1a0d060c1d03060c183264c1a7960c1831e3c78f060d0018b0e0c38b0e2c80018bc0000740e1e3e060c183060c1a0d060c38b0e2c0001d0fde0c1d03060cb93060c1a83067d060c1d03363c79b060c183264c1a7060c18306800c587061c587164000c5e00003060c1d03060c18306c830683060c1ef41a0d060ea89ef060c1d0389c0c993264d001d03060c1830e2c38b4183438b0e2c02000066f000000000183060e8183060cd831e0c1830744c1830740c9838997265c1b20c1a8306a0d068301a0e8183060c5830e0c187161c587161c5a0c1a0100000300000000001d030740c993264c1b20d068301a0c183066c183063c183064c1a8300000740c38b0e2c38b0e2d060d060c18b061c1830080000000000620000e8193264cb93260c793260d0697269c9a7263c9931e4c9931e3c79326801c587161c587161b000000740c78f265c98f064c98f06834b934e4d3931e4cd8f1e3c78f264c993400e2c38b0e2c38b1380000274e4cb932e5c997265cfa7d3e9f4b97099f539393c4d1931e3c9a3265cfa80007161c587161c587161c5a2c3a1c38b161c38b1600000000000000000f1e3cbefa8def366c9933eb377805550faa1e3c7971e3c797df32d46f7831e0cd932733bc78306831ea141c5871605555555555132e4cbcccc8341a0c180c1b4d55546c9a7260c183400aaaaa0e2c38b0e2c38b4183438b0e2c0aaaaaaaa365cbd2d4b5551fde0cd83360cf833e5e96677cc8341a0d0681555541c587161c587161c183168306ab565d5972e5cf9f3f1f8f9f3e7c79f1e7d1972e7cf9f2e5cfa7d3e9f4ba7d0038b0e2c38b0e2c38b0e2c387162c387162d161d000000041003780172e5cb972e1c587161c587161c587161c58716005c00581c 24 16777215 10 1023
def hc_70_1 : Nat → Nat := unpackHintV5 0xd3bdd0cd4d9cc2ee98b69f14aca67ea60da69eedc89aed0094c18b8c1a2a877928814d8b785e3c72318b6926436525005e91a555365750fd0e4a59a9409a703a45953541412ef5932a412d24d55b1e8d921805a21185a00c993b0735590001cd 0xf363cd972e5cb971e3cb9b066e371b066cd8f1e3c79b06a000c755545555550e2c38b0e2c38b0e2c38b0e1c58b0e1c58b5500360000000000000f363cd93264c9931e3c99327138993263c79336a0002aaa2aaaa87161c587161c587161c587161c5aa801b00026001bc2600000f363cd9b366e371b366c78f1e3cd9b2e5cb972e3c797018eaaaa8f77aaaaaaaaca9b536aaa4d5eaa974baa4d55438b0e2c38b0e2c387162c387162c38b0e2d555458b50e1d400d8001702e006f000001178004736acd9306ad59356bc1935e6e1935e6e1932e4cb932e4cb807e99f8fc7cf9b367c79f1e6cdaaa8001f3e9f699b4fa935793260cfa893264d264c987161c587161c5870e2c5870e2c587161c5870e2c5870e2c5a2c3a00bc000b817003780000000047369cd935e9d3934ebe1935e6e1935e6e1932e4cb932e4cb80bf555555549abd5498bf5654daa3d53e9f4b8002a1c587161c587161c38b161c38b161c58716aaa8b43a802f0002e05c00de0000000000555555545cbd554bf79b366cdd5545cbd5172e5cb8155546d9bf36bcf9b367d7972e5cbd555507161c587161c587161c587161c5ab56bd5cae5e8c7af1e8cb972e5cb972e5c056acfaf579f4b972e5c38b0e2c38b0e2c387162c387162c38b0e2c38b0e2c00000b8170037800003a070f8783060c18f1eaa0d926cf549a4d51e8f49a4d00e2c38b458740037a20306aaa50355a50740e5932e5e5932e5c78f1e3d55400155541d030e1c58b0e1c58b0e2c38b0e2c38b55000000000000400066c7d0fdf40c7d40e81831e3cb8f063c78f1e3d555555555506aca8347aaa3d5547aa3d52eaa800e81830e2c5870e0c587161c587161c5aaaa2d0ea000000000006f1010001d03878f8183265c18355506c9b47a4dbea9349aa4d2e9349a01c587161c3a2c3a0001bd101d00c1aaad2aa83a066c78f2e6c9972e6c9972eaaaaa000aa0e8187161c5870e2c5870e2c587161c5aa800000000000200031f543f7831e3ea0740cd8f1e5c19b2e5cd832eaaaaaaa9b4faaaa0d59536a8f541a8d5536aaa5d55001d030e2c38b061c58b0e1c18b0e2c38b55545a1d400000000000de202000306aaa0e81b31eccdb31eccd940d5694997265d55400155541d030e1c58b0e1c58b0e2c38b0e2c38b55000000000000400065cb83a060c7b336cc7833745f7d032f5132e4cbaaaaaacd3eaaaaa8356541aaab355546a8f54baa4d400740c187162c387062c38b0e2c38b0e2d5551687500000000000378808000c19b07178183260e1f2a83641a0d506cb54da3d2e934018b0e0d161d000de883cd8f366c19b8dc6c1972eaaa4cb932e0f1e5d5478f555555000550e2c38b0e2c38b0e1c58b0e1c58b0e2c38b55000000000000001e6c79b364e3713365cb97265c9971e3cbef1e3cb971e3c7aaaaaaaaaaaaca9b547aa4d46aa9b5552ea9350038b0e2c38b0e2c387162c387162c38b0e2d5551687500000000000378808000c78307031f03260e272a83647a3d0683541b8d52e9340583062c383458740037a26306ae5763063c78f1e3c7aaa932e4cb9326aaa3c783d540141555438b0e2c387162c387162c38b0e2c38b0e2d5400000000000100078f1f0f878f1e3c78f1e3c997265c78f2e3c78f1e3c797deaa8f4faaaaaaaaaed5951eaaa3d1eaa8f547aa5d526a007161c5870e2c5870e2c587161c587161c5aaaa2d0ea000000000006f101002955498f264c98f266c1d03060c1830720c193264c9aaaa8aaaaa870e2c5870e2c583a061c587161c58716aa00000000000000a3cd8f360e8183360cd93269cda7064c1972e4cb932e3cbef1e5c78f504550e2c38b0e2c38b00000541d03063d3a34e3c1a30740c1972e9c1972eecb8aa80282aaa83a060c38b161c383161c587161c58716aa0000000000000006c7c3f7c3e81d03063c18f66cc793260c7831e3c78f1e5c98f5554050e2c38b0e2c38b000001f43f78f1f40e819b1e3cd83260cdb3666c993066c1932e5cb9b264cbaaa9b4fa80a1c587161c58716000000c1830740c183066c18f060da060c193264c9935500041a0aaa20e8183060c5830e0c187161c587161c5aa8000000000000003a060c1d134997265c183060cd83060c783074aaaaaaaa2aaaa0e8187161c587161c583060c5830e0c1aa80000000000c5e00000ad5935713999346cc7931ecd1932e4cb932e4cbaaaaaaa000a8a1c587161c587161c38b161c38b161c58716aa000000000000000ad597565cb97555555559546a8f54baaa007161c587161c587161c5aaaa2d0ea00000006f1010001d0387c3c183060c78f0740c183064c193060c193069c18f063c193064c1a0d00e2c38b0e0c18b200440de5030740c78f1e3c1b20d068341a0c1d503060c1d03818f060c193060c19750000740c38b0e2c38b0e2d060d061c183060c18b00000000000000 24 16777215 10 1023
def hc_70_2 : Nat → Nat := unpackHintV5 0x8a0ce3c2a398e059be0f5cb4176e8ff39847c1b08ee6d085f06443002e99e21657bd4a6571a4f13062425d91052f007bc5b43a7ed919ead54c1e35c57566728d4b5926c7f88cb1ac39334a18f8e80a099cc435b3c19edf00671a182a22580bea4a00017d 0x3c78f1f9c1a793d9c1a800132e4cb8f1e3c793063c78f1e3c7aaaaaaaaa287161c587161c5870e2c5870e2c587161c5aa8003c00000000000078f1f0f878f1e3c7804cb932e3c98f1e3c78f2e3c78f1eaaaaaaaa9777aaaed5951eaaa3d1eaa8f547aa5d5438b0e2c387162c387162c38b0e2c38b0e2d55516875000780f003780000000000f1e3c7932e4cb8f1e3c7b306ae5733063c18000f1ea3d1e3cfa7d1e8f4ba25c1a8f06a1c587161c587161c587161c38b161c38b168b0e800000000000000f063e1f0f063c78f1e0133e7e271f763c7833e3c78f1e3c7831e3c79f1e3c78f1e3c78f265c9971e4c78f1e3c7971e3c78f54fa7d1e0d478351e8f4b972e5cbaa5dde1c587161c38b161c38b161c587161c38b161c38b161c587168b0e8003c07801bc000000000078f1f0f878f1e3c7805d5971e3c78f1e3cb8f1e3c7ab563cf8f478f1e8f1e3c7972e1c587161c38b161c38b161c587161c587161c58716000f01e006f00000028797a2e3c78f1eac1d51b063c7d0f878f1e0c0015d2b1e3c78f2e5cb97860e1b0c1c343d0b0e2c38b0e2c38b0e1c58b0e1c58b0e2c38b000000000000001e6c7d0fdf43c7d46c1d52b063c18f1e3c7c31e3c9af1e0c78f1e3c78f1e3c78f1e3e9a32f45c78f1e5c7931e3c78f1e3c0574ac78f1e8f3e3d1e3c78f8e0cda6c1c74b972e5c3d0b0e1c58b0e1c58b0e2c38b0e1c58b0e1c58b0e2c38b0e2c38b008000078bc0002e05c00de00003e82f45cb8f1e5cd83aa1e0cdc3c78f1f45c18002ba566c78f365cb972e6c19b4d833687a161c587161c587161c38b161c38b161c58716000000000000003e81f44e1e3c9930744c193263c98f266c9a3260c000574acd8f1e6c993264c983264c1930f42c38b0e2c38b0e2c387161c38b0e2c38b00800098006f09800003c7d50fde3c78fa8d83aa360cd9b1e3cd8f1e3cd9b368cd83268cd9b366cd935e6c19b465e8b971e3cb97265cb972e5cd932e5c0574acd8f1e6cd9b369b3e6d360cda6c19b4b972e5c3d0b0e2c38b0e1c58b0e1c58b0e1c58b0e1c58b0e2c38b0e2c38b008000000d8bc02e05c00de00000d5af0740c18f368cd8f068ca064d597265c9970740c19f06833e0d06ec19b064c1970740c187162c387062c38b0e2c38b0e2c383062c0205e000000002ba364c1935f544d5935e6dd935e6e1932744c265c99700993266cdc31f0c79b37554000ae959b8efcdaf064d79306be197264cbbf3f0d7e7e1a1e8587161c5870e2c5870e2c587161c5870e2c5870e2c587161c58010bc000b817003780005c2e000000e81832f45c2e5cb9706ad7bb460c7bb1e0d1d00003a060dd83065c197067c1a0cf8341d030e2c38b0e2c38b061c58b0e1c18b0e0c18b00237800000005c2e000003c78f1e3cd93366d593366dd8f1e4d78f1e3c78f1e4cb932e3c983c78f0079b1f0f878f1e3c78f363d18f2e000fd5ab8e3c78f1e6e193364cd9b865c9932e3c78f479b1e87161c587161c5870e2c5870e2c587161c5870e2c5870e2c587161c5801b00002e05c00de000000003e99b1e6cd93366d593366e193364d18f1e3c7935e4cb932e4c98f1e4c00dd3371b8d9b264c98f1e3c78f1e000fd5ab8e6c78f366e193364cd9b865c9932e6cd9b4d9f3687161c587161c5870e2c5870e2c587161c5870e2cd8b161cd870e2c587161c5801b00002e05c00de000000009e9397a2e5cb972e9daa54e6d38f4e3d39b2e0c00064fa7d2e97694fca1e8587161c587161c5870e2c5870e2c5a2c3a00000000000001313264c9934f49c9830000983a260c993264c9b2327d3e93260f7a4c1a4c38b0e2c3d0b0e2c38b0e2c38b4587426001bc020002600002aae959f1e7cd9f1e7cdab0754ac19f064cf9f3efcf9f26bcf833e7d7a37e3d78f7e8cbd172e4cb972e5cb9f265cb972e5cb80cefa5a8f9f4fb1cf9f067d4f835fa974ba1e85870e2c5870e2c587161c5870e2c5870e2c587161c5a2c3a0100001f1780005c0b801bc00015d2b2f45cb972e5d583aa3e0e19b863e18f866d400151555555543d0b0e2c38b0e2c38b0e1c58b0e1c58b55008000b8005c00000000574ad583aa560d7a38e3d78f8e8cbd172e5cb9701559deaab4d3eaaaaaa9f536a8f561aaa9357aaa5d526aa87a161c587161c38b161c38b161c58716aaa8b43a8040005c0b801bc0000045e0006cd9b37320e8183260e59b866c993066c19b1e3cd932e4cb81f3e3d1e8341a1c587161c587164006c36170b81bc79b1e6cb972e5cb8f1e5cd83371b8d83368f1e3c7a97060007cfa7da623d2e9747835360d438b0e2c38b0e2c38b0e2c387162c387162d161d00000000000000a50740cd8f1e6c19b374cd83360c0fa8f36aa87161c59170b81bc479b1e6cd9b8dc6cdaa6c19b8dc6c19b363c78f1e6cd9b064cf9b366cd9b26bcd83367cb972e5cb8f1e5cb932e5cb932e5c03e7d3ea3dde3c7a8f1e3cd835360d4ba5d0e2c38b0e2c38b0e1c58b0e1c58b0e1c58b0e1c58b0e2c38b4587400d80000001702e006f00001e3c78f2e5cb971e3c78f860d3c9e860c78f1e0c78f1e3d4001551555555438b0e2c38b0e2c38b0e2c387162c387162d540198001700000000001e3c78f36ed3c6e8eec78f1e3c78f1e3cb972e5c78f1e3c05547bbd555555558eaca8f586aaa4d5eaa97549aaa1c587161c587161c38b161c38b161c58716aaa8b43a80330002e05c00de000000003c78f1f2c0e5740df831e3c78f064c1d77f0df93260df83265c99703e7c78f369b41a0d162c38b0e2c38b0e2c801f86c2e170378f1e3c7972e5cb8f1e3c7bf06ae573f063c7a8f478f1e0c000fa7d1e8974ba6c1a9f06a1c587161c587161c587161c38b161c38b168b0e800000000000000f1e3e1f0f1e3c78f54d83571b9f831e3c9af1e0c78f1e0c78f1e3df8f1e3c78f1e3c7972e5cb8f263c78f1e3cb8f1e3c7807d3e8f1e6c78f547bbcf835360d4ba5d0e2c38b0e1c58b0e1c58b0e2c38b0e1c58b0e1c58b0e2c38b4587401f80000001702e006f0000065c1aa0c18307132703506aa1c5871611bc00197060cd831e0e001aa0ddeaa0d9069749a0d06a83555062c3835162d0e1d08de0030b800a6cdc6e360cd83a3703064c1a7369cd93260cd83363c79b2e5c997265c15555438b0e2c38b0e2c20d801b0d85c2e06f 25 33554431 10 1023
def hc_70_3 : Nat → Nat := unpackHintV5 0xdbe067d79912d0a9bccac978c17e53bda4f6b8a540b1adbea7e672a225709a65f08d5b43853e07807532785a0770e9dc6929f05bef4f538e184c59cd4519d03cee0b361db430e14f2b81581f131c1abd151415aa0ec953055a5c03bc670000ef 0x3a063cd8f2e4d5550e2c38b000740c7808cba32eb3bd551a7daeaa4d26a9b47a5d2e9349aa1c587168b0e8000022f0f83aa460c7d2350005745ed932e5ed932e5d18f1e5d51555546aaaa1e85870e2c5870e2c587161c587161c5aa8000003c0001e000002c001d0302745c98f1e6c993268c9b3264c99b266c9971e3c997265c993264d55555438b0e2c38b0e2c3870de3c1e000b07d23460ea9183015d17463c797468cb97465cbaab3bd46aaaaaaaa9f536a8f54da8d5546aaa5d55543d0b0e2c38b0e1c58b0e1c58b0e2c38b55545a1d4000de0f0078000000022f0058003068c184032e4c1aa8377a83641a0d506cb54da3d06a83161c1a2c3a00000a3cd8f360e8183460d19b369d1a7066c1813264e27132e4cbaaaaa87161c587161c58006f1e0f0596c1a793d6c18f463d1a800132e4cb93265cb93065cb931e3cbaaaaaaaaa287161c5870e2c5870e2c587161c587161c5aa800000000000000f463d1a3472391a300997265c98f1e5c9932e5c9932e5d555555552eef55559536a8f54da8d5546aaa5d5438b0e2c38b0e2c387162c387162c38b0e2d555168750003783c01e000000008bc016000e81813264cb932e4c99b1e3cd9b466d183068dddb360c1cb1f3e0d06974ba1c587161c587161bc783c00761b0583d18f464cb932e4c78f2ecc1ab95ccc1800f0605cba934b973e9f4fa3d2e89706a5c1a87161c587161c587161c5870e2c5870e2c5a2c3a000000000000003d18f468c1a391c8c1804cf9f89c7c99b1e3c78f3e6c99b067cfa33e4cf833e7cd9f464cb932e4c78f2e4c9972e4c9972ea9f4fa7d1e9f06a7c1a972e5cb9754bbbc38b0e2c38b0e2c387162c387162c387162c387162c38b0e2d161d0003783c01e0000000002c007a31e8d1a391c8d1805d597463c797468cb97465cbab568c78f468cfa3519f46972e1c587161c587161c38b161c38b161c587161c587160006f07803c00000580031e0e81c3c7c0c1c017065c183060c183065c183060d0683060c187161c583161c1870e000000e8060ea8183a1e3c78f1f030740c18f1e3c783060c1d03063c18f060c9a0c1934193064c1d030e2c38b0e1c58b0e1c58b0e1c5870e2c383062c0000000000000018fa1e031e3e80001d031e3c78f065cb832e0e81831e0c7833e0d067c1a0c1970740c38b0e2c187162c387062c38b0e2c383062c0000000000000007d0f1e0ea8b831e0c000a2e3c78f1f43c78f878f574ac78f1e3d98366b306cd2e4c9970f42c38b0e2c387162c387162c38b0e2c38b0e2c00000000000000b972e3c1d50f063c18f1e3d98f1e3c78f1e0c78fa1e3c78f1e3c78f1e0517df45cbd43c7931e3c78f1e3cb971e3c78f574ac99f76bb3e4d1e0c7a3c18f478f1e3cb93265c3d0b0e1c58b0e1c58b0e1c58b0e1c58b0e2c38b0e2c38b0e2c38b0000000780f003780000003060c1d03060c18f063c183060e8983060e818f0703c78f0740c1830683060d060c183060c1830740c183062c187060c38b0e2c38b0e2c183060c000000600000000003a060c183063c0001d03078f1e0c1930740c183060c1830683060d060c1830740c38b0e2c183062c187060c38b0e2c183060c00000000000000997263e878f1e3c78f1e4c9d513de3c78fa1f0f878f015d2b264c9931e3c78f264c9930f42c38b0e2c38b0e2c38b0e2c38b0e2c000000000000078f1e3e79395c4c78f000265c9972e0f1e3c78f1e3c7ab563c78f1e4cfcf679f2697264cb87161c587161c5870e2c5870e2c587161c587161c58000000000000000fa1e3daa51e0c0013d171e3c78f4e4cb974e4cb97191e8f6947ca5d3e87a161c587161c38b161c38b161c587168b0e800000000000004c8f1e3c98f263c78f263f383a063c78f1e04c9932e4c78f27320d0697261c587161c58716003c1e06f051e3c78f0740c19f067c9933f3d383260c780acb932e4cb8f1e3c7cef9a1e3c1a0d0e2c38b0e2c38b0000054783aa1e0c7831e3c79f1e3c78f1e3c18f3e3e878f1e3c78f1e3c780ae8b9f3e5cb9f2e5c78f1e3c78f2e3c78f1ecefa5a878f067d478347a8f1e8f47974fa1e85870e2c5870e2c5870e2c5870e2c587161c587161c5a2c3a0000000f01e006f0000000740c780acb8f1e3c7acef1eaa9f47a3d2693567b3d52e935438b0e2d161d0000045e0fa1e3c1d51f06a000ae8b8f1e3c7bb265cbbb265cbaa2aaaaaaa87a161c587161c38b161c38b161c58716aa000f0011800000000000e81813a2e3c9931e3c78f1e3c793663c78f1e4cb931e3c98f1eaaaaaa1c587161c587161c38f0781bc00783aa1e0c7d0f015d171e3c78f1e3cb8f1e3c7aab3bd1e9f555547aaaaa7d47aaa8f47aaa3d51ea9755550f42c387162c387162c38b0e2c38b0e2d55516875000780f0037800000008bc0001ab0f1f03060c1aa87161c580031e0c1c0032e4c1aa8377a83647a3d0683541aa835418b0e0d161d00000 24 16777215 10 1023
def hc_70_4 : Nat → Nat := unpackHintV5 0xd9707ed4b52fcb3a5fc55d77bd65feb6c1a9b1555bac4544a30e4e9cc193978d4d8ef2278a811c8481807ca5f7758dc66bd66e66c9435eae075721e34f61f04257433b21cd365d312dfe1829811f25cced1e11ef1709c211616a0c394a00030e 0x200d8f1e5c9970750341a1c58716001308993aaa89d50fa363d1ec4c9d44cb83064cb83641a0d060e0e1ea162c38b0e2e20378004c06043eaa375546eaaaa819faaaa56aa8bd51b1e3cb83365cb9b065e819f5a65a6647bbc18f5063c78341b41c3d550b17541c587160c38b161c383161c587168306904006f000000003600030014002a8783aaaaa4e4cb974e4cb971e3c78f555555478aaad5070e2c5870e2c587161c587161c5aa800000000000000143c7d550f475533aa8bd50f1e3c7aaaaaaa3ddeaaaacaab32ab2b2a3d4baacd55a0e1eaa858baa0e2c38b0e2c38b55545a1d4820037800033001000045e0015540014b35543c78f1efc9972efc9972f320c7a88f778306b4a0d06d507161c5870e2c5870e2c587161c5a0c1a0000000000000c0080aa1e0c1b31ecc783064c7931e3c78f5aa1e4c98f1e3cb971e3c1a0d1e6c7a3ddea1c587161c587160000003e87c4e7d5544c9d50f51f13275132e3c783060d9068341838387a858b0e2c38b162e20378004c0605031f555543eaaaa1f550faa56aa8bd50f063c18f1e5c78f1e3e06b4b320c79b063d51eef068368387aaa162ea8387062c187162c38b0e2c38b0e2d060d20800de00000000fc0006002800555551b07546c9972e6c9972e6c78f2eaaaaaaa8ab541cd870e2c5870e2cd8b161c587161c58716aa00000000006c0000a4f551ba81ccea81974e0cd8f1e5d555555156aa818b0e0c38b0e2c38b0e2d548018006f000036002000143c7d551b475533aa8bd51b1e3cbb27d5555955551eef5565559955956654da97559aab41c3d550b17541c587161c58716aaaa2c5a870ea41001bc0000d800800022f00080aa264c993555549bbd555595566536aaad507161c587161c5aaaa800000000009bc005000aa4e3d39b4e3d39baa260eaa8997265d555555552e2b541c38b161c38b161c587161c58716aa00000000005c0000021f5523aaa275545cbd5132e4cbaaaaaaaaa5ddeaacaab32ab2b2a6d51ea9755a0e1eaa858baa0e2c38b0e2c38b55545a1d4820037800017001000045e00155544cb932f4000ccdb31ecc7b3374b35320d06832ea25dde0c1ad2d507161c587161c5870e2c5870e2c5a0c1a40000005c0003e1f0000600010faa91d55033f555547eaaa819b3e3c18f3e6e275517aa265c9975606b4b320d06832e5c19754bbbe8387aaa162ea838b0e2c387062c187162c38b0e2d060d20800de00000030f800170001800043eaa47555545ea8b978fcd4d5172f41c3d550b17541c587161c587161c5871641001bc000000000183aa060ca063e264e899b060e8183060c1931e3c78f260e8183064d060c9a0c783460c983260e81870e2c5870e2c587161c587161c587060c58000000000000003468c91c0d1805003a060cb97960cba31e3cb83a060cf83419f06831e0d183065c1d03061c58b0e1c18b0e2c38b0e2c38b0e0c18b000000000000000a2e0e8b831e0c0007d2327172f45cb945c98f1e5d98366b306cd574ad18f1e8cb93265c387162c387162c3d0b0e2c38b0e2c38b0e2c38b000000000000002e5cb8fa463c7a3363c793368c1d523064c1a3468cda346cd193066d18145f7d172f5131e3cb93265cb93265cbaba564cfd3699f26a31e3d1a3068d460d1a5c9932e1e85870e2c5870e2c587161c5870e2c5870e2c587161c587161c580000001bc1e00f0000016000c1830740c0018f00740c183264c784c1d03060c1a0c1834183060c183060c1d03060c18b061c1830e2c38b0e2c38b060c18300000000000000064c1d13263c0264ea363c797264c993265c9c4c983260f59f4fa1c587161c5871600015c5e003a060c183066c183063c183060e8983263c2e0c1d03260e0740c183060c1830683060d060c1830740c38b0e2c183062c187060c38b0e2c183060c000000006000000003564c1d7a3ea8f0079b1e5c9932693264cb934993060d264c9930e2c38b0e2c38b00000269c9eb1e013264cbaa9349a4ebb24d066d1e9349aa1c587168b0e8000013571387a31e8c78f000265c997268cb93463c2e5d5ab3e4d267d463c7a32e4c9970e2c38b0e1c58b0e1c58b0e2c38b0e2c38b0e2c38b000000000000000a5a468f060003e91a7265cba7265cba7a2e8c78f2e7e5a5193e7d1ea32e9f4387162c387162c3d0b0e2c38b0e2c38b4587400000000000002647931e6c9a3b64c993264c993366c1d030264c997264c9939906834b930e2c38b0e2c38b261b000378f07802c50740c193067eba73e4c9833e0c79b1e6c7804cb932e8cba32f3be681a0d3e8c38b0e2c38b0e2c0000151f48c78f3e6c78f3e6d183aa460cf833e7cf9f368cf9f467c19b3e02ba2e7cf972e7cb97463c797468cb97465cbb3be96a3e7d1ea33e0d4f8352e9f43d0b0e1c58b0e1c58b0e2c38b0e1c58b0e1c58b0e2c38b458740000000de0f007800000b00 24 16777215 10 1023
def hc_70_5 : Nat → Nat := unpackHintV5 0x820b0d3d6de61dc13d6e8616a6fcf18b6a7501a49c28ccfd546304deaf8f7cd6d0bdca92b574dc3b4a58c555135644805e533d68b19ba0c50d06b2662816d2c673693e094c859e5a3badc81a5ede0b736f04f03261d32940aeaeb82f3a080afb2800015f 0x3a060e81c3c793060e8183060c183060cd83de0c1a83064d41b20d068306a0d26ef060c183a061c587161c587160c383060c1a0c1a0c8260f0984c064c060c4060b0380c1d50fde0c183a8183aa060c183063c18f060c19b068c183067c183060c1833e0c183460e81971e3cb83060c1972e0c193060d506c8341a0c1a0d4183067d4183060c1aa5dde0e8187161c583060c5830e0c1830e0c183060c587161c5a0c1a0c8460f0183006fc019b0060c0b85c4060b0380e81830744c1932e4cb83060c1bb060c1bb060e94193060c1836068341a0d1060d418350740c38b0e2c38b0e2c183062c187060d060d000000018bc0000193060231e3d1c4c9c0c19b06ec1c9306003060d068341a1c587160c587060c8763b0b85c0603018002030581c0740c183a2e0cb972e5c190376eddbb8b972e0c183066c18306ec183a5065c18300060d81a0d068341a0d068306a0c1a83a061c587161c587161c587160c183160c38306830683a060e81972e5cb832066cd9b37172e5c1b20d068341a0d0683a061c587161c587161c58716830683a060cbd17065cb972e0cf9f768c18f763c1a3a52e83819f63e8341a0d06832ea0cba83a061c587161c587160c38b161c383168306832076170b80d780bc10182c0e03070fdf03a0740c183060cd9b064c983060c78f1e3c197260d001a0d06003161c187161c58300018170183060c1d03060c19b063c1830740c001930264c99306c80030600d0683441d03060c18b061c1830e2c38b0e2c38b41834000000000000000dab364cdc4e36bc9a3363c98f368c997265c997265d4000fa7d369f4b970002e887161c587161c5870e2c5870e2c587161c5a2c3a2f00000f8005c003e001f3e7e3f1f3e7cf8f3e3cfa32e5cb972e5cb9754fa7d3e9f4b972e5cbaa5dde1c587161c587161c38b161c38b161c587168b0e801f03e7c0b85c43e0b03800fa363c79b363c79b366c1d513066c19b5e4cd93466cd9b564c193465cb972745c9932e5c9932e5c78f2fbc78f2e5c78f1eae959b366d367cda6c78f364c19b4d832697264cb87a161c38b161c38b161c587161c38b161c38b161c587161c5871606f202000000000000001e0ea87831e0c78f1e9c7ab1e3c78f1e0c7af1f43c78f1e3c78f1e3c78f1e4e8b93265cb93265cb8f1e5c78f1e3c78f2fbd5d2b367d5aacf9b47831e8f063d1e3c78f2e4c9970f42c387162c387162c387162c387162c38b0e2c38b0e2c38b0e2c0de40403c5e00000000000000e8183060c1934e0c993060c183363c18f47a0c993060c1932e0d068341a0c183161c187161c586f8800001d03060c19b063c183060ea8183060c1af060c19f060c1ab060c19f541d03060c19706ac183363c797060c197060c18306c83060d4183547bbc1835060c18341a0e8183060c5830e0c187161c583060c5830e0c187161c5a0c1a06f202000000000000000740c18f1e3c78f063c1d0306ecb974e9c1971e3c78f55555547bbd555506aca8357aaa9d56aa8352eac75541d03061c58b0e1c18b0e2c38b0e2c38b55545a1d40de4040000000000000031e3c183a060c183064c983269c183063d4783264c18f1e0c18341a0d0683060c587061c587162c586f880000183aa060c183063c18306ac183063c18306bc1d03060c18f063c183541d03060c19706ac183060c183060cb8f1e3c783641835060d4183060c1aa3dde0d0683a060c183160c383060c383060c183161c587161c58716830681bc80800000000000050000183360c183060e060c183069c183060c19b1e3cbaaaaaaa2a83060c183060c187161c587161c5aa9001bc0600000000003cd8f360e8183260cd934e4c993064c1831e3c1d132e4cb93264c9932eaaaaaa1c587161c587161be20986c000001d03063cd9b1e3c19b0740c19b2e5cda7065cd8f1e5d4eaaaaaaaa8f77aaa0d566541abd5536ab5541a9755550740c187162c387062c38b0e2c38b0e2d555458b50e1d40de404000000000000000e81831e9d1a71e0d183a060c9972e4c9832e4cb932eaaaaaaaa9777aaa0d59506af5553aad5536a8f541aa83a060c38b161c383161c587161c58716aaa8b43a81bc808000000000000001d03060c1a3063c183060ea8183060c19f060c1ab060c19f060c1af060c18f060c19b0740c183065c193060c997265d506c8306a0c1a8341a0c183060d52eef0740c183062c187060c38b0e2c187060c183062c38b0e2d060d0379010000317800000000000ae95ab1ead1ab1ead1aba2eacb9756acb972e5d5d2b567d5aacfab4b970f42c387162c387162c38b0e2c38b0e2c38b0e2c0de40400000000500055131ecd1b31e4d1955544cb932e5ea899f66b33e4d66ccb93265cbd5070e2c5870e2c587161c587161c587161c5800000000000000500055555172f543c7d5503cb8f2e5ea8d83369b066d363c79b2e4c997aa0e1c58b0e1c58b0e2c38b0e2c38b0e2c38b00000000002e000040550f1e4c98f263f7d5543c7d5544cb93aa264c993363c79b264d264daa0e2c38b0e2c38b0e2c38b0e2c38b0000000000000021f551baaa37555544d1d555172e5e89d55172f543c797de3c7972e3c78f8fcd4d51b1e3cd93366d367c9a5c9932f41c3d550b17541c587161c38b161c38b161c587161c5871641001bc00000000b8006c00aaa000a1e3eaaa878f1e3c1e3cbef264eaaaa878f1e3e38366c706cd2e4c997aa0e2c38b0e1c58b0e1c58b0e2c38b0e2c38b200000000002e00000050f1f555543eaaaa1f550faa1e3c7c4eaa2f543c7971e3c78f1e3cbef8fcd4d50f3e3d1e3c7a3c78f1e5c9932f41c3d550b17541c38b161c38b161c587161c587161c5871641001bc00000000b8000050005554d2d51b265cb9b265cb9b1e3cbcc8306b4a283506836a8387162c387162c38b0e2c38b0e2d060d0000000000000600400f363cdd513364cd8306ccdb3260c1ad51b2e4cb972e6c9932f40d068f778f478f50e2c38b0e2c38b00000 25 33554431 10 1023
def hc_70_6 : Nat → Nat := unpackHintV5 0xe30dc5dc05c2d449efcf2549c739fbc17172bad9a6b3d9c0acb9c8a6e5759fedbe9b891991f2668be9828401fa7dbd9175e9f56ee1c26a7d1960827f5935d353dd564d45a64609cf40bd533872132adf6523d5c219be861251db084e81000213 0x541c8e068c1c8cfd033e0e81832e5d3832e8c78f2eaaaaaaaaaaa0e81830e2c5870e0c587161c587161c5aa83201af04ebc1183c2e0882c0e03060c1d03060c19b063c1836a8183064c98f1e4d55555555541d03060c18b061c1830e2c38b0e2c38b55064030600c98130784c26220b0380e818307544f7a4c78f2e0c183066c183063c183a9555555555555541d030e2c38b0e2c38b060c18b061c18355064230784c260306030060cdaf04416072aaaa8defaaa5556a9a27bc98f1e4d9555555555aaaaa0e2c38b0e2c38b55899444130784c26220b0383d18f464d9c4e664cf8f1e3c7972e4cb97265c9a31e3cb97555555555555438b0e2c38b0e2c387162c387162c38b0e2d5466230784d78135e04cb84c4416070b971e6c79b8bef8bd2a83a060cd834e9d3af366c1a7060c02e4d393265cb97400e2c38b0e2c38b2005e1b11817440740c1d03363c797555455060c183360000cb83060c98306a0000e8187161c587161c5aa83060c5830e0c18011bc0000000004400079b1e6c993264c997263c793555455260c9c4e260c99b000264c9a80007161c587161c587161c5aa870e2c5870e2c580270000000000000079b1e6cba72e6c78f2eaaa8aa6d7a78dc9cd9f0002e5d39b5e5cba80007161c587161c587161c5aa870e2c5870e2c5802f0460000bc10010007a31e8cb97463c797555551eef5555953ea5d555438b0e2c38b0e2c38b0e2d555458b50e1d41183c2e088a080b0380c1aaab40d56941d031e3c78f060c1831e3c78f55555555550740c387162c387162c38b0e2c38b0e2d541912cd84b3603c1e170b8882c0e030020997265d54bbbd41b2bdb6a9b4daa3d1e835438b0e2d161d060301e171004360b01a31f43f7d031f503a060c78f2e3c9831e3c78f1eaaaaaaaa9777aaa0d595068f5547aaa8f547aa0d541d03061c58b0e1c18b0e2c38b0e2c38b55545a1d41900c780f01e0f0b85c445040581c9a55a5460d556a8b8f1e5ea8b83a5555555555aa0e2c38b0e1c58b0e1c58b0e2c38b5588460f139b04e6c0b85c441607287efaaaa4755171e3cbd45e274aaaaaaaa9777aab2b2a6d51eaccaacaaa5d56a838b0e2ea858ba0e1e838b0e2d5551687588460f2824e05c2e222826c0581ca5551e0d55698b83aaaaa1e3c78f66555555552eaa1c38b161c38b17541c587161c58716aa9cd827361103c1e170b8882c0e5543eaa87ef89d545ea878f1e3d93eaaaaaaaa9777aab2aaccaacaca8f547aa5d560f550baa0e2c38b0e2c38b55545a1d64e141103c1e170b888a0a70160701d20c1aaad2aa83a065c78f2e5c9972e0c18306aaaaaaaaaaa0e8187161c5870e2c5870e2c587161c5aa8321183c8e6c239b02e17110581c06040132e4cbaa9777a8364da3d5ee754da6d506a87161c5a2c3a0c460302e20086c03831f543f7831e3ea0740cb8f1e5c1932e5cb93065d5555555469f54bbbd5506aca9b547aa0d46aaa355506aa0e8187161c5830e2c5870e0c587161c5aaaa2d0ea0c8460f01a304605c2e222826c0581c541d03063d3a34e3c1a3065e8b83065e8b9707172e5cbaaaaaaaaaaa83a060c38b161c383161c587161c58716aa0c806bc13af01d85c2e220b0386c7c3f7c3e8797263d541d03063c18f264c79b360c7831e3c78f0062007161c587161c59000f0d83c0ba203a060e8193264c9aaaaa283060c19b060c18f060c00193050000740c38b0e2c38b0e2d54183062c187060c008de000000000220006d39b265c997265c99755554536bc9c6e266d1931e6c79346004cb8280007161c587161c587161c5aa870e2c5870e2c5802f05e00005c1001000b972e5cb972e5d55552eef55559546a8f54baa87161c587161c587161c5aaaa2d0ea005c2e2228202c0e03a060e818f1e3c78307540c1830740e063c183506831e0d9068341a0d060d418350740c38b0e2c38b0e2c187060c183062d060d0640f0785c2e033600c182030581c060c1d0fdf40c1d40c1d503060c1831e0c183060c19f060c18f060c18f063c183063c1a30740c183065c193060c78f1e3d506c8306a0c1a8341a0c183060d52eef0740c183062c187060c38b0e2c187060c183062c38b0e2d060d064030600df80f0780c018302e1710182c0e55555171e3cbd5551f363c783060c1d2cd4c8341a0d9060d696a838b0e2c38b0e2c387162c387162d060d88460f0b85c566c159b04060b03943f7d55503aaaa819b1e3c18f3e6eaa8fd033f55545c78f2f51789d2b320d06d2c0d41972e0cbaa5ddf541c58717542c5d070f41c383160c38b161c587168306c423079412b03e6c019b02e1710182c0e555550f1e3c7d55503060c18f1e3c7d2cd4c8341a0cbb25c19706b4cb541c587161c587161c38b161c38b168306c40f0785c2e2b360acd82030581caa81d550fdf40cfd55551faaaa063c78f063c78f89d545ea878f1e3d5a067d6996641a0d065cb832ea9777c1eaa17541c587161c383160c38b161c587168306cac28220783c3eac019f02e1710182c0e03a060e81971e3cb8307540c183818f060e8183506832e0d9068341a0d060d418350740c38b0e2c38b0e2c187060c183062d060d064230785c2e033600c182030581c 24 16777215 10 1023
def hc_70_7 : Nat → Nat := unpackHintV5 0xe28ddedabdf4d5415fcea9a6c789c8c045d1bac161b52d65acc21bac3024a6d1589e6e19962213891b4281bdd777a6866f22216761f05e663f5771bd5221544ac9d64319ec3b29fc33fdcb29e28723699e1a6a401455850d41c50765770001d9 0xe81830744d1e3c78f060c1831e0c1831e0c1d2aaaaaaaaaaaa83a061c587161c587160c183160c38306aa0c81e0f0984c060c0600c19b5e0882c0e0f1e3c7936713998f1e3c78f1e3c7932e4cb8f1e3c78f1eaaaaaaaaaaaa87161c587161c5870e2c5870e2c587161c5aac71983c1e135e04d7813098882c0e172e3c78f1f17df17a550740c19b069d3a75e6cd834e0c0185c9932e801c587161c58716400bc3603cb8882c0740c1d031e3c78f554555060c180031e00cb83060c98306a0000e8187161c587161c5aa83060c5830e0c18011bc0000000004400078f1e3c993264c78f1e3d55155498327138983001e3c099326a0001c587161c587161c58716aa1c38b161c38b16009c00099bc00000004400078f1e3cba72e3c78f1eaa8aaa6d7a78dc9c0078f02e5d39b5e5cba80007161c587161c587161c5aa870e2c5870e2c5802f0007817001001016003c78f1e5cb8f1e3c7aaa3ddeaaaaab2a3d4baaaa87161c587161c587161c5aaaa2d0ea03c1e170445040581c063c1d03878f818391e0cb832e0c183060c1832e0c183060c18f068341a0d160c38b0e2c18b0e0c3877e3f01803a060c1d5030743c78f1e3e060e81831e3c78f060c183641a0d060d41835068341d030e2c38b0e1c58b0e1c58b0e1c5870e2d060d0640f0784c98132604c262030581c2e0132e6c063c1810f1f030723c1815cbbf2e0cb83060c18f068341a0d160c38b0e2c18b0e0c183c060301800fc0607063e8783063c7d28f41c0e818f1e3c7832e5c197067d8fa0c7a0d1e0cfa833ea0d068385c0c587161c5830e2c5870e0c587161c5a0c1a0c81e0f01af05e05c10182c0e03a060c1d503060c1a83418f0740c78f1e3e818307031e0d9068341835060d41a0d0740c38b0e2c187060c183062c38b0e2d060d0640f0780cd8030605c2e2030581c060c18307540c183060c783060c183063c183060e8183060c7831e0c1ab45f7d0307503260c183060cb8f1e3c783641835060d4183060c1aa3dde0d0683a060c183160c383060c383060c183161c587161c5871683068320183006fc018030603c1e170b880c16072aaaaaa966aa878f1e3c183060c78f1e3e6418f591eef060d6941a0daa0e2c38b0e1c58b0e1c58b0e2c38b4183620783c566c159b02e1710182c0e5540c7d55550faaaa87d543ea95a075545f78f260c7831e3cb8f1e3c7c0d6966418f3e0c7aa3dde0d06d070f5542c5d5070e0c5830e2c587161c587161c5a0c1b2b0a0881eac018f01e0f0b85c4060b0380c1830740c183063c18f060c183a260c183a063c1c3c78f1e0d9060d41835068341a0d0740c183062c187060c38b0e2c38b0e2d060d064030600cd80f0784c262030581c0740c183060c7a8341830740c78f1e3c183260d9068341835060d41a0d0740c38b0e2c183062c187060c38b0e2d060d0640f0780c18032604c262030581c1e3c78f9e4e9f131e3d47a3c7932e4cb8f1e3c78f1e3c78f3e9f47a3d267d4b9752e5d267d0e2c38b0e2c38b0e1c58b0e1c58b0e2c587162d161d01e0f09af026bc0984c43e0b0380c1830740c0018f00740c183065c193060c78f1e3c1b2000c1803441a0d0740c183062c187060c38b0e2c38b0e2d060d000000000000000060c1d03060c183366c1af660c183063c783408bef81d132e4cb8341a0c0062c3830e2c38b000603c062c260c9c4e260c78f1e3c78f000264c993264c98f1e3c79f4fa4c18000f449a4d0e2c38b0e1c58b0e1c58b0e2c38b0e2c38b4587400000000000000179b95c6d78f1e3c7a80017565cdaf2e5d7972e3c78f1e7d3e9b3e0003d12e9f438b0e2c387162c387162c38b0e2c38b0e2d161d00078003c00003e02c0078f1f0f878f1e3c7aa5cb8f1e3c78f1e5c78f1e3cfa7d1e3cf8f1ea8f77974fa1c587161c38b161c38b161c587161c587168b0e80f01e3c0783c2e087c160701835550740c183060c78f466daa06ab4a5c78f2eb355555555550740c387162c387162c38b0e2c38b0e2d54190ccd8333608c1e170b8882c0e032e5c1d03063d19b1e3c19ba2fbe8197a8b8f1e5d66aaaaaaaa8f77aaa0d566541aaab355506a5d526aa83a060c38b161c383161c587161c58716aaaa2c5a870ea0c8066c199b0460f0b85c445040581ca555aaa3e0ea8b83555a62e3c79755555555550e9c387162c387169c58baa0e2c38b0e2c38b554e6c139b088460f0b85c4416072aa1e3eaa8da3aaa2f5545f7971e3cbb27d5555955551eef5565559955956654fa974baa4d5568387aaa162ea838b0e2c38b0e2d555458b50e1d636141108c1e170b888a0a701607151f48c78f3e3c79f6745cf973e5d18f1e5d5653ea7d550f42c38b0e2c38b0e2c38b0e2d5553907c3e230785c8e220b0380c1aaaa0c1c0c183360c18341832fbc183060ea2e3c797555555555060c183060c1830e2c38b0e2c38b5506030183019b1183c2e17110581ca4f551ba81d03060cb9741832fbcb8f1e5d555555556aa818b0e0c38b0e2c38b0e2d5636500c4e230785c2e220b0394aaa3e264e899b0740c183060c1c83064c78f26aaaaaaaaaa1c9870e2c5870e2c98b160e8187161c587161c5aa932604c980320983c2613110581c 24 16777215 10 1023
def hc_70_8 : Nat → Nat := unpackHintV5 0xe2ee02da9e14d29602cfccb2c73a25bf2206bbbcd9b6dd38ae721ba6460b9dc2219083508979c27f1e97775df07345066e513d65ce215d422357856f5091bd4b654b440dd63c81e33476032d7dbe23e6661db98b158a0c0e4dcf06f9d50001be 0x3e8d9b07546c1972e5cbd171e3cbef1e3cb971e3c7aaaaaaaaaa9b2366c78f366cd9b366cd9b365cb972e8a1e8587161c5870e2c5870e2c587161c5aa87161c58f07543c18fa1e3c78f2f45c78f2e3c78f1e3c797deaa8f4faaaaaaaa9b2763cd8f1e3c78f4e3c78f1e5cb972e8a1e85870e2c5870e2c587161c587161c5aa87161c58fa1e9e8b8f1e3c7aaaaaa9b2363c79bde3c78f1e5cd9b2e8a3c1840f063c78f1e5c78f1e6c78f50451e6c787a161c587161c58716aa1c587161c38b161c38b160e819b1e3cbd1b2e6cbc741aaaa5c7972e6cb87161c58fa369e8b9b1e3cbaaaaaa9b2366cd8f1e3c79bde5cd9b2e8a6c1841b066cd9b2e5cd9b365cba8228f1e3c3d0b0e2c38b0e2c38b550e2c587162c387166c58b0e6c387162d3d1b2f45cb972e5d555554d8527366cd9b2e5cbef2e6cb97454e0c21383366d38f4e3cd9b2e5cda822972e5c3d0b0e2c38b0e2c38b550e2c38b0e1c58b0e1c58baa2e5cbaaaaaa9f25ebcbaf2e8a1e8587161c587161c5aa87161c5d5172e5d559deaaaaa7d51aa3d52eaaaa1e8587161c587161c5aaaa2d0eaac802e088a20a02c0e0307540c183a063e264e899b060e8183060c1931e3c78f260d9060d41835068341a0d0740c387162c387162c38b0e2c38b0e2d060d064132604c98130784c262030581c067cf8391c0d18391b4a0e81832e5e5832e8c78f2e0cfb1f418f5063d41a0d068341d03061c58b0e1c18b0e2c38b0e2c38b418341900d784b5e08c1e1704060b03940c1d03060c1a831e0d0740c1c0cbd03060e81971e3cb8306a0c1a8306c83068341a0d060c18b061c1830740c38b0e2c38b0e2d060d060c019b0064230785c2e2030581c060c183a060c183360c783060c1d503060c183060c19f060c183060cfab45f7d03075171e3cb83060cb83260c18306c83060d4183547bbc1835060c18341a0e8183060c5830e0c187161c583060c5830e0c187161c5a0c1a0c8060c019b0460f018300605c2e2030581caaaaaaa9a5aa060c1832e4cb972e3c79799060d696506a0d06d5070e2c5870e2c587161c587161c5a0c1b10acd82b3608c1e170b880c16072a87d546eaa8fd5555033f5554ad03aaa2fbcb8f1e5c1932e5cb93065e819f5a65a6647bbc18f5063c78341b41c3d550b17541c587160c38b161c383161c587168306c6c28221183c067c0fab02e1710182c0e03060c1d03060c1a0c7a83a060c193263c79306c8306a0c1a8341a0d0683a060c183160c383061c587161c58716830683201830064c0983c261310182c0e44c9d50f4797a0703370f89c0c1932f03270341b20d060c38b0e2e161e261320980c183a264c7a3cb830751b063c183260c1932e0e260c1a0d068341830e2c38b062c38326130184c0740c183060cd83060c783060c1d13064c78f2e0c1d03260e06c8341a0c1a8306a0d0683a061c587160c183160c383061c5871683068321183c060c019b0261310182c0e1389c3d18f463c7a8f1e5d265c997267cb93463c7972e7d3e971ea3c7a9747a5cba4cfa1c587161c38b161c38b161c587161c587168b0e8135e04d78230784c2621f0581c0740c1d503541d03463c797065cf834faaa3d4faaa0e8187161c583161c187161c5aa8321183c061f0b822a0b0380e8183060c19b0000740cd8f1e5c183065c193060c1b220d00060c01a0d0740c38b0e2c183062c187060c38b0e2d060d000000000000000060c19b1e0c1d03060c1835ecc19b360c183408bef81d132e4cb8341a00c062c3830e2c38b0046030063cd8f364c19389c4c193360004c993264c78f264c9933e9f447a004c181349a1c587161c587161c38b161c38b161c587168b0e8000000000000000f363cd9b5eae372f50002eacb9b1e3cbaf2e5cdaf2e5cfa7d11e800f1e05d3e87161c587161c5870e2c5870e2c587161c5a2c3a0023000f800007c001e8c7a33e7e3f1f3ea972e8c78f2e7cf972e7cb973e7d3ea3dde3c7a8f1e3cba7d0e2c38b0e2c38b0e1c58b0e1c58b0e2c38b458741183c3e7c0f817043e0b0380c1aaa83a063c78f1e0c18306d0355a51e3c78f55555555550740c387162c387162c38b0e2c38b0e2d54190ccd8333603c1e170b8882c0e032e5c1d03063c78f1e3c18fa2fbe8197a878f1e3d5555551eef555541ab2a0d5559aaa8352ea935541d03061c58b0e1c18b0e2c38b0e2c38b55545a1d41900dd8336603c1e170b888a080b0394aaa3c1d55551706aab4c3c78f1eaaaaaa8f55550e1c58b0e1c58baa0e2c38b0e2c38b554e6c139b0881e0f0b85c4416072aa1e3eaa87a3aaa2f5545f78f1e3c7aaaaaaa3ddeaaaacaab32ab2b2a3d4baa4d55a0e1eaa858baa0e2c38b0e2c38b55545a1d64e141103c1e170b888a0a7016072955478fa1e3c7c0e8183060c1839060c78f1e3d55555555554387162c387162c1d030e2c38b0e2c38b55264c099300640f0784c984c98882c0e2a0c7d0f060c7d0f1e0e0740c1972e9c1971e3c78f555555547aaaa83a060c38b161c383161c587161c58716aa0c806bc13af01e0f0b91c4416070183060e8183060c7831e0c1b40c183263c78f1eaaaaaaaaaa0e8183060c5830e0c187161c587161c5aa83201830064c0783c2613110581c 24 16777215 10 1023
def hc_70_9 : Nat → Nat := unpackHintV5 0xd4f594d01139c8add9c1a5c2b7c279b0a9c6a6c679a141619cf91293426e8e31448456777a5e7e7331cb6f150764ca935df9b459851d4ee2a9493d694361773d61803685b72f69c7286dbf21b1af1a15e71840751121c80ecc950775d60001dd 0x15555540d1b31e0c7b3475544cb932eaaaaaaaaaaaad507161c5870e0c5830e2c587161c5aac42b1584d58035604c26220b03955545cbb3bd555555951aa3d52eaaab541c587161c58716aaa8b43ac42b1585c5622282ac0581ca59aaa263d9a3663c9a3aaaa8997265e6499f52e5d4fa7d2e5d267daa0e1c58b0e1c58b0e2c38b0e2c38b45876209ab026ac158ac2604c10f82c0e52cd55555172f543c7d5543cb8f2e5e64f8353e0d4fa3d2e976a8387162c387162c38b0e2c38b0e2d161d88566c159b0460f0b85c43e0b038ac3eaa375548eaaaa89a3aaaa2e5cbc4eaa2f543c797de3c7972e3c78fa3f4acef3e8f4f8353e0d4ba5d83d542ea838b0e2c387162c387162c38b0e2d161d8d85044230788d18235605c2e21f0581caaa59aa1e3eaaa878f1f0f2e5c9d555330f47a7c1a8f06a5d2ed507161c5870e2c5870e2c587161c5a2c3b103c1e2b360acd8170b887c160715a1e3eaaaa87d55543eaa1f543c78f89d545ea878f2e3c78f1e3c797df47e959de3c1a8f06a3d1e974bb07aa85d5070e2c5870e2c587161c587161c5a2c3b2b0a0881eac078f01e0f0b85c43e0b038ac3eaa47555545ea8b97a3f4acef3e9f4ba7d83d542ea838b0e2c38b0e2d161d95850442b1585c5621f0581caaa87d03063c7acef5506ccb67aa4d26a8f51a3d1e9749aa1c587168b0eab158a0ab281d5bea0755503060cb83060c78f1e3d559deaaa834faa0d5555941a3d55069f5547a8d51e8f54baaaad503060c5830e0c187161c587161c5aaaa2d0eb100c18035603c1e1715888a20aac0581caa87d5232e0c1acef06aaac9b51a3d1ed76faa4d26a974ba4d26a87161c5870e8b0eab1585d5a826c81d55be81d5548c78f2e0c1832e0c18355677a0d55555069f5556536a3547a3d5069f5541a3d552eaaab55030e2c38b060c18b061c1830e2c38b55545a1d621183c060c01ab02e2b1114414d80b03940ea8183068c18f060eadf503a8b972e5d559deaaa834faa0d5555941a7d5506975551aa3d52e97549aaad503060c5830e0c187161c587161c5aaaa2d0eb0328060c01ab0562b0b85c4451055602c0e0fa467c1d523065cbaaa97a2e8f1e3c797551e3d55546aaaaaaaa1e8587161c5870e2c5870e2c587161c5aaab21183c8e6c239b02e17110581c0740cb8003c59de6d553e9b47a4d26a9b4daa5d26a87161c5a2c3a8c4605c010d83e91a307548c1972e5cbd171e3cbef1e3cb971e3c7aab3bd46aaaaaaaa9f536a3547a3d526a35551aaa97549aaa1e8587161c5870e2c5870e2c587161c5aaaa2d0eaac8460f11a304605c2e2228829b016070783aa3e0c7d0f1e3d554bd172e4d55478f47aaaaaaaaaa87a161c38b161c38b161c587161c58716aaac8766c1d9b01e0f0b85c44160701d031e01701677aa8f4fa6d36a9349aa3d1e9749aa1c587168b0eab0780f0b88021b0583c1d50f063e878f1e3cbd171e3cb8f1e3c78f1e5f7aab3bd1e9f555547aaaaa7d47aaa8f47aaa3d46a8f47aa5d2ea935550f42c387162c387162c38b0e2c38b0e2d555168755640f01e3c0783c2e1711144140581c81d6f81d5503060c1b3660c993060c18f1e3c7d03060cb93060c18f1eaaaaaaa0c587061c587161c3831586c3603ab7c0eaa8d8f1e6c183060d9b3064c983060e878f060cb97064c983555069f555418b0e0c38b0e2c387062b0d86ca07540c183063c1b56fa81a814a4c99326aaaaa0d55556a8183060c3830e2c38b0e2c38b558806030984c2613110581c1e0e87831f43c78f1e4e898f1eaaa8f1e3c7a3c793deaa8f555555543d0b0e1c5870e2c38b0e2c38b0e2d549903c1e0f0784c26220b03944cfd5172e4d1b31e4c7b3464e8b97265cb932eaaaaaaaaaaaa87a161c587161c38b161c38b161c38b0e1c5aaab2009af026bc0984c44160701d031e3c7971e3c797de3d3eaa9b0079b363c78f1e3c78f369c78f1e3cb93265d0038b0e2c38b0e2cd903c3600f07803c1e170b88882c0e27a364e8993264c9aa2aaa93060004cd931e4c793264c99350000f42c38b0e2c38b0e2d54387162c387162c02000266f0000000110005746d5d17365cbaa2aaa9b3e0006d19b1e6c79b465cba736bcb9750000f42c38b0e2c38b0e2d54387162c387162c560402f017805c05e02020202c00e15550fa060c78f55369cda70e2c38ba0756fa81d5540c1832e0c1831e3c78f555555555558a060c1a7066c1831e3c78f2e9cd9745aa060c18b061c1830e2c38b0e2c38b550e2c38baa87d51b2e0c1aaa9b366cd97361c587161c3c0eaadf40eaaa363c797060c197060c1aaaaaaaa0d3eaab146c78f360c183360cd83065cd9b2e8b541c587160c183160c383061c58716aa1c5871740ea8183066c18f060eadf503a8b972e5d55555069f555558a060c1a7066c1835e9d7a72e5cb9745aa060c18b061c1830e2c38b0e2c38b550e2c38b 24 16777215 10 1023
def hc_70_10 : Nat → Nat := unpackHintV5 0x7db725bd05759d79c24e3262a6ef0a8b5269499a83acc48e2d5df3152da555152ce98a2d9a34af99d2232d2906f2a87e29543c6ea99cd6584d91b666505e22e411093c2d788d7c2639076e1900e08b065e849b3a01de1be0bf6be83be8f411eb0200023d 0x1a3460e4703460e2e5e8197065e8b83063e8b8f07171e3cb83a060cf83419f06831e0d1832e0cb83a060c38b161c383161c587161c587161c183160c806bc25af0460f0b85c0182c0e03a060c183066c0001d03078f26000c9803a060c183060c18341830683060c183a061c587160c183160c383061c587160c183060000000000000003cd8f366d7938dc4cb97000265c997078f2e003c783f56acd8f1e6c99f369b3e4d2e4c9970e2c38b0e2c38b0e1c58b0e1c58b0e2c38b0e2c38b00118008c002e00000f463d1a3472391a32e5cb972e5cb8f1e5f78f1e5cb8f1e3d18f1e8d19f46a33e8d2e5cb970e2c38b0e2c38b0e1c58b0e1c58b0e2c38b0e2c38b0460f11a304605c2e00b0380c783021e3e060e063c1800c99389c0e260c1a0d060c183160c38b0e2c18b0e0c183c0603018005c0607063e8783063c7d031e3c7838197a2e0c78f1e3c197a2e5c1c0e81831e0c7833e0d067c1a0cb832e0e1703161c587160c38b161c383161c587161c183160c81e0f01af05e05c2e00c16070183060e8180031e00e8180032603c783c1d03060c1a0c1834183060c183060c1d03060c18b061c1830e2c38b0e2c38b060c183000000000000000266e271b5e3c78f1e3c7800132e4cb932e0003c783dfab566cf93499f368f1e3c797264cb87161c5870e2c5870e2c587161c587161c587161c58bc001e000f000b800bc05800f1e3e1f0f1e3c78f1e3c7972e5cb8f1e5c78f1e3c78f2fbc79f1e8f1e3d1e3c78f2e5cb970e2c38b0e1c58b0e1c58b0e2c38b0e2c38b0e2c38b01e03c780f0785c2e00b038b540c18306cd383264c183060c78f0750fa065c983060c78f9df340d06831e0c587061c587160c562b158ad03060c19f5506834183063eadf503060c1831e8c1831e3c183aa07540c1832e0c183060c197060c18f1e3c7b3be96a060d06a0c1833ea0c1a0d1e0d06d503060c5830e0c183060c5830e0c187161c587161c5a0c1b0328060c01ab0060c01ab01e0f0b8ac4060b038a0e066c783aa060c183669c193260c18387d503060cb93060c1a32e0c1cef9a068c1a0d060c18b0e0c38b0e2c387061b158ac2ead581d55bc183060cda3060c78f060e8183060c7aa8341a0c1833f55503060cb83060d18f1e5c183065c18306cefa5a818341a8c18341a83060cfa8341b540c183160c383061c587160c183160c383061c587168306c4030600cd8230780c18035605c562030581c568183060cbaa8341a0c1832f03aa060c1a3063c183060c1a3063c183ab7d40c183060cb97060c983075172e5cbb3be96a060d06a0c1833ea0c1a0d660d06d503060c5830e0c183060c5830e0c187161c587161c5a0c1b100c18035600c1803560ac56170b880c1607262e4c79b0740c98f263c78f1e3c793264cb83264c7931e5d9068354b930e2c38b0e2c38b26130784c264e62e3c993264c7931e3c783a064c993264cb93260c793265d9506834b930e2c38b0e2c38b26130984c264e6538396a93064c18307031e3c78fadf03a060e8197260e641a0d060c38b0e2c18b0e0cd86c07031385d3cc8f363cd83ab7a7073d5260c983060e0740c1d032e4c1cc8306a0c19f41830e2c38b062c383361b0189c2e9eaded40e01a060e8193264c9d503060c1cccc830683060c1ef41a0d0e2c38baa060c1830e2c38b41834984c88060c064c261310182c0e52d174793464c7a3a267cb93a2e5c997265cbcb4a5d93e9f4b97499f4387162c387162c3d0b0e2c38b0e2c38b458749af026bc139004cb84c43e0b0394b48d1e0cb971e3cb971f48cb8f2e5c78f2e0cbd172e3c7973f2d29764f9f47a8cba5d0e1c58b0e1c58b0f42c38b0e2c38b0e2d161d4e6c139b04e4230785c2e21f0581c547d231e3cf9b1e3cf9b460ea91833e0cf9f3e7c9a33e7d19f064cf972e5cbd172e4cb972e4cb971e3cbef1e3cb971e3c7b3be96a3e7d1ea33e0d4f8352e9743d0b0e1c58b0e1c58b0e2c38b0e1c58b0e1c58b0e2c38b458755907cd81f3608c1e234608df8170b887c160707d0f1ed528f063c78f1e3c797a2e3c78f1e5c997065c9972e3d91e8f6947ca5d2e87a161c587161c38b161c38b161c587168b0ea720783c4e6c139b02e1710f82c0e2a3c1d50f063c18f1e3cf8f1e3c78f1e0c79f1f43c78f1e3c78f1e3c78f1e5e8b97265cb97265cb8f1e5c78f1e3c78f2fbd9df4b50f1e0cfa8f068f51e3d1e8f2e9743d0b0e1c58b0e1c58b0e1c58b0e1c58b0e2c38b0e2c38b458755907cf81f01efc078f01e0f0b85c43e0b0384c18002ba364c793364c793264e8993264c993264c64009830369f49a9350f42c387162c387162c38b0e2c38b0e2d161d000000000000000400740c78f1e6c79b1e3c79b1f8c78f1e3c78f265c9971e5c78f1e5f7840f067d063d438b0e2c38b0e2cd86c000b86d40015d1b363cda3363cda35745d7972e6d7972e6cb971900a0369f4ba7d0f42c387162c387162c38b0e2c38b0e2d161d158007c00005e001f0015a3e3cfa33e3cf9fa2e7cf972e7cb972e5d9df4b51f3e9f4ba7d0f42c387162c387162c38b0e2c38b0e2d161d5641f3e07c00b821f0581caaaaaa060d556a91e3cbaa8306aaaaaaaaaab541c587160c383060c183161c58716ab108c1e033600c18170b8882c0e555555172e5ea878f2fbc78f2e5c78f1ecef55555555556536a8f549a8d5546aaa5d526aad507161c5870e2c5870e2c587161c5aaaa2d0eb108c1e234608d58170b888a09b016072aaaaa8183555aa060d55478f47b2aaaaaaaaad503060c5830e0c187161c587161c5aac4030600cd80f0785c2e220b0395555543c78faa1e3cb8f1e3c78f1e5f7b3bd5555555555947aaa8f47aaa3d51ea97549aab541c38b161c38b161c587161c58716aaa8b43ac40f5603c780f0785c2e22282ac0581c 25 33554431 10 1023
def hc_70_11 : Nat → Nat := unpackHintV5 0x902523463c75a21bc0b0925ee7d69cabb31e0dc7947edb4222674d9531a580571070aaac37050ff18a63393118166283fe033c37721c85658d094e65baf272b38a7940c640933b4a44754a1e48fc8cda9285873982076f10a3980831b8040c7b1800018f 0x1f45c78faa2e3e878f1e3cbc4e8b97268c78f2e5c9a32f48c78f477cf93499fbe972e4c9970f42c38b0e2c387162c387162c387161c38b0e2c38b564230784d78135e04cb84c0160707d04c180013360004e89931e3c993264d5d2b363c79b260c9a4c1934993264c3d0b0e2c38b0e1c58b0e1c58b0e2c38b0e2c38b0000000000000001f40f1e0014000ae8b9b1e3cbaf2e5cdaf2e5d5d2b363c79b5e7cda6cfaf4bbf2e1e8587161c5870e2c5870e2c587161c587161c58ac004600230017800bc000e0f1f543f78f1e3eaa2e8c78f2e8d1972e8cb97a463c7a3467d1a8cfa34b970f42c38b0e2c387162c387162c38b0e2c38b0e2d5908c1e234608c0b800b03940e8183060d183060c783060cb83060c7d5bea060c183063d183063c78307555bea07503060c1972e0c193060c78f1e3e07540c18341830683060d060c1a0c183060c18307540c183160c383060c183160c383061c587161c587160c183070328060c01ab0060c01ab01e0f0b85c06030581ca0703aab783060c19b460c18f1e0c1d03060c18f060c197060c18f060c197aaadf503a8b8f1e5c183060cb97060c98307540c18341830683060c183060d060c1a0c18307540c183160c383061c587160c183160c383061c587160c18307100c18033608c1e030600d58170b80c060b0380c183060c18fde0c18307440381830750f1e3c783ab783060e060c183060c183060c183060c183060c583060c38b0e2c183060c38b0e2c183060c180c1e0f0180c26130180c16070183060e89efa060c18307940c183a060c183060c18fde0c78f8783a060c183060c183060c183060e8183060c187161c587161c583060c18320180c26130783c06030581c060c183060c183068c1d03060c783063c783060c18fa27be8183a8183263c78f1e0e8183060c183060c183060d060c1a0c183060c183060e8183060c5830e0c183060c5830e0c187161c587161c583060c183201830064c01830064c0783c26130180c16070183060e8183068ef83b7efdf6f07bc183270f1e3c1d03060c183060c183060c1830740c183060c38b461d18b0e2c38b060c183064030184c26130980c060b0380cb97060e8183060c78f1e0c19b460c1d503063c78f1e0c183a2fbe8197a89931e3c997a1e3c9c5cb83a060d983660d983660c783460c1a341834683260cb83a060c38b161c383161c587161c38b462c587461c38b161c587161c183160c8066c099b0460f11a3046ec0984c66030581ca060e81831e3d1a3065cb83060c183a060c1831e3c78f060c7df1f0f1f43cbd17df40cbd43c98f1e3c783063d060c7a0e8183660d983660d9831e0c783260cb870e2c5870e2c583a060c38b161c383161c587161c587161c183163e980f1e00c806ec09b301e0f0984c66030581c060c1d100c183066f783060c1830703a81d5bc18307131e3c983060c183060c183060c183060c183060c183060c187161c587161c583060c1830180c06130784c26030182c0e03060c1d03060c19bde0c183060e89efa060c18309940c1c3c7930740c183060c183060c183060c1830740c183060c3830e2c38b0e2c38b060c18306403060326130784c26030182c0e03060c1d03060c183368c1831f7c183060c1831e0d183a27be8183a898f1e4c183260e8183060c183060c183060c183060d060c1a0c183060e8183060c5830e0c187161c583060c5830e0c187161c583060c183201830064c0983c060c0193026130180c16070183060ea264c993060c1d1083060c1d5bd060c1c0c1a0c18307bd068341a0d06834183060c38b0e2c38b0e2c183060d060d06030984c26130180c18310182c0e03060c18306aa0e8183060d983660c183060d1831e0c1d13df40c1d40c193264c99306ca0d060c19f5060c18341a0d0683a060c183160c383060c183160c383061c587161c58716830683201830064c01830064c0984c261310182c0e03060c1d03060c1836b7efa07bc183264c99326aa83555541d03060c1830e2c38b0e2c38b5506403060326130984c26220b0380c1830740c18306cc1b3060e8befa060ea265c99741aaa0d555555506a0d595069f41aa0d506acaa83a060c183160c383061c587161c58716aaa8341a8320183006cc298ec261314418a0830160701835a060c18306aa0e81831e0c183060d183060d983660c1d17df40c1838183a5a8997265c18364183060c183067d5068341a0d260c1a0e81830e0c183060c583060c5830e0c187161c587161c5a0c1a0c8074c01830060c01b30a63b0984c5980c182c0e03541d03060c1836dfbf7dbc1ef50693264c983a060c183061c587161c587160c806030984c26130581c06a83a060c18306dbf7efb783deb24c9932683506aaa4d0740c183060c38b0e2c38b0e2d541900c06130984c2628a930581c072a820c183060c18306d5bc18307544c99326aaabbd06aaaaa0c183060c183061c587161c58716aa0c06030184c2613098882c0e03541d03060c183681ac93264c9832060c060c993264c9932603a060c183061c587161c587161c587160c1830740c183066c1b3060e89efa060ea264c9935555541aaaaaa0c81830600c983064c993264c9931141d03060c18b061c1830e2c38b0e2c38b550e2c38b060c183a060c183660d9830744f7d0307513264c9aaaaaa0d555541a834fa8d51ea93550740c183062c187060c38b0e2c38b0e2d55516875064030600c98130984c2622288293016070183060ea264c99300000183060eade0003060c183060c183060c183060c183060c187161c587161c583060c183060c18000cde0000000300000183060c183000740c183066c1bb060c183068c18f060e89efa060ea060c9ab264c9930740c183060c183060c1830683060d060c183060c1830740c183062c187060c183062c187060c38b0e2c38b0e2c183060c02000062f0018000000000c1800032e4c001d03263c9a3263c993064c99b26cc193a27be819300a0a8993264c1d03060c9a0c193419306cc1b3064c1b306cc193064c1d030e1c58b0e1c58b061c58b0e1c18b0e2c38b0e2c38b0e0c18b018000c018bc000000098000c002e5c0015d1b263cda3363c9a328b8050132e4cbaba564cf9b4d9f269b66fcd97264cb87a161c38b161c38b161c587161c587161c587162b0017800005c005e00172e5e87a31e8e8befa2e5ea2e5cb97a3e9f4b972e5c3d0b0e1c58b0e1c58b0e2c38b0e2c38b0e2c38b564000170b802c0e550faa91d5517aaa2fbcb972e5e3f353545cb972f41c3d550b17541c587161c587161c587172b0a088562b0b85c562b0581c 25 33554431 10 1023
def hc_70_12 : Nat → Nat := unpackHintV5 0x1deb153445e458640a91e7b8e39011619961b942825a46031069000188 0x1347545cb8fa1e3e1e3e878f2745cb8f1e3c78f1e3c78fa9e7c9a4cfcf478f1e3cb93265c3d0b0e1c58b0e1c58b0e2c38b0e2c38b0e2c38b564135e04d780f0784c2600b0384c1800143c0078f02744c993263c78f1e3c7aba564c1934983268f1e3c793264c987a161c38b161c38b161c587161c587161c587160000000000000006d1800143c02815d175e5cb9b5e5cb8f1e3c7aba56bcf9b4d9f5e8f1e3c7977e5c3d0b0e1c58b0e1c58b0e2c38b0e2c38b0e2c38b158003c001e002f001780b001e8c7d0fdf43c7d545c78f1e5c78f1e3c78f1f43c78f479f1e8f1e3c7972e1e85870e2c5870e2c587161c587161c587161c5ab2078f01e03c1e170016072aaaaa89a31e3c78f2e5eaa89a31e3cb97aaa918f1e8d99f26933ecd2e4c997aa0e2c38b0e1c58b0e1c58b0e2c38b0e2c38b88460f09ab026ac0984c562b0581ca1fbeaaa91d548c78f2f517aaa918f1e8ea63f25cbd507161c5d50b1741c3d07161c587161c5c423079412b02e2b158ac16072aaa878f1e3c78f1e3eaaaaaa1e3c78f1e3c99f66b33e4daa1e3c78f2e4c9970e1c58b0e1c58baa0e2c38b0e2c587162c38b0e2c9ab026ac220783c2604c158ac16072a878f1e3ea8f973e5ea878f1e3c38b0e2ea838b0e2c38b0e2cf87c881e0f0b8ac16072aaa878f1e3d555556a838b0e2c38b0e2d5620783c2e2b110581caa87d550fdf5545ea878f1e3e8fcd53543c78f1e5cbc1eaa17541c587161c587161c587172b0a0881e0f0b8ac562b0581c 23 8388607 10 1023
def nh_70 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_70_12 (Nat.sub p 384)) (hc_70_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_70_10 (Nat.sub p 320)) (hc_70_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (hc_70_8 (Nat.sub p 256)) (hc_70_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_70_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_70_5 (Nat.sub p 160)) (hc_70_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_70_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_70_2 (Nat.sub p 64)) (hc_70_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_70_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_70 : Nat → Nat × Nat := unpackForestF 0xc3355c3b5dc305500c5fc234500c5bc036dc026cc026000c57be345beb4dbe04500c53b0c6fb0c63bbd7cbbb54b0c5fbad6cb0c5bb0c57b8c7cb8b44b0c53b7d7cb0a5fb6b6cb0a5bb0a57b525cb3364b327cb3a54b3024b0a53b257cb085fb0857b085500b5f00b57ae46eaec62ae04500b4fad047abd62ac56eab85d00b47aab55a246fa9b45a2463a236fa646fa6463a645fa6453a635ea2355a5464a234fa4568a2347a2b5da2b47a205500a5fa12549f45fa026c9f4579f24600a5b9c36d9dc7c9c34f9cd709c34700a579b4658c56f9a4558c5638c46f98254980558c45f96a6c9686d8c4579456f945639436e943568c24692c5792a4a8c02591b558cc5f90b458cc538cb5f8cb4f8cb478c94b8d9468c9438c93b8c02400a538b35583c6e8a46483b6f8947c83b6786d6e86d6b86d6386d6283b4583a62844628436f8434d8384500a4f82a647cc6f81a7c7cc6780b557ca6e7f46e7f4627ca467d46f7d2627d24a7c82500a4b7a3477a3457ab457a04774562795687436f785707436776c6e76c627435d74d6e74b6f74b557405d00a47732646b46f7227c6b4676b36e6fb6d6fb656fb556b26e6dc6e6dc626db666b2466bc6f6ba626ba4a6b02500a4369a646986563d6f68a5463d6b67a7c63d67662546605563d6363a6e6456f642626382500a3b62c685ad6f61c585ad6b60c705ad675f4585f3545ad635c83a5c8375c8365c8345ac625b56f5b46e5a84d00a375434f5434758b455424f5424b5735d5424755a7c55a46542435423b542370085f4736d5247c5237c4734f51570473474ec7c4eb7d4f5704eb454724f4da7c4724b4bd704bb7d4bb5d472474a27c4a26c4724348c7c48a7c4723b47c7047237008574635539c6e4546439b6f4256e42563425624225f4225339b4540464403654034539a6f3f26c3dc553da543da4639a633bd7e3ba7e3ba5439a3b3a4723a45839a370084f38347383452dd62375682db6f3546e354623536e2db5d33568333653335d2da6f3146d3126c312462da63302542f6722f26c2da3b2e4602da37008472cc681cd6f2b4582b3541cd631cc6e1cc631cc621cc5b1cc5327468273641ca6f2625c1ca632457e24458242721ca5f2325c1ca5b21e7221c601ca5720a441ed721ea7e1ea5c1ea441ca531ca4f1ca431c866008371b4651b2641156f19c5519a541156318a641146f1757e172541145f15e7215a6c11457143551434f1126e11d6f11d6311c6e11c62112460082f0fc650fb680156f0e4550e358015630d3680146f0c3580145f0b360014570845f082470824608946080260136203d6f06a5403d6303c6e03a6e03a6203a5f03a570134a02d7001b4701a3a01066008270003f 9 11
def ch_70 : Nat → Bool := dagCheckNodeV5 fullMask g_70 ep_70 5 31 bds_70 393 (dagTraceF fullMask rootStock 11 f_70) cur_70 nh_70
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV5 fullMask g_70 ep_70 5 31 393 bds_70 (dagTraceF fullMask rootStock 11 f_70) (cur_70 0) (nh_70 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_0 : treeBlockF 0 32 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_1 : treeBlockF 32 64 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_2 : treeBlockF 64 96 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_3 : treeBlockF 96 128 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_4 : treeBlockF 128 160 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_5 : treeBlockF 160 192 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_6 : treeBlockF 192 224 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_7 : treeBlockF 224 256 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_8 : treeBlockF 256 288 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_9 : treeBlockF 288 320 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_10 : treeBlockF 320 352 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_11 : treeBlockF 352 384 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_12 : treeBlockF 384 393 ch_70 = true := by decide +kernel
theorem nj_70_1 : ∀ i, 0 ≤ i → i < 64 → ch_70 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_70_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_70_1 h1 h2)
theorem nj_70_2 : ∀ i, 0 ≤ i → i < 96 → ch_70 i = true := block_join nj_70_1 (fun _ h1 h2 => treeBlockF_at nb_70_2 h1 h2)
theorem nj_70_3 : ∀ i, 0 ≤ i → i < 128 → ch_70 i = true := block_join nj_70_2 (fun _ h1 h2 => treeBlockF_at nb_70_3 h1 h2)
theorem nj_70_4 : ∀ i, 0 ≤ i → i < 160 → ch_70 i = true := block_join nj_70_3 (fun _ h1 h2 => treeBlockF_at nb_70_4 h1 h2)
theorem nj_70_5 : ∀ i, 0 ≤ i → i < 192 → ch_70 i = true := block_join nj_70_4 (fun _ h1 h2 => treeBlockF_at nb_70_5 h1 h2)
theorem nj_70_6 : ∀ i, 0 ≤ i → i < 224 → ch_70 i = true := block_join nj_70_5 (fun _ h1 h2 => treeBlockF_at nb_70_6 h1 h2)
theorem nj_70_7 : ∀ i, 0 ≤ i → i < 256 → ch_70 i = true := block_join nj_70_6 (fun _ h1 h2 => treeBlockF_at nb_70_7 h1 h2)
theorem nj_70_8 : ∀ i, 0 ≤ i → i < 288 → ch_70 i = true := block_join nj_70_7 (fun _ h1 h2 => treeBlockF_at nb_70_8 h1 h2)
theorem nj_70_9 : ∀ i, 0 ≤ i → i < 320 → ch_70 i = true := block_join nj_70_8 (fun _ h1 h2 => treeBlockF_at nb_70_9 h1 h2)
theorem nj_70_10 : ∀ i, 0 ≤ i → i < 352 → ch_70 i = true := block_join nj_70_9 (fun _ h1 h2 => treeBlockF_at nb_70_10 h1 h2)
theorem nj_70_11 : ∀ i, 0 ≤ i → i < 384 → ch_70 i = true := block_join nj_70_10 (fun _ h1 h2 => treeBlockF_at nb_70_11 h1 h2)
theorem nj_70_12 : ∀ i, 0 ≤ i → i < 393 → ch_70 i = true := block_join nj_70_11 (fun _ h1 h2 => treeBlockF_at nb_70_12 h1 h2)
theorem nc_70 : ∀ i, 0 ≤ i → i < 393 → ch_70 i = true := nj_70_12
theorem lb_70 : LowerBin fullMask rootStock g_70 12 :=
  lowerDagV5 (kn_cons lb_66 (kn_cons lb_61 (kn_cons lb_60 (kn_cons lb_27 (kn_cons lb_69 (kn_cons lb_68 (kn_cons lb_63 (kn_cons lb_24 (kn_cons lb_62 (kn_cons lb_48 (kn_cons lb_65 (kn_cons lb_64 (kn_cons lb_1 (kn_cons lb_29 (kn_cons lb_67 (kn_cons lb_3 (kn_cons lb_28 (kn_cons lb_6 (kn_cons lb_46 (kn_cons lb_23 (kn_cons lb_11 (kn_cons lb_54 (kn_cons lb_31 (kn_cons lb_2 (kn_cons lb_56 (kn_cons lb_26 (kn_cons lb_19 (kn_cons lb_22 (kn_cons lb_25 (kn_cons lb_47 (kn_nil))))))))))))))))))))))))))))))) rc_70 nc_70 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.and, [5, 9]⟩, ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [11, 14]⟩, ⟨GateOp.and, [12, 15]⟩, ⟨GateOp.or, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3972571264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677288 * 2 ^ 32 + 3972571264)) (13 - 1) := by
  rw [show canon fullMask (4276677288 * 2 ^ 32 + 3972571264) = g_70 by decide]
  exact lb_70

end PEqualNP.Outside.L_meta_47997

theorem PEqualNP.Outside.L_meta_47997 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 3972571264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3972571264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47997.table2_from_lowerBin (4276677288 * 2 ^ 32 + 3972571264) 13 PEqualNP.Outside.L_meta_47997.root_lb PEqualNP.Outside.L_meta_47997.wg 18 rfl PEqualNP.Outside.L_meta_47997.wfits PEqualNP.Outside.L_meta_47997.weval
