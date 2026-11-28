import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48581

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

def m_0 : Nat := 0xf000f000000000
def s_0 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_0 : Nat := 0x10007000000000
def ep_0 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
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

def m_1 : Nat := 0xf000f0000000000
def s_1 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_1 : Nat := 0x100070000000000
def ep_1 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_2 : Nat := 0x5500550000000000
def s_2 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_2 : Nat := 0x100150000000000
def ep_2 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_3 : Nat := 0x3300330000000000
def s_3 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_3 : Nat := 0x100130000000000
def ep_3 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_4 : Nat := 0x5050505000000000
def s_4 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_4 : Nat := 0x10105000000000
def ep_4 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_5 : Nat := 0x3030303000000000
def s_5 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_5 : Nat := 0x10103000000000
def ep_5 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
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

def m_6 : Nat := 0x4444444400000000
def s_6 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_6 : Nat := 0x4044400000000
def ep_6 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_7 : Nat := 0x2222222200000000
def s_7 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_7 : Nat := 0x2022200000000
def ep_7 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_8 : Nat := 0xc000c000c000c00
def s_8 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_8 : Nat := 0x40004000c00
def ep_8 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
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

def m_9 : Nat := 0x3333000000000000
def s_9 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_9 : Nat := 0x113000000000000
def ep_9 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_10 : Nat := 0x5555000000000000
def s_10 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_10 : Nat := 0x115000000000000
def ep_10 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_11 : Nat := 0xff000000000000
def s_11 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_11 : Nat := 0x17000000000000
def ep_11 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_12 : Nat := 0xc000c000c000c0
def s_12 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_12 : Nat := 0x40004000c0
def ep_12 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_13 : Nat := 0xf0f000000000000
def s_13 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_13 : Nat := 0x107000000000000
def ep_13 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_14 : Nat := 0x5500000055000000
def s_14 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_14 : Nat := 0x100000015000000
def ep_14 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_15 : Nat := 0xf0f000000000
def s_15 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_15 : Nat := 0x107000000000
def ep_15 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_15 : Nat → Nat := fun _ => 0
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 1 bds_15 (dagTraceF m_15 s_15 3 f_15) (cur_15 0) (nh_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 1 ch_15 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → ch_15 i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0x22222222
def s_16 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_16 : Nat := 0x20222
def ep_16 : Nat := 0x2200000000000020020000000000002020000000000000000000000000000000000
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_16 : Nat → Nat := fun _ => 0
def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 1 bds_16 (dagTraceF m_16 s_16 3 f_16) (cur_16 0) (nh_16 0) s_16 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 1 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 1 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xff0000000000
def s_17 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_17 : Nat := 0x170000000000
def ep_17 : Nat := 0x6000000000000001200000000000000140000000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_17 : Nat → Nat := fun _ => 0
def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 1 bds_17 (dagTraceF m_17 s_17 3 f_17) (cur_17 0) (nh_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 1 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0x4444000044440000
def s_18 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_18 : Nat := 0x4000004440000
def ep_18 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_18 : Nat → Nat := fun _ => 0
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 1 bds_18 (dagTraceF m_18 s_18 3 f_18) (cur_18 0) (nh_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 1 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0x5050000050500000
def s_19 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_19 : Nat := 0x10000010500000
def ep_19 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_19 : Nat → Nat := fun _ => 0
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 1 bds_19 (dagTraceF m_19 s_19 3 f_19) (cur_19 0) (nh_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 1 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xcccc00003333
def s_20 : List Nat := [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033]
def g_20 : Nat := 0x44400001333
def ep_20 : Nat := 0x4000000020000004000000020000000000000000000000044400001000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def nh_20 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_20 : Nat → Nat × Nat := unpackForestF 0x32db2432a32632532400f 3 9
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 7 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 7 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 7 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 7 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xff00ff0000000000
def s_21 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_21 : Nat := 0x100170000000000
def ep_21 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_17, s_17, 4, g_17), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3)]
def cc_21_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_21_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_21 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_21_1 (Nat.sub p 32)) (cc_21_0 p) (Nat.blt p 32)
def hc_21_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_21_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_21 : Nat → Nat := fun p => Bool.rec (hc_21_1 (Nat.sub p 32)) (hc_21_0 p) (Nat.blt p 32)
def f_21 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 43 bds_21 (dagTraceF m_21 s_21 6 f_21) (cur_21 0) (nh_21 0) s_21 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 43 ch_21 = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 43 → ch_21 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 43 → ch_21 i = true := nj_21_1
theorem lb_21 : LowerBin m_21 s_21 g_21 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_17 (kn_cons lb_2 (kn_cons lb_3 (kn_nil))))) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xffff000000000000
def s_22 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_22 : Nat := 0x117000000000000
def ep_22 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_11, s_11, 4, g_11), (m_10, s_10, 4, g_10), (m_9, s_9, 4, g_9)]
def cc_22_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_22_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_22 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_22_1 (Nat.sub p 32)) (cc_22_0 p) (Nat.blt p 32)
def hc_22_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_22_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_22 : Nat → Nat := fun p => Bool.rec (hc_22_1 (Nat.sub p 32)) (hc_22_0 p) (Nat.blt p 32)
def f_22 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 43 bds_22 (dagTraceF m_22 s_22 6 f_22) (cur_22 0) (nh_22 0) s_22 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 32 ch_22 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_1 : treeBlockF 32 43 ch_22 = true := by decide +kernel
theorem nj_22_1 : ∀ i, 0 ≤ i → i < 43 → ch_22 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_22_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_22_1 h1 h2)
theorem nc_22 : ∀ i, 0 ≤ i → i < 43 → ch_22 i = true := nj_22_1
theorem lb_22 : LowerBin m_22 s_22 g_22 7 :=
  lowerDagV5 (kn_cons lb_13 (kn_cons lb_11 (kn_cons lb_10 (kn_cons lb_9 (kn_nil))))) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xffff00000000
def s_23 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_23 : Nat := 0x177700000000
def ep_23 : Nat := 0x6000000000000006000000000000001222000000000000144400000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xff00ff00000000
def s_24 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_24 : Nat := 0x17007700000000
def ep_24 : Nat := 0x60000000000000000000000000000600000000000000120022000000000014004400000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xf0f0f0f000000000
def s_25 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_25 : Nat := 0x10107000000000
def ep_25 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_15, s_15, 4, g_15), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def hc_25_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_25_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_25 : Nat → Nat := fun p => Bool.rec (hc_25_1 (Nat.sub p 32)) (hc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_25 : Nat → Bool := dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25 nh_25
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 43 bds_25 (dagTraceF m_25 s_25 6 f_25) (cur_25 0) (nh_25 0) s_25 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 43 ch_25 = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 43 → ch_25 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 43 → ch_25 i = true := nj_25_1
theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_15 (kn_cons lb_4 (kn_cons lb_5 (kn_nil))))) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xf0f0f0f00000000
def s_26 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_26 : Nat := 0x107070700000000
def ep_26 : Nat := 0x600000000000006000000000000000000000000000001020202000000000104040400000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xcccccccc00000000
def s_27 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_27 : Nat := 0x4044400000000
def ep_27 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x3333333300000000
def s_28 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_28 : Nat := 0x113133300000000
def ep_28 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_9, s_9, 4, g_9), (m_5, s_5, 4, g_5), (m_7, s_7, 4, g_7)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_28 : Nat → Nat := fun p => Bool.rec (hc_28_1 (Nat.sub p 32)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 43 bds_28 (dagTraceF m_28 s_28 6 f_28) (cur_28 0) (nh_28 0) s_28 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 43 ch_28 = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_9 (kn_cons lb_5 (kn_cons lb_7 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xaa00aa00aa00aa
def s_29 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_29 : Nat := 0x20022000200aa
def ep_29 : Nat := 0x8800000020000000a80000000000000000000200000002000000020022000200000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_29 : Nat → Nat := fun _ => 0
def f_29 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 1 (dagTraceF m_29 s_29 3 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 1 bds_29 (dagTraceF m_29 s_29 3 f_29) (cur_29 0) (nh_29 0) s_29 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 1 ch_29 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 1 → ch_29 i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 4 :=
  lowerDagV5 (kn_nil) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xaaaaaaaa00000000
def s_30 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_30 : Nat := 0x2022200000000
def ep_30 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0x5050505050505050
def s_31 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_31 : Nat := 0x10105010501050
def ep_31 : Nat := 0x1040000000001040000000000010004000400040000000000000000000101000100010000000000000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x5555555500000000
def s_32 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_32 : Nat := 0x115155500000000
def ep_32 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_10, s_10, 4, g_10), (m_4, s_4, 4, g_4), (m_6, s_6, 4, g_6)]
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def hc_32_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_32_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_32 : Nat → Nat := fun p => Bool.rec (hc_32_1 (Nat.sub p 32)) (hc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 43 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) (nh_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 ch_32 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 43 ch_32 = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_10 (kn_cons lb_4 (kn_cons lb_6 (kn_nil))))) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x3030303030303030
def s_33 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_33 : Nat := 0x10103010101030
def ep_33 : Nat := 0x1000000000001020000000200010002000000020000000000000000000000000000000000010100010101000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xc0c0c0c0c0c0c0c0
def s_34 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_34 : Nat := 0x40004000c0
def ep_34 : Nat := 0x400080000000400000008000000040004000c0000000000000000000000000000000000000004000400000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x3333000033330000
def s_35 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_35 : Nat := 0x113000011130000
def ep_35 : Nat := 0x1000000000000000000000000012000000020000010200000002000000000000000000000110000011100000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0x5555000055550000
def s_36 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_36 : Nat := 0x115000015550000
def ep_36 : Nat := 0x1440000000000000000000000014000000400000010400000400000001100000100000000000000000000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10), (m_14, s_14, 4, g_14), (m_19, s_19, 4, g_19), (m_18, s_18, 4, g_18)]
def cc_36_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_36_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_36 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_36_1 (Nat.sub p 32)) (cc_36_0 p) (Nat.blt p 32)
def hc_36_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_36_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_36 : Nat → Nat := fun p => Bool.rec (hc_36_1 (Nat.sub p 32)) (hc_36_0 p) (Nat.blt p 32)
def f_36 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_36 : Nat → Bool := dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36 nh_36
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 43 bds_36 (dagTraceF m_36 s_36 6 f_36) (cur_36 0) (nh_36 0) s_36 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 ch_36 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 43 ch_36 = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 43 → ch_36 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 43 → ch_36 i = true := nj_36_1
theorem lb_36 : LowerBin m_36 s_36 g_36 7 :=
  lowerDagV5 (kn_cons lb_10 (kn_cons lb_14 (kn_cons lb_19 (kn_cons lb_18 (kn_nil))))) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0x5500550055005500
def s_37 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_37 : Nat := 0x100150015001500
def ep_37 : Nat := 0x1400000000001400000000000000000000000000010004000400040001001000100010000000000000000000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xff000000ff00
def s_38 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_38 : Nat := 0x170000001f00
def ep_38 : Nat := 0x800000000000000000000000000000000000000060000000e0000001200000010000000140000001000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xf0f00000f0f0
def s_39 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_39 : Nat := 0x1070000010f0
def ep_39 : Nat := 0x80000000000000000000000060000000e0000000000000000000001020000010000000104000001000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xcccc0000cccc0000
def s_40 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_40 : Nat := 0x4000004440000
def ep_40 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000004000004440000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_18 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0x3300330033003300
def s_41 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_41 : Nat := 0x100130011001300
def ep_41 : Nat := 0x1000000000001200000002000000000000000000010002000000020000000000000000000100100011001000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xcc00cc00cc00cc00
def s_42 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_42 : Nat := 0x40004000c00
def ep_42 : Nat := 0x4000800000004000000080000000000000000000000040004000c0000000000000000000000040004000000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xf000f000f000f00
def s_43 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_43 : Nat := 0x100070005000f00
def ep_43 : Nat := 0x40008000000060000000a000000000000000000000000000000000001000200000000000100040005000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0x33333333
def s_44 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_44 : Nat := 0x11131333
def ep_44 : Nat := 0x2200000000000020020000000000002020000000000000000000000000011101000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xcc00cc00cc00cc
def s_45 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_45 : Nat := 0x40044004400cc
def ep_45 : Nat := 0x40008800000040000000880000000000000000000400000000000000000000000000000004004400440000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xffff0000
def s_46 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_46 : Nat := 0x15570000
def ep_46 : Nat := 0x420000000000000402000000000000100200000000000015540000
def bds_46 : List (Nat × List Nat × Nat × Nat) := []
def cc_46_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_46_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_46 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_46_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_46_0 p) (Nat.blt p 32)
def hc_46_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_46_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_46_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_46 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_46_2 (Nat.sub p 64)) (hc_46_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_46_0 p) (Nat.blt p 32)
def f_46 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_46 : Nat → Bool := dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 64 (dagTraceF m_46 s_46 5 f_46) cur_46 nh_46
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 64 bds_46 (dagTraceF m_46 s_46 5 f_46) (cur_46 0) (nh_46 0) s_46 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 32 ch_46 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_1 : treeBlockF 32 64 ch_46 = true := by decide +kernel
theorem nj_46_1 : ∀ i, 0 ≤ i → i < 64 → ch_46 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_46_1 h1 h2)
theorem nc_46 : ∀ i, 0 ≤ i → i < 64 → ch_46 i = true := nj_46_1
theorem lb_46 : LowerBin m_46 s_46 g_46 6 :=
  lowerDagV5 (kn_nil) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xff00ff00
def s_47 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_47 : Nat := 0x15001f00
def ep_47 : Nat := 0xa0000000000000000000000000004000e0000000000100010000000000015001000
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

def m_48 : Nat := 0xf0f0f0f0
def s_48 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_48 : Nat := 0x105010f0
def ep_48 : Nat := 0xa000000000004000e0000000000000000000000000100010000000000010501000
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
def cur_48 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_48 : Nat → Nat := fun _ => 0
def f_48 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_48 : Nat → Bool := dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 1 (dagTraceF m_48 s_48 3 f_48) cur_48 nh_48
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 1 bds_48 (dagTraceF m_48 s_48 3 f_48) (cur_48 0) (nh_48 0) s_48 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48 : treeBlockF 0 1 ch_48 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 1 → ch_48 i = true := fun _ h1 h2 => treeBlockF_at nb_48 h1 h2
theorem lb_48 : LowerBin m_48 s_48 g_48 4 :=
  lowerDagV5 (kn_nil) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xaaaaaaaa
def s_49 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_49 : Nat := 0x20aaa
def ep_49 : Nat := 0xaa800000000000200a00000000000020a0000000000000200000000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xff000000ff000000
def s_50 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_50 : Nat := 0x100000015000000
def ep_50 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000100000015000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xff000000ff0000
def s_51 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_51 : Nat := 0x17000000570000
def ep_51 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xf000f000f000f0
def s_52 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_52 : Nat := 0x100070005000f0
def ep_52 : Nat := 0x40008000000060000000a00000000000000000000000000000000000100020000000000010004000500000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xf0f00000f0f00000
def s_53 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_53 : Nat := 0x10000010500000
def ep_53 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000010000010500000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_19 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xf0f00000f0f0000
def s_54 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_54 : Nat := 0x107000005070000
def ep_54 : Nat := 0x400000000000000000000000006000000020000000000000000000001020000000200000104000005040000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x4444444444444444
def s_55 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_55 : Nat := 0x4044404440444
def ep_55 : Nat := 0x440000000000440000000000004004000400040000404000400040000000000000000000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xa0a0a0a0a0a0a0a
def s_56 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_56 : Nat := 0x2020200020a0a
def ep_56 : Nat := 0x8080000020000000a080002000000020000000000000000000000020202000200000000000000000000
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

def m_57 : Nat := 0x5a005a005a005a00
def s_57 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]
def g_57 : Nat := 0x120010001a00
def ep_57 : Nat := 0x100008000000120000000a000000000000000000000000000000000000001200100010000000000000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := []
def cur_57 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_57 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_57 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_57 : Nat → Bool := dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 3 (dagTraceF m_57 s_57 4 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 3 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) (nh_57 0) s_57 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57 : treeBlockF 0 3 ch_57 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 3 → ch_57 i = true := fun _ h1 h2 => treeBlockF_at nb_57 h1 h2
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV5 (kn_nil) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xc0c0c0c0c0c0c0c
def s_58 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_58 : Nat := 0x4040404040c0c
def ep_58 : Nat := 0x400080800000400000008080004000000000000000000000000000000000000000000000004040404040000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def nh_58 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 0 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) (nh_58 0) s_58 4 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 0 (dagTraceF m_58 s_58 4 f_58) cur_58 nh_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x50a050a050a050a0
def s_59 : List Nat := [0xa000a000a000a0, 0x1020102010201020, 0x50a0000050a0, 0x50a050a0]
def g_59 : Nat := 0x1020100010a0
def ep_59 : Nat := 0x1000008000001020000000a00000000000000000000000000000000000001020100010000000000000000000
def bds_59 : List (Nat × List Nat × Nat × Nat) := []
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_59 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_59 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 3 (dagTraceF m_59 s_59 4 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 3 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) (nh_59 0) s_59 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 3 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 3 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV5 (kn_nil) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xaaaaaaaaaaaaaaaa
def s_60 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_60 : Nat := 0x2022200020aaa
def ep_60 : Nat := 0x8880000022000000aa800020020000200a00002020000020a0000020222000200000000000000000000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 5, g_30), (m_16, s_16, 4, g_16), (m_56, s_56, 4, g_56), (m_29, s_29, 4, g_29)]
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV5 0x408101cb870c4681 0xa9e2533c6793f899b4bca4601f 7 127 3 7 10 1023 13 8191
def nh_60 : Nat → Nat := unpackHintV5 0x3502c61f180ba1ab07ac028850144000 0xb8f7c7caaaae9569b0040000100 14 16383 7 127
def f_60 : Nat → Nat × Nat := unpackForestF 0x31994fea78533297a530a4601f 3 10
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 8 (dagTraceF m_60 s_60 6 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 8 bds_60 (dagTraceF m_60 s_60 6 f_60) (cur_60 0) (nh_60 0) s_60 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 8 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 8 → ch_60 i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 7 :=
  lowerDagV5 (kn_cons lb_30 (kn_cons lb_16 (kn_cons lb_56 (kn_cons lb_29 (kn_nil))))) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xff00ff00ff00ff00
def s_61 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_61 : Nat := 0x100170015001f00
def ep_61 : Nat := 0x140008000000160000000a0000000000000000000100060004000e0001001200100010000100140015001000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 7, g_21), (m_43, s_43, 5, g_43), (m_38, s_38, 5, g_38), (m_42, s_42, 5, g_42), (m_37, s_37, 5, g_37), (m_50, s_50, 5, g_50), (m_41, s_41, 5, g_41), (m_14, s_14, 4, g_14), (m_8, s_8, 4, g_8), (m_47, s_47, 4, g_47), (m_57, s_57, 5, g_57), (m_1, s_1, 4, g_1), (m_17, s_17, 4, g_17)]
def cc_61_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x7c26a95c75c05a15a05815805425405404e34e04e04a24434404214204014004004003e1364360341340321320038001 0x200983e110a91f94a3b2646e488cc20971183b22066420ac78119c34f3769666d1cbda183a3e2b27c3a0506daf0c93e154a22e8e456b009350144b824d48452f0b452134a620904380a06254080281717c29a984a5e072a40a0500da95134fa06973cd1e75a1ce24f9a4972891e4121c723f8d477008ddd519b614f602967451c70a18d13f182761e4dc34998312f042560449c04918001f 12 4095 5 31 11 2047 19 524287
def cc_61_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x902318c1f4569504c9123c8f03c0a5280a02446318060144320c0300c03004810004000000000000 0x7cd02012f7e4ade9277848efb5cbcd42ea5cb8946aa50a48fe823b928de0a3376171c94454051714c52051693c50051b5606a571613c681713014620b19134600d120145b141734a58d1944504e1012828 10 1023 4 15 11 2047 18 262143
def cc_61_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x944a2190884421f4f87533190c859ac144a04924104803c9548440200e47038150140000 0x29b4ea2d2a634690d0a6c50b2132325cae092da3fb48eec237ac8cea36ca6982006ca2d81f86c9a941f05c9b142584c965427c609d14262607a1b2504c8c97220248c94222508654243608e9b22a5c781b21024 9 511 3 7 11 2047 18 262143
def cc_61_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a5094250942328c2306a5374c1304c13044910440f22d0b0284a0280a0280731c0701485001400 0x3795d8a557d818f4053eb4ef852fc943dc13f184b8411d8043f007fb813ff17bf25eda57f115b8255d7953ec0939460e21337a6cdc093a23fe68ef8237da8cf5944d1583395ccc1732134c60d3534fd2d2f2b47c4d0f093e 10 1023 4 15 11 2047 18 262143
def cc_61_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0700bc6f0b86e0b82e0b82e0a5690a4290916407d5b46c1745c1705c152541323d0f03c0b406801 0x4fa519b8bd368fa65ae4c350972b92c542542e49c5f9248e2651c289fc89278f6bce857da8ada9157382a6e657da4ada8157372a6e4575a0aca7155362a29a90220261693c86029144fe249dc393785266e213d9825a504734087191622e2942450702beca56d24ab99953832990450204263e824 10 1023 4 15 11 2047 19 524287
def cc_61_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x28308040 0x24e53a3925fe310b4be8434 6 63 3 7 10 1023 18 262143
def cur_61 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_61_5 (Nat.sub p 160)) (cc_61_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_61_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_61_2 (Nat.sub p 64)) (cc_61_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_61_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_61_0 : Nat → Nat := unpackHintV5 0xe06036b626b14a357f458b1c6f5541d25ea5d2f4009262a48b042458011c8328d00a4680021e0b0f5cca6de682ca52965000ac83052e1b26f1413382092c383ce6419b260971b44045a150590104c00004000000 0xad31c74d31c74e1c78722e2e2e2cb806db6db1c04c71d34c71d3a1c787ab8b8b8b8b2ea2c32cb2cf2c32cb4b4b2c71c7000000000000b02830c30c30d5d5eaaaa4c0030c30ea87a83974d35c30c30e65e6aaa0eaeaaaaa970000000000003d33cf4c71d3692cb0c32cb4343003cf0cf0d34d34d30cf3c38b8b83aba0c38b8b2d32c72c72cba8b2d2d2cb0c30c000000000000f3e832cb0d357eaaa8002bad87ada7c33eb2e3ebab5cf3c71df4b2da83a99000a87a8f0cf0e8b5d34e6a60cf3c3aaaaaa0eaea800000000000034c30c30d34d34c30c30e2e2e0e25cb8b2d34d34e0175d75cb0034c30c30d34d34c30c30e2e2e830e0eae5cb8b2c34c30c31c30ea0d70d0d0c30cb0c000000000000c0acfa0cf2e4ebadf1cb8b1eacba8f0cf0d37d2d2e99a8021cba1cba830d62c0b134d75355d5ea87a83a8fa8baaaaa975ab5a54000000000000134d34d55562e2e2e2d45534d34d75d75c10b0134d34d554d562e2e2e2d6ad554d51d50d53d554b400000000000404d7550cf3c355a56aea800174d35d51d554f543555556aaa96555ab0000000000004d34d3534d4d35757932e2cb972e2cba55ab2d32c72c72cb2c32cb2cf2c3a95000000000000000000000 21 2097151 9 511
def hc_61_1 : Nat → Nat := unpackHintV5 0xda0034820cd84aaa8c76b41da006b8b186285a87158125184910363f050fc003c030ce2230830c2002d8305a5c13038460611800400609868260006830140603818000e000000000 0x9db1eb8badb9c701b9e76c71c71db9e76c71c71e028aaaaa87a3eaa831c71c7a6a6871c71eaaa87abaaaa200000000000002bacb833d2d2bad3cb5cb2b0cf6b1ad6cadb8c7aeb8b52c33d0aeb1badbaeb0cb0c2b0eb2d34e5833cf0cb2cb2d1d1c02b2eaeb1eb8b6eb6eb6eb2c 18 262143 8 255
def hc_61_2 : Nat → Nat := unpackHintV5 0xc5202b460911c23e068e01a38008885a2200830599874638298806598895e084c8b1161c4005900003a858ea00328809832200606e121b800620c188005c06108680c36018180006 0xc30c31c71c70c30c3a2aaaa00000000551c71c755a255aa000000001c71c7471d0cf3c3a87aa9900000aeb1eb8b2b1cb81c71c71c71c7a887aaaa000000000aaeb3c365aeb2b8f0dad7a3eb1abab5b0f0dac1eb8b236cf0dad91cf0daeb8b0aeb8b89adb03aeb3c35bacf0dae831eb2e0aeb 18 262143 8 255
def hc_61_3 : Nat → Nat := unpackHintV5 0xc245cc0410be80ebe800be800bdc06bd006bc406aa09286d1a82c207f41c7e4087d806788287700c7640671c24584cc58400558164f8304ec064d80a4cc06480264800045c123f43431c6c1010e00080 0x30c30c343575d3d3e2e2c0030d6b0caeb6c30c30c3575750d46db403c00c30c35d576db0c30c30d5d5d430d0dac30c30c70c35433c30c30c35d570e0cb0e0c3000000000030002536bacbab8f4eadaeb1d4dabae2c0ebaeb1e0d3ab22e4c71d3a838fa4c71d39939a87abaaaaaaaa4c000000000002bad1daeb0cf3c75c7adadac7aeb8b51cac33ebacb833c31c3071da433cf0c71c71cb2d2d2c00071c71c71c71e1eae871e2e2e2e2ea1c31c71cf1c31c747471c72c700000000000001c71c71c71c73cf3cfa2aaaa00000000 20 1048575 9 511
def hc_61_4 : Nat → Nat := unpackHintV5 0x7a1519b9d7467837992c5a5b44b95d080532211408604be2211b0a43f73a8f70363c9098ee022327488bf45429c3088391c1ce2006606c1950186480619200061c161870005f0161441c0450600d42002388c0263400004c 0xc30c71cf1c70c30c70eb1d1c71d1c71c71c33cf0c7871c7872c71c71c33cf0d34d34c00000000000030c30c31c3ac33c30c30d71d71d75c30d70c30c3435c3430d31c74c30d30c30c3832c3830d74d74c0000000000001571c75d50d3d51dad555554c71d354b655d35d355530000000000001d745ad433cf0c14e2e2c0071c71c75d1dad471d5d5d51c31c71cf1c31c71c71c74d34d34d531e1cb1e1c70000000000001c71c751551c71c73cf3cf55000000000c30c3545551c71c70c30c35500000000aaaa1c71c7555155000000001c71c75447551c71c72cb2cb55000000001c05d75d71c71c74051554d34d31c71c74d34d35551d4f5550c71c71d555476b5559554b1c71c74d34d355100000000000003aeb7d434f0cf0d5eb0cf5eb472d3931d71d75d471d1dad5d5d55c37cf3d70c71c74c71d35d34d4d4d37e4cb932c000000000001430c30c30d55562e2c00030c30d5475435550dad5550c30c354b655500000000000003cf0cf0d75757436b50c33d73c73c73cf5430c30cf3c35d573e3cb3e3cb0000000000000c71c351550cf3c31c71c755000000003c33c350cf3c3555558b8b00000aeb3c36b2b0cf40cf3c3545550cf3c355000000000aa3c33c3aa555551000000003c33c355512cb2cb0cb2c355000000008db8db3c33c33c05540516e38db0cf3c355547554f0cf0d4f5555550dad65552c33cf0d54004000000000000c350c73c33c32c300c 22 4194303 9 511
def hc_61_5 : Nat → Nat := unpackHintV5 0x83868599503d8e0115620008a 0xc35df3cf0d43471d3cf8b8b000c30c31c3ac71c30c71c75c71cf4f3d3cf0cf3cf0d31c74cf8f2cf8f2c33cf3c34d35d300000000000000c7030c301c0c01c71c70c30c35d75d71c71c70c30c34d34d34d34d30c70eb0c30c30c70c30c31c71c71d70c30c30d0d70d0c31c71c70c30c30e0cb0e0c34d34d300000000300000070c70eb1c73cf430d4f3d1c74d38b8b000 20 1048575 9 511
def nh_61 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_61_5 (Nat.sub p 160)) (hc_61_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_61_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_61_2 (Nat.sub p 64)) (hc_61_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_61_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_61 : Nat → Nat × Nat := unpackForestF 0xa349202d3e841a00b4b9f4a202d1c05a180a4f9b47c0292e55ae4ab50952b92a542542e00a47918bf2291e449380a438f6bc028fc051dc0c58818a50a4fe149dc404c8526f0c0521499c0c508129902502042600a37768bcec979dda73b94b7a030f4051dca1bb81f77026ec0900519b6a3f6d476e3181c42636a376e4d8dc091b5198094f6b288c2d3d85a5b3560662b8cc17185a3b193463068c2d0d849f0094b3b6b876d40ed2e1da515647eac8ed64262b23757048ac8cced2829b6c534c0768fd45b01da3b4a8c0951413628252604b2a094130ed1ba1360424d88c941092e21a50432a084090ed199e12f3c2567cd00f0939e1233b0b80251ce4a20eb4f1d69669580d0ae1a05c1d68e604d0c416180341d68658d28b628163461d27c3c8fc791d93c50270803c8dc94140f2331e0763c0cc78158f84c1f0883c08c740a009431b6bc024fc649f0093b174722114852b00a25c104a622d48452f082410126e1c050049986254078be0ed4c1d2f04014072a4024bc140a0092b036a40249c04918001f 8 11
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 4 15 bds_61 164 (dagTraceF m_61 s_61 8 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 4 15 164 bds_61 (dagTraceF m_61 s_61 8 f_61) (cur_61 0) (nh_61 0) s_61 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_0 : treeBlockF 0 32 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_1 : treeBlockF 32 64 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_2 : treeBlockF 64 96 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_3 : treeBlockF 96 128 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_4 : treeBlockF 128 160 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_5 : treeBlockF 160 164 ch_61 = true := by decide +kernel
theorem nj_61_1 : ∀ i, 0 ≤ i → i < 64 → ch_61 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_61_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_61_1 h1 h2)
theorem nj_61_2 : ∀ i, 0 ≤ i → i < 96 → ch_61 i = true := block_join nj_61_1 (fun _ h1 h2 => treeBlockF_at nb_61_2 h1 h2)
theorem nj_61_3 : ∀ i, 0 ≤ i → i < 128 → ch_61 i = true := block_join nj_61_2 (fun _ h1 h2 => treeBlockF_at nb_61_3 h1 h2)
theorem nj_61_4 : ∀ i, 0 ≤ i → i < 160 → ch_61 i = true := block_join nj_61_3 (fun _ h1 h2 => treeBlockF_at nb_61_4 h1 h2)
theorem nj_61_5 : ∀ i, 0 ≤ i → i < 164 → ch_61 i = true := block_join nj_61_4 (fun _ h1 h2 => treeBlockF_at nb_61_5 h1 h2)
theorem nc_61 : ∀ i, 0 ≤ i → i < 164 → ch_61 i = true := nj_61_5
theorem lb_61 : LowerBin m_61 s_61 g_61 9 :=
  lowerDagV5 (kn_cons lb_21 (kn_cons lb_43 (kn_cons lb_38 (kn_cons lb_42 (kn_cons lb_37 (kn_cons lb_50 (kn_cons lb_41 (kn_cons lb_14 (kn_cons lb_8 (kn_cons lb_47 (kn_cons lb_57 (kn_cons lb_1 (kn_cons lb_17 (kn_nil)))))))))))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xf0f0f0f0f0f0f0f0
def s_62 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_62 : Nat := 0x101070105010f0
def ep_62 : Nat := 0x1040008000001060000000a000100060004000e0000000000000000000101020100010000010104010501000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 7, g_25), (m_52, s_52, 5, g_52), (m_39, s_39, 5, g_39), (m_34, s_34, 5, g_34), (m_31, s_31, 5, g_31), (m_53, s_53, 5, g_53), (m_33, s_33, 5, g_33), (m_19, s_19, 4, g_19), (m_12, s_12, 4, g_12), (m_48, s_48, 4, g_48), (m_59, s_59, 5, g_59), (m_0, s_0, 4, g_0), (m_4, s_4, 4, g_4)]
def cc_62_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x7c26a95c75c05a15a05815805425405404e34e04e04a24434404214204014004004003e1364360341340321320038001 0x200983e110a91f94a3b2646e488cc20971183b22066420ac78119c34f3769666d1cbda183a3e2b27c3a0506daf0c93e154a22e8e456b009350144b824d48452f0b452134a620904380a06254080281717c29a984a5e072a40a0500da95134fa06973cd1e75a1ce24f9a4972891e4121c723f8d477008ddd519b614f602967451c70a18d13f182761e4dc34998312f042560449c04918001f 12 4095 5 31 11 2047 19 524287
def cc_62_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x902318c1f4569504c9123c8f03c0a5280a02446318060144320c0300c03004810004000000000000 0x7cd02012f7e4ade9277848efb5cbcd42ea5cb8946aa50a48fe823b928de0a3376171c94454051714c52051693c50051b5606a571613c681713014620b19134600d120145b141734a58d1944504e1012828 10 1023 4 15 11 2047 18 262143
def cc_62_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x944a2190884421f4f87533190c859ac144a04924104803c9548440200e47038150140000 0x29b4ea2d2a634690d0a6c50b2132325cae092da3fb48eec237ac8cea36ca6982006ca2d81f86c9a941f05c9b142584c965427c609d14262607a1b2504c8c97220248c94222508654243608e9b22a5c781b21024 9 511 3 7 11 2047 18 262143
def cc_62_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a5094250942328c2306a5374c1304c13044910440f22d0b0284a0280a0280731c0701485001400 0x3795d8a557d818f4053eb4ef852fc943dc13f184b8411d8043f007fb813ff17bf25eda57f115b8255d7953ec0939460e21337a6cdc093a23fe68ef8237da8cf5944d1583395ccc1732134c60d3534fd2d2f2b47c4d0f093e 10 1023 4 15 11 2047 18 262143
def cc_62_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0700bc6f0b86e0b82e0b82e0a5690a4290916407d5b46c1745c1705c152541323d0f03c0b406801 0x4fa519b8bd368fa65ae4c350972b92c542542e49c5f9248e2651c289fc89278f6bce857da8ada9157382a6e657da4ada8157372a6e4575a0aca7155362a29a90220261693c86029144fe249dc393785266e213d9825a504734087191622e2942450702beca56d24ab99953832990450204263e824 10 1023 4 15 11 2047 19 524287
def cc_62_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x28308040 0x24e53a3925fe310b4be8434 6 63 3 7 10 1023 18 262143
def cur_62 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_62_5 (Nat.sub p 160)) (cc_62_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_62_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_62_2 (Nat.sub p 64)) (cc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_62_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_62_0 : Nat → Nat := unpackHintV5 0xe06036b626b14a357f458b1c6f5541d25ea5d2f4009262a48b042458011c8328d00a4680021e0b0f5cca6de682ca52965000ac83052e1b26f1413382092c383ce6419b260971b44045a150590104c00004000000 0xad31c74d31c74e1c78722e2e2e2cb806db6db1c04c71d34c71d3a1c787ab8b8b8b8b2ea2c32cb2cf2c32cb4b4b2c71c7000000000000b02830c30c30d5d5eaaaa4c0030c30ea87a83974d35c30c30e65e6aaa0eaeaaaaa970000000000003d33cf4c71d3692cb0c32cb4343003cf0cf0d34d34d30cf3c38b8b83aba0c38b8b2d32c72c72cba8b2d2d2cb0c30c000000000000f3e832cb0d357eaaa8002bad87ada7c33eb2e3ebab5cf3c71df4b2da83a99000a87a8f0cf0e8b5d34e6a60cf3c3aaaaaa0eaea800000000000034c30c30d34d34c30c30e2e2e0e25cb8b2d34d34e0175d75cb0034c30c30d34d34c30c30e2e2e830e0eae5cb8b2c34c30c31c30ea0d70d0d0c30cb0c000000000000c0acfa0cf2e4ebadf1cb8b1eacba8f0cf0d37d2d2e99a8021cba1cba830d62c0b134d75355d5ea87a83a8fa8baaaaa975ab5a54000000000000134d34d55562e2e2e2d45534d34d75d75c10b0134d34d554d562e2e2e2d6ad554d51d50d53d554b400000000000404d7550cf3c355a56aea800174d35d51d554f543555556aaa96555ab0000000000004d34d3534d4d35757932e2cb972e2cba55ab2d32c72c72cb2c32cb2cf2c3a95000000000000000000000 21 2097151 9 511
def hc_62_1 : Nat → Nat := unpackHintV5 0xda0034820cd84aaa8c76b41da006b8b186285a87158125184910363f050fc003c030ce2230830c2002d8305a5c13038460611800400609868260006830140603818000e000000000 0x9db1eb8badb9c701b9e76c71c71db9e76c71c71e028aaaaa87a3eaa831c71c7a6a6871c71eaaa87abaaaa200000000000002bacb833d2d2bad3cb5cb2b0cf6b1ad6cadb8c7aeb8b52c33d0aeb1badbaeb0cb0c2b0eb2d34e5833cf0cb2cb2d1d1c02b2eaeb1eb8b6eb6eb6eb2c 18 262143 8 255
def hc_62_2 : Nat → Nat := unpackHintV5 0xc5202b460911c23e068e01a38008885a2200830599874638298806598895e084c8b1161c4005900003a858ea00328809832200606e121b800620c188005c06108680c36018180006 0xc30c31c71c70c30c3a2aaaa00000000551c71c755a255aa000000001c71c7471d0cf3c3a87aa9900000aeb1eb8b2b1cb81c71c71c71c7a887aaaa000000000aaeb3c365aeb2b8f0dad7a3eb1abab5b0f0dac1eb8b236cf0dad91cf0daeb8b0aeb8b89adb03aeb3c35bacf0dae831eb2e0aeb 18 262143 8 255
def hc_62_3 : Nat → Nat := unpackHintV5 0xc245cc0410be80ebe800be800bdc06bd006bc406aa09286d1a82c207f41c7e4087d806788287700c7640671c24584cc58400558164f8304ec064d80a4cc06480264800045c123f43431c6c1010e00080 0x30c30c343575d3d3e2e2c0030d6b0caeb6c30c30c3575750d46db403c00c30c35d576db0c30c30d5d5d430d0dac30c30c70c35433c30c30c35d570e0cb0e0c3000000000030002536bacbab8f4eadaeb1d4dabae2c0ebaeb1e0d3ab22e4c71d3a838fa4c71d39939a87abaaaaaaaa4c000000000002bad1daeb0cf3c75c7adadac7aeb8b51cac33ebacb833c31c3071da433cf0c71c71cb2d2d2c00071c71c71c71e1eae871e2e2e2e2ea1c31c71cf1c31c747471c72c700000000000001c71c71c71c73cf3cfa2aaaa00000000 20 1048575 9 511
def hc_62_4 : Nat → Nat := unpackHintV5 0x7a1519b9d7467837992c5a5b44b95d080532211408604be2211b0a43f73a8f70363c9098ee022327488bf45429c3088391c1ce2006606c1950186480619200061c161870005f0161441c0450600d42002388c0263400004c 0xc30c71cf1c70c30c70eb1d1c71d1c71c71c33cf0c7871c7872c71c71c33cf0d34d34c00000000000030c30c31c3ac33c30c30d71d71d75c30d70c30c3435c3430d31c74c30d30c30c3832c3830d74d74c0000000000001571c75d50d3d51dad555554c71d354b655d35d355530000000000001d745ad433cf0c14e2e2c0071c71c75d1dad471d5d5d51c31c71cf1c31c71c71c74d34d34d531e1cb1e1c70000000000001c71c751551c71c73cf3cf55000000000c30c3545551c71c70c30c35500000000aaaa1c71c7555155000000001c71c75447551c71c72cb2cb55000000001c05d75d71c71c74051554d34d31c71c74d34d35551d4f5550c71c71d555476b5559554b1c71c74d34d355100000000000003aeb7d434f0cf0d5eb0cf5eb472d3931d71d75d471d1dad5d5d55c37cf3d70c71c74c71d35d34d4d4d37e4cb932c000000000001430c30c30d55562e2c00030c30d5475435550dad5550c30c354b655500000000000003cf0cf0d75757436b50c33d73c73c73cf5430c30cf3c35d573e3cb3e3cb0000000000000c71c351550cf3c31c71c755000000003c33c350cf3c3555558b8b00000aeb3c36b2b0cf40cf3c3545550cf3c355000000000aa3c33c3aa555551000000003c33c355512cb2cb0cb2c355000000008db8db3c33c33c05540516e38db0cf3c355547554f0cf0d4f5555550dad65552c33cf0d54004000000000000c350c73c33c32c300c 22 4194303 9 511
def hc_62_5 : Nat → Nat := unpackHintV5 0x83868599503d8e0115620008a 0xc35df3cf0d43471d3cf8b8b000c30c31c3ac71c30c71c75c71cf4f3d3cf0cf3cf0d31c74cf8f2cf8f2c33cf3c34d35d300000000000000c7030c301c0c01c71c70c30c35d75d71c71c70c30c34d34d34d34d30c70eb0c30c30c70c30c31c71c71d70c30c30d0d70d0c31c71c70c30c30e0cb0e0c34d34d300000000300000070c70eb1c73cf430d4f3d1c74d38b8b000 20 1048575 9 511
def nh_62 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_62_5 (Nat.sub p 160)) (hc_62_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_62_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_62_2 (Nat.sub p 64)) (hc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_62_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_62 : Nat → Nat × Nat := unpackForestF 0xa349202d3e841a00b4b9f4a202d1c05a180a4f9b47c0292e55ae4ab50952b92a542542e00a47918bf2291e449380a438f6bc028fc051dc0c58818a50a4fe149dc404c8526f0c0521499c0c508129902502042600a37768bcec979dda73b94b7a030f4051dca1bb81f77026ec0900519b6a3f6d476e3181c42636a376e4d8dc091b5198094f6b288c2d3d85a5b3560662b8cc17185a3b193463068c2d0d849f0094b3b6b876d40ed2e1da515647eac8ed64262b23757048ac8cced2829b6c534c0768fd45b01da3b4a8c0951413628252604b2a094130ed1ba1360424d88c941092e21a50432a084090ed199e12f3c2567cd00f0939e1233b0b80251ce4a20eb4f1d69669580d0ae1a05c1d68e604d0c416180341d68658d28b628163461d27c3c8fc791d93c50270803c8dc94140f2331e0763c0cc78158f84c1f0883c08c740a009431b6bc024fc649f0093b174722114852b00a25c104a622d48452f082410126e1c050049986254078be0ed4c1d2f04014072a4024bc140a0092b036a40249c04918001f 8 11
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 4 15 bds_62 164 (dagTraceF m_62 s_62 8 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 4 15 164 bds_62 (dagTraceF m_62 s_62 8 f_62) (cur_62 0) (nh_62 0) s_62 8 = true := by decide +kernel
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
theorem nb_62_5 : treeBlockF 160 164 ch_62 = true := by decide +kernel
theorem nj_62_1 : ∀ i, 0 ≤ i → i < 64 → ch_62 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_62_1 h1 h2)
theorem nj_62_2 : ∀ i, 0 ≤ i → i < 96 → ch_62 i = true := block_join nj_62_1 (fun _ h1 h2 => treeBlockF_at nb_62_2 h1 h2)
theorem nj_62_3 : ∀ i, 0 ≤ i → i < 128 → ch_62 i = true := block_join nj_62_2 (fun _ h1 h2 => treeBlockF_at nb_62_3 h1 h2)
theorem nj_62_4 : ∀ i, 0 ≤ i → i < 160 → ch_62 i = true := block_join nj_62_3 (fun _ h1 h2 => treeBlockF_at nb_62_4 h1 h2)
theorem nj_62_5 : ∀ i, 0 ≤ i → i < 164 → ch_62 i = true := block_join nj_62_4 (fun _ h1 h2 => treeBlockF_at nb_62_5 h1 h2)
theorem nc_62 : ∀ i, 0 ≤ i → i < 164 → ch_62 i = true := nj_62_5
theorem lb_62 : LowerBin m_62 s_62 g_62 9 :=
  lowerDagV5 (kn_cons lb_25 (kn_cons lb_52 (kn_cons lb_39 (kn_cons lb_34 (kn_cons lb_31 (kn_cons lb_53 (kn_cons lb_33 (kn_cons lb_19 (kn_cons lb_12 (kn_cons lb_48 (kn_cons lb_59 (kn_cons lb_0 (kn_cons lb_4 (kn_nil)))))))))))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0x3333333333333333
def s_63 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_63 : Nat := 0x113133311131333
def ep_63 : Nat := 0x1000000000001220000002200012002000020020010202000002020000000000000000000110100011101000
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28)]
def cur_63 : Nat → List (Nat × Nat) := fun _ => []
def nh_63 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 1 1 0 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_63 g_63 ep_63 1 1 bds_63 0 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_28 (kn_nil)) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xcccccccccccccccc
def s_64 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_64 : Nat := 0x4044404440ccc
def ep_64 : Nat := 0x4400888000004400000088800040040004000c00004040004000c0000000000000000000004044404440000
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 5, g_40), (m_27, s_27, 5, g_27), (m_55, s_55, 5, g_55), (m_42, s_42, 5, g_42), (m_45, s_45, 5, g_45), (m_34, s_34, 5, g_34), (m_58, s_58, 5, g_58), (m_6, s_6, 4, g_6), (m_18, s_18, 4, g_18)]
def cur_64 : Nat → List (Nat × Nat) := unpackCursorV5 0x119 0xddf 3 7 1 1 5 31 6 63
def nh_64 : Nat → Nat := unpackHintV5 0x845000840000 0x9d4d6f7ac6738c9180407d2cf4338ce3b90b1e0c393656bd1a744 16 65535 8 255
def f_64 : Nat → Nat × Nat := unpackForestF 0xddf 1 5
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 3 7 bds_64 2 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 3 7 2 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64 : treeBlockF 0 2 ch_64 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 2 → ch_64 i = true := fun _ h1 h2 => treeBlockF_at nb_64 h1 h2
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_40 (kn_cons lb_27 (kn_cons lb_55 (kn_cons lb_42 (kn_cons lb_45 (kn_cons lb_34 (kn_cons lb_58 (kn_cons lb_6 (kn_cons lb_18 (kn_nil)))))))))) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xffffffff00000000
def s_65 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_65 : Nat := 0x117177700000000
def ep_65 : Nat := 0x1660000000000016006000000000010606000000000001121222000000000114144400000000
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_21, s_21, 7, g_21), (m_28, s_28, 7, g_28), (m_26, s_26, 5, g_26), (m_32, s_32, 7, g_32), (m_25, s_25, 7, g_25), (m_23, s_23, 5, g_23), (m_24, s_24, 5, g_24), (m_27, s_27, 5, g_27), (m_30, s_30, 5, g_30), (m_15, s_15, 4, g_15), (m_1, s_1, 4, g_1), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_0, s_0, 4, g_0), (m_11, s_11, 4, g_11), (m_17, s_17, 4, g_17), (m_5, s_5, 4, g_5), (m_4, s_4, 4, g_4), (m_13, s_13, 4, g_13), (m_3, s_3, 4, g_3), (m_2, s_2, 4, g_2), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10)]
def cc_65_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8351d4341d0340cc6f4bc2f0b86e0b46d0b42a3a468194e328861178de0781e06cda1608bd06801 0x71b00e560192783b5886db10d16e182c42b14c4da409453116a020d001c1a028240e6901a520101206453030480c0d014920534809290080901d1c031380507008d0c222981824288a64cd7c91a791a5e204a63e94879270ba4316484288e83d1b059360206d2ad0e4527c5a3f8629efe4fd9493ae84f5307e6209c040b8001f 10 1023 4 15 11 2047 19 524287
def cc_65_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xd4714c4310c0700bc6f0b86d1b06939c9ad681a06098058951541411f47018460144501044001000 0x7e9321d628318a026e7c989dc59731b9bc530e05030146ad21a248080519c5306052545392d7a33538ad4a234e7ad0de3427457dc14f6c4f479356449410161a8d8483632d316a4c540d1503444984ea51609297a495c921624630904aa3a248d95946184d94846100d93c594b1b8e36045584db5242578c152 10 1023 4 15 11 2047 18 262143
def cc_65_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc066a94650942509425094241901aa681a06098058951541411f4701846009020080110400100000 0x2fc59c8d26db41929371a45c48fd194dc2517013fbc49ea03eac49eb46eb8d7adb52b497e223db28d6c15f3c4f6b935aa49ea05e684d450167ed32794c980d2613490d861b51a4d2a8b49a0d2273467cd066a466e4f491356649658461005a1460915860c528e979f252851821560 10 1023 4 15 11 2047 18 262143
def cc_65_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb82e0b0ac0a8a91a42816f5b0685a0591605815154141501404c4f43c0f03841d004000000000000 0x6a0d47015d6d33d84cf04d3c134e8d877b51fcd2beb49f8d23d346d4d07ca46ee51b383d240d59825180577460e95876c52e697b5252dd1837560d69337d62db18b626ed498b3c53ed14fab5ee4d4f8b52e0d3b4b43d0d0af05faa13f303d1e0d5902516056f927 10 1023 4 15 11 2047 18 262143
def cc_65_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9410a21042082304200b88700b3158ab056086900a004008010016a2a2540a8150174284500a01402805000a 0xa0935ea459f8d5dd269e134b045980d4ac154c090a8149b9353a459a8d6654d2c51661354b098a4168f8f68a37a18d6113d9d4de71357649d6c3d970de58354a09ca0172705e53498fd063a3e755364d45834fd244d92115683f2605c941790d7a3f528e97a215f704f635356217d103d8c0d490173b09e2b4984d05d64d89916223f814f88c4d87115603f3a09ce42785d7a13528397dc23d828d6055e6017c783d800d4e027 11 2047 4 15 10 1023 18 262143
def cc_65_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x909018101001 0x1494d7aa2cfcd5e64b464d4e22cd0d5344af124 8 255 4 15 9 511 17 131071
def cur_65 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_65_5 (Nat.sub p 160)) (cc_65_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_65_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_65_2 (Nat.sub p 64)) (cc_65_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_65_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_65_0 : Nat → Nat := unpackHintV5 0xb797ada20d6ca43760626ae60ed73002b383140ac98ec8cc570f9e224cf04067342735e1e18d50ea311d5160128781d37464755333a8011d081cdbc646de0036f001b7800d483a4e6df14099834b5c000d200000 0x2a879b0e1c3871e3e879f0e1c5d50f062c58f062c5aa8aa3d55000007800001c78f261c3c3caf07ab85e361e0f4073741e05a3406858f0e1e1e3ea859f1e2d52601c3c3c59f3e2ea40007a2000155174e1c38baa85aaaaa2a97361c3870e5cbd0f162cb832e0c58b50000000000000000818b4997067c183e0f03060c183160c1d0316aaaaa2a0cd83060c383060cbd503060c18350000000000000000aa0e6e2e0c197160d260f0740cdd1b060c18355515500000000060c1832e1c397818306aaa2aa00000001078183061c187060c19b060c1d03a8197060c183060e8183060d555506a8800000c000005c0c5831e0b079078187064c1d13061c18b0742d51e1c3931f44c58b000058b064c162c58b000009800000030111703160c7a2d26c0c183c60f03060c183a060c183060e81a80003c3871e3e8783060000306a2ac1e061c18f0743c187062c1d0b007870e3c7d0f162d555162c18f458b162d55551eaaaaaa0d4083c1c38ba163c3870e1c7d50b167c78b16aaaaaa800000000820010783871742d0eb22d40e102c10 21 2097151 9 511
def hc_65_1 : Nat → Nat := unpackHintV5 0xfdd0ef8cb1380233ba030cb78ce410d6dce1f66a3ea1e8bd0e00a868053e42890576c0d3ae0102cfe6117ae22bd6009e4436ed6267550b3978998e1eec06354bda32418e8d6e504b8ff2311590c8604b5d80012d 0x58af017030e0e060ea81c01c3c0ea8054683458346a340180c00001f5517061c18b81d417361c3870e5cbd03a0004e8765945a0d2e4d4b93500000000000008b83560cb9345a5e1c3870e4c1835e8e5a3060c9a3268e9383160c582d70e8757a8d26aaa800b0580087360d383364d03875ea8c38757544c1835e8e3a3060c9a3260c583160bd5af328d26aaa800b05800c2c197268c99341f078187062c1d0b266c3870e1c993265ea8993500049aaa4d54541a83400000000000006060c49a0f20f03060c183a060c183060e81a8000aaaa83506a2a800000c00001800210781870e0c383aa061c18b0742c043aca3506a2c5a0d00000580b000002a838f2e02341eaa160c18b4000283d071726cb84cb8457ae306cba3cbac1eaa83a3168c5870e1c3870e6eaa8b971e3c78f2e5c58b5549a80003c11008b8f563cb8316071748c387ae1c5870e8c5870e1c3831e0d19f7e7c78f067c19fa4e2c19f060c58b16aa8300001a2001cd8f4e3cd8316070e8e168c5d5785d1f0e1d5d5031e0d19f767c78f067c18b067c183162c5aaa0c00006880070e3e0f07a1e5e878f0e1c3871e0c58b1e0c58b3f42c551eaaaa8003c000000878f2741c7917a8381c38b0e3c7870e1c38fa167c78b5498071f42cf9f161c38740007a20001070f07361c3870e1c5aba16aa8aaaa1c38f365ea8d97162cd83360c58b50000000000000000 21 2097151 9 511
def hc_65_2 : Nat → Nat := unpackHintV5 0x8d9c66178f77d9429d66ff6c848d8ff115bd4154e70751f0d525f0f3fecc8e2ae837f858dd216352114d4402346058cc22b32306cc2235280c407f1091e68ac76a18164bb032537049bfc0bc3502186c03a2600007400000 0xa3e1c3870e3c1833ece99f060c79f1e9e9383160c5aaa8b45aa8570e070f87c1e0000010783d2ba1e1c3870e3c58b3e2c5d0b0e8747ab75645a815c0e00700000000e1c79550050070e1c39b062c59b062c5d50743a6c9a9b26b322d40000000000002a03871f43c3870e1ea8783162c783162c3a1d991e3d47935169f400001e00000717541c3870e0cf833e3c7ab3efc18f0601c3d70e2c387a062c18b56b34fabd0e0005788060c187060c19baaa000060c183060c1d452343a0c9a8306b320d0680000000000002d5070e1c3934e4d38f1ead3cb263c782b170c5a3168c5ad70e876554380015e209930e1c387266ea940017870e2c983162c983162ea9551eb22aa800000000000007360d383368f03873e0ac38757543c1833ece79f060c79f1e0c58316aaa2d16aa7c0af107c1e0000015550faabc1c7870e1c387af5070f55001c3870e3c58f17543c58f161d0e8f47b323d1e8b4fb549c3870e1c7801c38baa1e2c59f162d0ecc8f56ea2d40002b90100001541c197005940eaa1600b2693400a0f41d859b2e032e115eb82e0d97163cb8b1707aaa0e1c3870e1c39baaa2e5c183060cb97062c58b060c582f57aa2c001e0b058000c38383c1e8197a060c060c183060c1d030e8741835064d51b20d068000c00000081830741c7917a8381c183061c183060e81830060e81870e0c054683458346a340180c00001f070f07360c187060c0742c183066cbd51b2e1c38000750eaad916834d935364d40000000000002a819b060c187060e8183060c19503060d1a1d99060d4193506834000006000007060c187070f2bc0eae178d8783d01cdd038 22 4194303 9 511
def hc_65_3 : Nat → Nat := unpackHintV5 0x85c05a1441682e9160b60282285a0342b7ff86df943575d441b63096c30adadc186413b1697375263fd42e354fe06d3ac264dc875372004ce0751b0c43dfc64f023e33545cafeeb23d4146ab25120c5026b0c01841400030 0x2a83832ea8b681d542d555163c1e341e8390b365d065d66bd745c9b2e2c997162e0f5541c3870e1c387375545cb83060c1972e0c58b160c18b55549a2d16aa7c3e00b4187070783d032f40c1a0c183060c183a06aa8355554381c060c018f0564030188903060e839362f5074383060c383060c1d0306a0c1d030e1c1aaa0d06aaaa0cc060b067c3e24e0e1e0e6c1830e0c1a0e8583060cd97aa365c387555555555555550e01c15902c061b1e06c78225503360c1830e0c1d03060c1836a060c1aaaaa0d554e072201830063c0180c440e0c1830e0e26d781d5d2f1b0f07a439ba0722d5161f8187070307540e50e1e0754aa8341aaaa8330182c19f0f893aa8b830e0c5c0ea4b9b0e1c3872e5e81d2aaaaaaaaaaaaaa70390402c06171e05c782245c7b31e2c1a4c7907879b0e1c3871e3c797aa1e3c187062c1d0b50005555500051078003c0006000300120f030e1c18707540c383160e85aaaaaa8b516aaa07086600c058b018a25141c028287870e1c3d517062c597062c58743b325c9a9726a2d40000000000000187000a060e819783c1c183060c18301870740c1935060d43a1d46c8341a00000000000001541c3870e3cf8f3e0c19f4eec783070b0e1c18b062eabc2e8fabd4eb342b87039000a00144c9d132f078393062c593062c5870e1c3afa168f50e8aaaaa00000000000001541c3870e3d38f4e4c9ab4f1c7931ea8c5a3169c5c3161d555af3215c381c8008b83560cba3c 22 4194303 9 511
def hc_65_4 : Nat → Nat := unpackHintV5 0xe2184f75a96d47c7b4e41dd2609b47213d0e87330e96c34c7af1cdbb3847aa9725a134965fb298efc7a1ad097d9c8dd4f0c6cdc3193efc5cd4154eb254b0c510ab0c3af3dcca90a2aabfc86523190c443df3207441c000e8 0x24007c1ea9595a83aa2c597162c3b25d2e935540b83534aab4aaa1c3870f544c18b164c18b16875565549aaa4d0e0722098f0263c058bc512642c0160e16003163c90127201347907aa0202a0e00b165c58b52ea1c82e17078005450005000070e1c3d50f062c58f062c58743b323c9a8f1ea2d3e81c008001e000f00079507aaaa83870e1c3d517162c58b0e87664baa8b50e07220b800b042aa0f5541c3d0383830f03aa060eaa83a1d992e4d4b93516834381c882e3c0b8f01603100e1d5560f07a264e899743830eaa0c1a83a16875541aaaaa0d0e07098f0263c19902c0622070e0010783d0f1f43cb81c18700060c01d0b0e87479351e3d5bb22d0681c0006000003000387170783d2ba061c387ae0c387160c3870742c58743a0d51ab22d06870380c1f8102c06200c183aaaaaaa060c383075070f55541d0e9b26a6c9acc8b41a1c0e1b1e06c78440b018855030e0e81c0c183aa060c18743b320c1a8326a0d0687039100c18031e00c0622301870755503aabc0c183060c383af50307555030e8741a0d9906834381c0603220180c4465513261c3870e4cdd2aa830e0c5b52ad2aab2aa0d5506b3039104c78131e02c0622550f1e1c3870e3cdd000030e0c59500503743b323c9a8f1ea2d068010000c0006005527061c3870742c187062c5d55ea17521d9906a8d45a0d039100c1d80b01885341d569689870e1c3d517062c597062c5aaaaaaaaaaa87039105c78171e02c110187555a060e819783c1c183060c18341870740d5555555555418f0060c0381c8640301888b541c3870e4d193460c1ab46ec983070b0e1c18b062eabc2e96b8743b2aa7c3e231b8a0010783d0f1f43cb870e1c38f062c58f062c59fa162a00a0aaaa07000780000008ac1e0f4ae89870e1c393162d78b1742d5ae87543aaaaa870384c198102c11038726d54ab4a1c3870e6c18b166c18b1754aaaaaaaaaaa1c0e1b1e06c78440b044a90e1c9d130e1c387aa260c58b260c58b555549aaa1c0e44131e04c780b178881c5d5070e1c383460d193268d3bf064c1a870f5c38b0e1e818b062c3aaab5e6518dc3e1f0183061c183066eaa9554183060c18307534aaaaaaaaaab0c0e031e00c18440301888ad5544eaaf07261c3870e1ebd41c3d54a870e1c393164c5d513164c5870384c2644130982c5e550f1e1c3870e3cda8001f0e1c5d50f062c58f062c5aa8a80282a8010003c00004aa4e1c3870e4d50e1c5d513162d78b16aaab5d95955039104c1980b044 22 4194303 9 511
def hc_65_5 : Nat → Nat := unpackHintV5 0x25f0c48e186118621d04260e80026 0x42d549c2c007c1ea83d55541c58b161c3d17165c183162c58b52ea2c0b80baaa061eaaaaa818307030f5540c1830e876641935060d418b41834381c88063c01830062c060c44642d5160e16a83164d 19 524287 9 511
def nh_65 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_65_5 (Nat.sub p 160)) (hc_65_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_65_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_65_2 (Nat.sub p 64)) (hc_65_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_65_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_65 : Nat → Nat × Nat := unpackForestF 0x5194da309b2c8de591acf24d9e46b3c136589bcb1359849b308d660a6cc1359606f2c0d405a1c93499228b241140527c635e8c6a51897a309ac60350147f0ed261d22c3a3f8708a0253e01af40352804bf008d600af400350127eeed29dda4bbb487b098eed19dd233c1347728ccd14d99af39d61734bcccd4d99a93334e6aac4dd581aa313526e6b498d498999a1b3342678a6cc0f40493af3495e48abc8fd78a2af13f5f8b2bc49c0427aa35e546a4a897d511aaa15f5426aad1b95093aa05e0107e96d292da4a5b484f29896d192d23261344b08c6514cc9af23d61474bc64d4cc9a91934e3eac485580fa311f26e3f4987c988c9a1993423b8b26457ce6371914f378a6644f4d1a41a248338a664494041394a4a2949252920b52614a462928c540d0a42301453278b204d7c96370134f024bc4358484af01253024a40493862b10e560186c4305b8649e0c162024860490856298123a136902114c41a8083400246c1ad2034a4064530226c12d2024a401c53054700a4e0141c0234303048040d8040b8001f 8 11
def ch_65 : Nat → Bool := dagCheckNodeV5 m_65 g_65 ep_65 5 31 bds_65 165 (dagTraceF m_65 s_65 9 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 5 31 165 bds_65 (dagTraceF m_65 s_65 9 f_65) (cur_65 0) (nh_65 0) s_65 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_0 : treeBlockF 0 32 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_1 : treeBlockF 32 64 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_2 : treeBlockF 64 96 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_3 : treeBlockF 96 128 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_4 : treeBlockF 128 160 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_5 : treeBlockF 160 165 ch_65 = true := by decide +kernel
theorem nj_65_1 : ∀ i, 0 ≤ i → i < 64 → ch_65 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_65_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_65_1 h1 h2)
theorem nj_65_2 : ∀ i, 0 ≤ i → i < 96 → ch_65 i = true := block_join nj_65_1 (fun _ h1 h2 => treeBlockF_at nb_65_2 h1 h2)
theorem nj_65_3 : ∀ i, 0 ≤ i → i < 128 → ch_65 i = true := block_join nj_65_2 (fun _ h1 h2 => treeBlockF_at nb_65_3 h1 h2)
theorem nj_65_4 : ∀ i, 0 ≤ i → i < 160 → ch_65 i = true := block_join nj_65_3 (fun _ h1 h2 => treeBlockF_at nb_65_4 h1 h2)
theorem nj_65_5 : ∀ i, 0 ≤ i → i < 165 → ch_65 i = true := block_join nj_65_4 (fun _ h1 h2 => treeBlockF_at nb_65_5 h1 h2)
theorem nc_65 : ∀ i, 0 ≤ i → i < 165 → ch_65 i = true := nj_65_5
theorem lb_65 : LowerBin m_65 s_65 g_65 10 :=
  lowerDagV5 (kn_cons lb_22 (kn_cons lb_21 (kn_cons lb_28 (kn_cons lb_26 (kn_cons lb_32 (kn_cons lb_25 (kn_cons lb_23 (kn_cons lb_24 (kn_cons lb_27 (kn_cons lb_30 (kn_cons lb_15 (kn_cons lb_1 (kn_cons lb_6 (kn_cons lb_7 (kn_cons lb_0 (kn_cons lb_11 (kn_cons lb_17 (kn_cons lb_5 (kn_cons lb_4 (kn_cons lb_13 (kn_cons lb_3 (kn_cons lb_2 (kn_cons lb_9 (kn_cons lb_10 (kn_nil))))))))))))))))))))))))) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xffffffff
def s_66 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_66 : Nat := 0x15571fff
def ep_66 : Nat := 0xaa800000000004200e00000000004020e0000000000100210000000000015541000
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_46, s_46, 6, g_46)]
def cur_66 : Nat → List (Nat × Nat) := fun _ => []
def nh_66 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_66 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 1 1 0 bds_66 (dagTraceF m_66 s_66 6 f_66) (cur_66 0) (nh_66 0) s_66 6 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_66 g_66 ep_66 1 1 bds_66 0 (dagTraceF m_66 s_66 6 f_66) cur_66 nh_66 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_66 : LowerBin m_66 s_66 g_66 7 :=
  lowerDagV5 (kn_cons lb_46 (kn_nil)) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0xffff0000ffff0000
def s_67 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_67 : Nat := 0x117000015570000
def ep_67 : Nat := 0x1440000000000000000000000016000000420000010600000402000001120000100200000114000015540000
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_36, s_36, 7, g_36), (m_53, s_53, 5, g_53), (m_35, s_35, 5, g_35), (m_54, s_54, 5, g_54), (m_40, s_40, 5, g_40), (m_51, s_51, 5, g_51), (m_50, s_50, 5, g_50), (m_46, s_46, 6, g_46)]
def cur_67 : Nat → List (Nat × Nat) := unpackCursorV5 0x13098486411188442030078bc1e0e1703443801 0x3230cd11d30791092028d3e3fe8ef637b8ce93f94ee13764cd52f44acd27148c01f 9 511 4 15 10 1023 14 16383
def nh_67 : Nat → Nat := unpackHintV5 0xacedba17b7945d28d76e816c1726f0636f054fe74cc833cffd318b723ddb16bd20fd6e03cc10003c00000 0xaaaaab52aac3b631d0c635558c6b39cf33bce78e784000000000001555561dbaa55558754aa318c75554e7d08000000000002aaaaad4aa319c63a872a8de318c6398c631c73c2000000000000aaaab0edaa8c631d508000004002aaaaad543955563d52aac635d55539f4200000000045c0015555556b5aaac635aceb9675caaa31bf631ad6318def7bc4000000000001555546318d54637ec6318df37cd55546318e18c671c358c4000000000001555554631aa8ce38631c318c6aa31ac6318c637bdef788000000000002aaaa8c631aa8c6bdad6b58800000002c5555558c6b5555ac6318def9be6aaaab5ad72ceb3ae18c62000000000002cb82aaad52aaacba87552aabdef7d3f755471000000000000555553c7955f37ce9fb39e95554eb38ce339ce73d42000000000000aaaaaa739c6719d6aa78f1ce7557bdefaa8e7a788000000000002aaaa9ce73aad547b62000000010aaaab54aaaf9be7554f55559750eaa8f0800000000001170555555100000000 20 1048575 8 255
def f_67 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
def ch_67 : Nat → Bool := dagCheckNodeV5 m_67 g_67 ep_67 3 7 bds_67 16 (dagTraceF m_67 s_67 8 f_67) cur_67 nh_67
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 3 7 16 bds_67 (dagTraceF m_67 s_67 8 f_67) (cur_67 0) (nh_67 0) s_67 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67 : treeBlockF 0 16 ch_67 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 16 → ch_67 i = true := fun _ h1 h2 => treeBlockF_at nb_67 h1 h2
theorem lb_67 : LowerBin m_67 s_67 g_67 9 :=
  lowerDagV5 (kn_cons lb_22 (kn_cons lb_36 (kn_cons lb_53 (kn_cons lb_35 (kn_cons lb_54 (kn_cons lb_40 (kn_cons lb_51 (kn_cons lb_50 (kn_cons lb_46 (kn_nil)))))))))) rc_67 nc_67 (by decide +kernel)

def g_68 : Nat := 0x117177715571fff
def ep_68 : Nat := 0x144008880000166000000aa800160060004200e00106060004020e0001121222100210000114144415541000
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_67, s_67, 9, g_67), (m_65, s_65, 10, g_65), (m_45, s_45, 5, g_45), (m_36, s_36, 7, g_36), (m_54, s_54, 5, g_54), (m_21, s_21, 7, g_21), (m_25, s_25, 7, g_25), (m_62, s_62, 9, g_62), (m_64, s_64, 8, g_64), (m_61, s_61, 9, g_61), (m_63, s_63, 8, g_63), (m_60, s_60, 7, g_60), (m_19, s_19, 4, g_19), (m_38, s_38, 5, g_38), (m_14, s_14, 4, g_14), (m_8, s_8, 4, g_8), (m_58, s_58, 5, g_58), (m_66, s_66, 7, g_66), (m_7, s_7, 4, g_7), (m_2, s_2, 4, g_2), (m_12, s_12, 4, g_12), (m_52, s_52, 5, g_52), (m_55, s_55, 5, g_55), (m_51, s_51, 5, g_51), (m_32, s_32, 7, g_32), (m_20, s_20, 5, g_20), (m_40, s_40, 5, g_40), (m_35, s_35, 5, g_35), (m_49, s_49, 5, g_49), (m_56, s_56, 4, g_56), (m_33, s_33, 5, g_33), (m_44, s_44, 5, g_44), (m_41, s_41, 5, g_41), (m_46, s_46, 6, g_46)]
def cc_68_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8a08248208018007c27827807807237207017007006e16456406216206206206015655605605605605604c5292033001 0x106720db500fa6c0f16c0e25c0dc640d02406454023540bd6f0b46e062450895c08a620a57209b72063480925c0815c0515c054620756f06c630634e05a4e0494e03d6f0346302a63022390194e20d6f1e5631cc6f1ac5f194571836f1736e1636314b6211b5f10b5b0eb570cb530c34b0ab4a07b470434601246e4c5fe1c5bdf457da453d535fd4357d034fcc347c3a5fc0a57b9a4fb32477ca377315f581574e94f4114722937009270003f 12 4095 5 31 11 2047 20 1048575
def cc_68_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xe8e8ccc8c8b3b0b0b09490908280797871705450504240403938381509010000 0x203587ed51f2547a551db6874d90b348715f95b726ed61b35468db19b60625917b554d1b89c560ad596a565717d52464e951457e4cdc913684a951215438951146c 8 255 3 7 11 2047 18 262143
def cc_68_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc7782f05e0bc1592b0560a4538a704e090720230c608c1105d2ba0740e81d03a060a348600c018001800000 0xc11a2fc64a6932ed7eb91cadc58b5152c46caf1805a5490912a56fa69b85a369c5727362a35ca84729ed705a4c9a5725d6f9518e4b63908fa394efd5bfcd63ef1bfac6ee718f8c62d717f4c5bcb15f0c53bc9beca5fac95eaa4fa49366247109163235891961b6884d90bb4a1cd183a46 11 2047 5 31 11 2047 18 262143
def cc_68_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x6f361b0d86c2f170b1582a5508c441e8f078389c0e04d208e470381c0703011080080000 0x40c68808c8fe9955126872454b46afb161f22a3db547a2a8f0591d92ab756e504aa92915d11aae25f7246aded51c2bf374726a8d0dad51b0aa323546aad8d19c98e2833b6c662d8c8d718eb231034 9 511 3 7 11 2047 19 524287
def cc_68_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xa2c5a21107dbe1f0dc6c36178b85c2e138984c260f878389c0c46030164b035030000000 0x5257ea38e545162862a4f94cad8dd56dbea5a2d3a6fa548b3c8de71a2cda458a46f335a259ae4c2658f4bb2cdba4537c3a4d9548b275a249b2c8b5d8d4b91edbe1da6c73458d4dd171621ab844b7c86ae5159ca2239c3c6c858c3091826ab14bb6f946bb209be312ec1a37 9 511 3 7 11 2047 19 524287
def cc_68_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x915e6781d1741c1701b16c1a1681a0609352e0b02c083200711c0521404110022044100401004001 0x62d80c471984df2cc465f834d38f9a51c722386345bbe8a7641f2f09add14db846b6c936d1a5d9b43bb47f728dedc9fda937b224fc8db781a7eeb47db4dbae93f5123dea37b10d95ed56b92ad2237ac8c954976852ad4464a66bb42d5680a65046e 10 1023 4 15 11 2047 19 524287
def cc_68_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x94c4e20fb7c3c5e0d46832566b0512652289441e8f0713816c7838150683018088402002 0x2e83e6fd70de4bb721f34daeee355d849d701f36a3e6cb45d84f96e1f2d83e6b570d56bb6a1f31eb562d62d06d198d53423665b50ce0d998d732e3261b7cca069a2d7f3dade6b57c96a78f602d04661b7cc1069871c3063860270 9 511 3 7 11 2047 19 524287
def cc_68_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xf03e03c0780dcafe1f03c1780e85d0381700d85a0b21640c8161ac0580a09401e520e400518a014020402000 0x515c7f5727ec727e35c7da5c0494cb056fae56bab567a7d63a646fa546ea3c6ba04679c4639ac629845f96c5b8fc57864537396f5e9674f15f419578114f7f94d7d1470414523135011257c2457b25d7a3457935d775627595c775707515c7683475c5a754527846177c5b764537494e7414c3ab5d7bb4f7ab471725d79a4f78a4773a377134e69a5d72a555e07c71c7c7137c70a455d87c 11 2047 5 31 11 2047 20 1048575
def cc_68_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730cc330cc2d6b42d0b42a3a0a809c6709c27094a055e57054950505314c1304c0e51645014005 0x8315d8ec658e3468db447714d8d145899358c5628bd608b35c611758294d89d728825c8782488a6b872637686f5f8678204d8f67e8cd728ad648a37e7617f5f1778195d891358683485d7883560849367597e8367e7757282b7e7517e820348567f8457283d6a81d62784727497e04954239340192480d6f805637416e4f95e04946 10 1023 4 15 11 2047 20 1048575
def cc_68_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8360ccf12c06f18f2308c203801f17c1f0695a0645455012240900400c4300c0300b12c0b024809 0x9fd609f36d9eb6c8e5708ed608496c8d5629e57499d6e8cd629db67441678415d7e955251457813d9d1379c935031259bd695195f9b135943549a57e99c72974689935498a548b35497d7a9756c7797f631778395d94c788c4608bc6094c5a94e709436c9216c9086c9236a9156790b6a9667895e729567093c7a8ac509336c92a6c9196c9006c 10 1023 4 15 11 2047 20 1048575
def cc_68_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x88441e8f0783c1e0f066b2190c160301809648240e87034984c044200e470381c0e00e00 0x9bc70afc58af454ae854adc7cad471acc70ac37caba7caa14caac58a9c54a9354a8a54a81558014da467ea4c78a7364a6a64a59559eb64a4d7c97d6a93d66a435e9fc60a357ca2d709e460a237ca1a7ca117ca087c 9 511 3 7 11 2047 20 1048575
def cc_68_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8f20c82f3bc2e1b82a4a82a09cdf87c1f0749d0741b26c1a16816458142320b12c0b02c0a102800 0xc0355bf9552e937bec64be165bb145bd47c7a16f6c967bc15d2d155bb36fbab4d2d345bf46ebdb6fbcb67bbb457996f6b967ba1452c937b9345b8945b7d68b7165b65707916f6a9672c14db51452c35db4355b8562b6b6fb5b67b4b5d7896f6a167b395d2b1378595db1461b2c69b2468b1c648f451b09658514f8094d071452593503925 10 1023 4 15 11 2047 20 1048575
def cc_68_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc2d2b4294a42727e1f0785e0781e06cdb06c1836016258160581604905d14050104400c40300000 0xcfa45cf1457b16f6f1671a15dce1551a25dcd255ced62c6a6fc1267cda5d7a96f6e967cc95d19127cb844c996d2f96549147c8c64c5165c8145c7568c4965c5b5d2fb55c534fc4b47cb45bcac57a535dca357c9355c7b4fc6b471715dc6157c41555394f481472f137c2c7cc1d70c336dc234fc1347 10 1023 4 15 11 2047 20 1048575
def cc_68_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x8670c2183d67a0f41bb3706e0c1d532a0522a41482904c6981302242ba540919202403cc780b416020c04000 0xe0b6ddfa6dab237dea4da9a45a9235de14d3e1453d935dd34da9b45a8a36dc94d1f9451f125dbb4d3e345db24d1fa45a82373d1361e926ddb45dc245a7a37da9453c9371e127d9844d795d1d1554c147d625d1d255be24fb7247d945bd8c57a525dd8257d7255bda4fb6a473a95dd6957d59555594f4b9471c927d4a6dbca4fb5a47d3a55d31551c1277c16f70967d214d1b145c826fd124d1b245d2c6ec7a6fc2267d1a457b96f70167d09451a927 11 2047 4 15 11 2047 20 1048575
def cc_68_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x90481faf87c355a0d0569f8f06a34168a2341806c3003 0xe94bb63957a2aea01552224fcfd76c7aaf395d212aa7f4df99aea0355e5cba42956c31bf4355e6cab608df94aa9f93720a4fc8936bd22f1b4daf68b5d49f8fa2f1645ae46fc4112b736f0a65ac46b5bdb781b2d5e36 9 511 3 7 10 1023 19 524287
def cur_68 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_68_14 (Nat.sub p 448)) (cc_68_13 (Nat.sub p 416)) (Nat.blt p 448)) (Bool.rec (cc_68_12 (Nat.sub p 384)) (cc_68_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 416)) (Bool.rec (Bool.rec (cc_68_10 (Nat.sub p 320)) (cc_68_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (cc_68_8 (Nat.sub p 256)) (cc_68_7 (Nat.sub p 224)) (Nat.blt p 256)) (Nat.blt p 288)) (Nat.blt p 352)) (Bool.rec (Bool.rec (Bool.rec (cc_68_6 (Nat.sub p 192)) (cc_68_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (cc_68_4 (Nat.sub p 128)) (cc_68_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (cc_68_2 (Nat.sub p 64)) (cc_68_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_68_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 224)
def hc_68_0 : Nat → Nat := unpackHintV5 0xee8239c6b59775c5eeb24e5ccd25f80365eb8b1f528d2298034714b6d60a67c3f04927669e8ea7099b2889b0ed595ba98cac52c13ec67a488d446c0947ea3b8d8e919890a32be1504d928c80a6a0c4cf20f724a09356c00049800000 0x560c1abaa80660c193564d593aaaa80002abf855544eaa03f805151ba80555555555555a81d555547060c9d1eaa1f55503a9fd45eaa3f5551ea275555151ba800020000082003faaaaaaaaaaaaaaaa80552f060c9d5554157fbfc0000007f3f87ffffd5555555402aa5ebc183275555551baaaaaaa80002000fe01fcfe00aaaaaaaaab20154bc1832755503a97d55054bea27555146ea0178306be549b3664e3eaab5400000041001fc025f54bc1832755503a97d45eaaa97d44eaaaa28dd404bea075543ea8f551fa000000000020800fe0000aaaaaaaaaaaaaaaca802f81c1d783063c9c3c3d2f060e06bd7cce5f4797c3e2707878f81c2eaa820f0b017af060c1830ebe839f5e7eaa1e3c78f162c0000000000001602c00fe0000aaaaaaaaaaaaaaaa0140efe0e060c1830e3c38f85c2e8183060cf9f3e7c3873ebe39f0e1e3e7ea160000002aaa83061c183060c3870e1c183060c3c1c3c0cd8b362c187060c18307fc1878183060c183061c3870e1c000000000000555555555500060d987060c7930e3c38f360c18b362cd8b1e4c0e6c5af460c183061d1b32e1cfb33e1cb87262c580000000000000002aaaaaaaaaaa80507075540c38307503a81d541e5e0f89d40e0750381d072a80002203faaaaac0e075513aa4f555274e3c3831f001000aaab541c1831f5555550015527aa20f7f0a0000000000003f9010aaaaaaaaaa0155401c182d507060d5d507060c7d50702aaaaa8000283dfc2aaaaa03f805070805555555555555aaa81d555541c1831f5544ea0755555543ea0f43e27555555070800000200082003faaaaaaaaaaaaaaaa80557f0703a0703a8fd3ea3f1fa8fd45c38f0e3e27554010aaab5503aaa838383afaaa8183061c183aa4f541000aaaab55552faaaaaaabf87060c3d50040000011fc0001555555555402aaaa4f541c1830f5541ffd5550040000011fc000155555555540283830e0ea80383aa55aaaaaaa8383061ea800383061eaa83ff0e0555555fe028955555555555560748c18381a38bc7e3f170e0c18f8787839381c2eaa3707058000000002aaaaaaaaaaa80557f0703aaa838f0e3e175550050f8780407f0855a81d7f0e0e0f55503061c18380283c3eaa0000085585c0ebfd40143e27555003c3831f03080fe1000ab55555555554001c1830f5400141c7800010010000aaaaaaaaaa015555541c1830f5407f0e0c187aaa0e1c38055554004005452aaaaaaaaaaac0e81d541c1831f0f0f07162e075543c0008787078f263c0000000fe0000b1555555555400183060c993260c183065cf9f2e4c7931e6c183166c59b164c59b362c00000000580b003faaaaaaaaaaaa8013264c99b366cd93364c00981b05555555514 23 8388607 10 1023
def hc_68_1 : Nat → Nat := unpackHintV5 0xa199019cf5299615b88ef9c78b0cfb7eef087ba4d277810973acf56d918769acf963ad8059fe6c55c90d4ff5754a357045393f3ff152379218344cd12d21cb2669ae22d0e6217c551f24961b78eb172d1311b55e0df4f007b19103d0f80000f4 0x54555503060c1d541eaaaa0755545e8000a675000010007f00215555555555402a0181000c1830754ac9ab275503aaaaff5545e174ceaaaaaaaa377fa37500aaaaaaaaaaaab5503bfc0ea8183060eaaa1f47aa81d40eaa3f5517a8bd55545ea6750faaaaaa85d5546ea000000000800020800feaaaaaaaaaaaaaaaa000c1830603060c38f0e3c183060cd8b362c7870e1c383060c1830703069e4e7d39f4f0f8183060c1830e1c00000000000000155555555555402a07503aaaaaa01830740c1d550faaaaaaaa83d40040000002aaaaaaaaaaa8003063c183060c39f4f273e1e060c1ff060c18f060c1871e1c783060c183060c1870f234e9d7a74f070ebd1b32ebcfc73ebcb8f1e1c3af0e1c78f263c183060c3c2c59b838b362cd8b1e1c3870e2c000000000000580b003faaaaaaaaaaaaaaaa80555507061c183070381d48e5f52391d541e1f541e000880feaaab541c1831e55555541eaa81d48eaaaaa0f50fa00000000000000055555555555500aaa81d48eaaa8383063caa0f550faaaaaa83d40000400002aaaaaaaaaaa80555503aa8383063e87ffaaa27503aaaaaaa2f555517a83d43eaaaaaaaa83d400000000000104007f55555555555555550091d40eaaaaaa8383063ea1f07aa2aaaaaa83d400400001002aaaaaaaaaaa801f81c1c1831f0f281c2eaa0e1e0e2d7a3060c1835e8e878f263eaa83871e3c387000000000058000002aaaaaaaaaaa80073e0c183067e39f81c3c78f0e0c18faa878fa1ffe7e0c1c0e3bf8fc1c39f3f078f9f3ebe2f1f8fc5e1e1c3c1c78f81c2e838ba162eaa0e1e0e2c000000000000580b003faaaaaaaaaaaaaaaa800302aaa8183060d593564ea82a81dfc0200aaaa2a0080ff5546ea0155555555555560755555503060c1d43e5f5550381d40e47503aaaaa97d44caaa075546ea00008000020800feaaaaaaaaaaaaaaaa000c183060c183061cfd070f40e07540c183060c1c1c3d40c1d07160381d5503a0e0000000000000aaaaaaaaaaaa000c1a30703a3f178fc5c183060e464c7a387c4dfc0381c0c1d542e160023000000155555555555402060e8f878183261c387060c18cd7b35e1e8183060e8183061c3870e0c39327038187060002c1607f555507038183060e271e81c8c18381c0e97cfe5f135ebe264e81d1550b370b02aa467d79fa263d1af5e4c783060c1830600000000000b016007f00005555555555555555000703aa1ffea27555555233f55234723df50f0e1c7c0000002aaa83060c1838183060c1830f073e1c3878183060c1830e1c9870e1c3870e0c1830d8b362c3c0c18381830e1c18700000000000055555555555500060c183060c18326fc983360c1830d8b362c98b362c183468cba33e8cfa32e4c7a3468c98f060c000000000000000155555555555402aaa838f0e3ea07503a81c0ea0703297d45e5f13aaa3700004407f5555aaaa0e3c38fa28370002a8381d50f8f551baaaa5e3d7b31f0010000aaab555500cc1832707aaaaaa0000028a8bd50010007f000021555555555402a958306ae01983064ea9593564ea82aabf804015554540101fe8dd402aaaaaaaaaaad55503aa9983064eaaa1f47aa81d555545ea3f533a89d5155546ea00000080020800feaaaaaaaaaaaaaaaa012faa5e0c193aaaaaabfdfeaaaaaa00008003f9fc3ffffe00aaaaaaaaaa011faa5e0c193aaa81d4beaa8fd54bea275545546ea02a0751faaa3f50fa8bd0000000000104007f0000555555555555555500aaaa064c38f0e3ea07503a8f94bea0703a81c0e5f13aaa3700004407f55555aaaa808e0c193aaaa0f554fcabf850000154000001fc80008555555555500 24 16777215 10 1023
def hc_68_2 : Nat → Nat := unpackHintV5 0xb85308b2ed59adf13fa6e9c29ff5bd9462e58d49c6861dcb7a52f36f2aca6be0d26824ef62b95b5c31a258a8e2526d8f51ac304a69d140428a3c60f838e4df3518f330b11a2ba94225ad7f20415b1b553b15b16911d4f708266c040109000100 0x60c583060c1a33ebcbaf3e8cb83060c183060c1a383a34ebd3ab5e1d1c9d1ab939f567d3c0c183064c38f1e4c38f1e4c7931e003060ff83060c583060cd8b362cda7858b370b362c58f262c99b16000000000f01e007f00555555555555555500065c197060c18b060c183461c3a34e9d1870e8d1a38b97838f0e3c0d83360c18385c2c99b001e0f03faaaa83060c18b164c1871e1c78347178b97467e8bc5d1a32e8fbc5e0601717fcb8b2e6e170b0000055552e0c197260c18f263c98f4e8c183060d3a32f172e5c38b87c0006c183160b2e2c793164cd8b370b0e6e162c00000000000155555555555400387060c1830e8cb83065c3970f070e1e0e0c1870e1c3870e1c39b060c58783870f07160b2e2c3930e1c38700038000000aaaaaaaaaaaa005c1832e5c183060cb97162c5ab660c18306ccbc5cb972e5e2f072e5cba72e5c3978b97260c18f263c98f261c78f261c78f00d83062c59717fcb97162cb97366e162cdc2c58f262c99b16000000000f01e007f005555555555555555003e0c1970e8c183060c3870f070e1c5878383061c3870e1c3870e6c183165c582c3c1c58783870e4c3870e1c00000e01c000155555555555400f83065c983063c98f263d3a3060c1834e8cbc2c59b165e1f0001b060c597160b1e4c593362cbc2c39b858b000007800000002aaaaaaaaaaa801f3e0c183067d99f060cb8b162d5b3060c18366fcf9f0e7e3e7cfc1cf9f3e9cbc7cf9f3e5e260c18f261c78f261c78f263c98f00d83062cb972e5cb8b162cb8bfe6e162cdc2c58f262c99b16000000000f01e007f005555555555555555004e0c1a70e9c183060d3a70f274e1d5a78383063c38f0e3c04e9c183060d3a74e5d39f4e7d397162c58b162c00000da7060c59b362cd8b0e1c59b0e1e162c03870e1cd8b0e1c3800003c07801fc0000001555555555555555402abf8381c1c7871e0e071f8fd47e575550b0207544ea00000555581d55540c18307541eaaaa81dfeaaa81d550000000000000aaaaaaaaaa01038983063e1e4e4e8e060c1c8e2f1f8fc5c58b00081c2cdd502c9c4c5c6c0000000000001555555555554001a3061c383060c183938783830061cb9f3e5c183061c387060c183060c187060cd830f270e07166c986c1830601c0e07f0055555060c1830e7c3970e0c3875e0c3c7cfc1d3af06007370b85807001555578306bc387060c3af0e1c387360c18b362cd8b0e1efe0070e1c1830e1c3870e00000700000000e00007f0382aaaaaaaaa8007060c3d0052b3060d987060c3870e1c3870e0c1870f070e1e0e00001c1830e1c3870e1c0fe0001b060c59b166c58700387bf8700e1c3930e01d555555555555598306cc387060c1830e1c3873e1c3872e1c383060c1870f07661c38783870e2c383061c3870e1c3870e01b060c59b166c5870e6c38783870e1c59b0e4c380700000380700e007f00555555555555555500a077f070307338f9f661d3873e7d38b0085c2c78f4e2cd8b1600cc0fe3c055a8183bf8700a8f9f8183061c183a0e3c3870e2c5c0e061c0038000aa1c18307fc3a70e000c3c7cfc1c0060c38f0e1c38b370b8580703f870001553c0e81c1ea8383061e0e1e0e1c013c0eaa0000e1c58b0000038001c0005555555555006703a0707aa0e0c187838780fe1c1830f070f0700038010385d541c7c1c020e1c0e1d555555555554183661c1830ecc3b30e0c187661d987160001b060c59b166c58f1e3cd87160b362c580000001fc1e0002aaaaaaaaa8003060c183065cf9f2e4c1831e4c7931e003066cd9b362cd8b1e4c9931e00000f01e007f0055555555555500818381c0e060c387261c183060c3d070e1c3d075ebcb9f3e5c3870e1e0f0b0e1c000582c0feaaaa40e060c183899fa0703aa85c2c183060eaa8183060e898f5e1d787263c58b00000000000000055555555555500a81d40caaa0755503060c1c1eaa1f5555555550010000000aaaaaaaaaaaa01540efe0c1d03060c183060cf9f263cf931f133f40c1838183071f8f9f3ebe3f1f3e7cfc5e3e7cfc7e2ebcbc3d7c4c7c0e0742c5d0b17550b370b0000000000001602c00feaaaaaaaaaaaaaaaa01500c1830755555546eaa81d40eaaaaa0f50fa00000000000000055555555555500a8a81d40eaaaa8183060c1d541eaa1f5555551ba800008000055555555555500 24 16777215 10 1023
def hc_68_3 : Nat → Nat := unpackHintV5 0xe24311db39c2d3f1d2cd09bac4a619b7eb2fb0a9d0a5c2baa1a5079b4199960d4d8b42b38748fe8091ae7a3d95785c7874c4e66e998b677dc75d428f56ed954b96d644d1b13e599e36f1da2c5ea528011721b194199a060e52d20749c20001d2 0xc197060c1ff060c197060c183060c183060c19f3e1cf9f3e9cf9f0e7cf9f3e5cb9f3e7cf9f3e5cba72e0c183064c38f1e4c38f1e4c7931e003060c19f3e6c59f362cb9b3e5d39b16ccd8b1e4c9931e000000000f01e007f00555555555555555500060c180c183064c1931e0c183060c183060e060cb87070f8000183060cb972e5c793264d98f4f1b169e362c000000000001555555555554001830603060c183060c18383970e0c1838183060c1830e1c1870e1c383060c1972e5cb8783870f07161c9870e1c3800001c000055555555555500060c180c183060c383060c183060c1878387061e0e5c3c00003060c1972e5cb87661c3870e1e0e1e0e000007000fe0700155555555554001830603001800c183060c1978ba72e5e2ffcbc3c793264c78f060c183263c98f26ac78f263c98ffe003060c1972e5cbab36acda78dab8d8f264c9ab1eaaaaaaaaaaaaa0cb83060c183fe0c197060c183060c183060c1978b974e7cb972f172e5e0e5cb974e5cb872f172e0c183064c7931e4c38f263c7932e1c78f00183060cb972e5cb972e2cbb32e2d3c6c5b38d8b1e4c993663c00000002e003c07801fc015555555555555554001800c183061c3870e00c183060c3ff0006001c3870e03060c00181fc3870e1c0060c1830e1c387566d59b0e1c3870e4c3870e1d55555555555541830e0c183061c3872e1cf870e0c183060c183061d183060c1870e1d3870e1d380c183060c1830e1c38700183060c3870e2c3a70e1d59b566c3a70e1c3870e6c3930e1c38700038000700e007f00555555555555555500a81d40eaaaaa8060c1c0eaa17555503aaaa83d40000000000000aaaaaaaaaaaa000c1a3060c1830e7d197467c3970183060c1830e3c38f060c1830e8cd8b461c5b336ccd8f0e1c78008c00000055555555555500060c192757003060c1973e7cb83a0e2c383a060c1830e0c183066d9a7a171b166e919b1e0f03f802aaa83060c183061d183060c183061d3a70efd3a7061c18306071e1c7800c1874e5d19f4e7d197060c183060c000183060d99b666d3a70e6c39b363c9870e3d1a7362d39b16000000f01e007f000000555555555555555500aa060c1955503a81d555541ea075503aaaaaa800000000000155555555555400183060c193060c184c7931e0c1a3465d19f467d197060c000183060cdbf363c9931e8d19b168cd8b000000000000055555555555500061c197060c197061c383060c1830e1c383060c183060c1830b874e1e0e5c3830e0c1830462d58b83c6c9870000e0703faaaa83a065e070706030642e164c38002a83060c1970e1c1870e0c3c5cbc1d3830038b561c98785c2c038000aaaa1c1830e5c1832e1c00e0c18700000038703c1cbab060cd87561c3870e5cb972e1c3870e0007000fe0007001555555555400b83065c383061c3801c1830e01c3870f07fe001c00383061c0e1c3800703f80ac183365cb972e1c3870e1c3870e1c9870e1c3aaaaaaaaaaaa97060cb87060c1830e1c3970e1c383060c1870e5c3870e1e0e5c3870e7c383061c0e1c3870e1c0560c19b2e5cb970e1c38b0eac3870f070e1e0e6c3930e1c38700000380700e007f005555555555555555000e9c1830e1c383061c3870e7c1833e1c39f0e027060cd870e1c387fe1c3ff0e7cd9f3600070fe7f0fffff80002aaaaaaaaa801f3e0c1974e1d383060c1a74e1cb870e7c39f2e5c383063c38703871e01f4e0c183067cf870e1cb972e5c78f0004e0c19b2e6cf974e9c39b0eccd9b1e4c387663cf9f362cfb3362c000001e03c00fe000000aaaaaaaaaaaaaaaa007c1830e0cf83060c387060c183061cf873e170e9c3878183060c183060c187061c1830600cda316ac5a70e1cd930e0001c0e07f555553e0c1970e0c1870e0070e0c1877e073e1ff8070e00002b060cd97367cb870e1c3ab0e1c3870e000001fc0e007001555555555400383061cf83065c3801c1830e1c00003873e1ff8070e1c1830e1c0fe001c381c0560c19b0e1c3872e6cf970e1c3870e6c3930e1c3875555555555550e1c183060c39f060cb870e7c387060c1830efc3870e5c3870e7c39f0e5c387060c3870e1c3870380ac183361d5870e1c387165cd9f2e1d5870e1c387361c9870e1c38001c0003807003f802aaaaaaaaaaaaaaa8027060d387060c38700e9c18336acdab361ff870ffc380001fcfe1fffff0055555555000e1c1830e9c383061c3870e5c1832e1c3970e027060cd870e1c387261c3870e5cb972e00070fe01fcfe0000aaaaaaaa5d55002e0c1970e9c183060d3a70f172e1cb807060c7871e1c01383069c3aa7cfaaa8f0e1c7a7060cd972e5cba7839b0f1b363c9870ecc7b336ccd800003c07801fc0000ba7060cb970e9c183060d3a70f072e5cb872e1c383063c3871e1c380174e0c183065cb870e1cb9f2e7c78f0004e0c19b2e5cb974f07361e366c7930e1d98f2e5cb8b2eccb8b000000780f003f8000002aaaaaaaaaaaaa5d55500060c183060c183263c98f060c183060c1834f273e9cfa787c00003060cd8b362c793164cd83070b0e0e060c00000000000155555555555400183060c183060c39f0f070e1e060c1830e1c383060c1870e1c3830703060c1c1c38b0183066c59b161c9830e1c381c0000000055555555555500 24 16777215 10 1023
def hc_68_4 : Nat → Nat := unpackHintV5 0xa7758ca0f1a199b1d09591088ef5a787fdbe8488dd784711717db26d710366b9ae60d9785c4d2357613b4d4e8548753642ed623f44ea39e15938586232657d320019309c592ce0ef2bd44328f4b822e584193e6a12b9a10be9b404edbf00013b 0x155540e80a81d55555517aaaa8b87060c7d5543e0f542eaaaaaaaaaaa87c4c000fe404100000000000aaaaaaaaaaaaaaaa005c1832e5c183060cb9700183265c997265cb931e5c98f060cd972e5cb972e5c5972e2c99b260007f0b805c000055555555555500060c180c183060c183060e0e7c1830703060c183061c3830e1c387060c1832e6cf970f070e1e0e2c3930e1c38700000000000055555555555500a8a81d40eaaa8183060eaa0f550faa81d55546ea00000000000055555555555500067c1830603067c183000060c1832e4cf93468c98f464c783060c197367cba3466c5a3362c99b260000000000000aaaaaaaaaaaa000c183060c183060c183061e0000183061c787060c18f1e0c183060c183065cd9f2e9e362d3c6c58f0e1c78000000000002aaaaaaaaaaa8040e060c183071f3f5551f675400e85871e1c7c0eaa83c01101fd55541831e0c183060c183061c39f3e7d39f3e7cf9f0e1cfa3060c1830e7cb973e7c3970018307fc183063c183061cf871e3c3871e4c78f0e3c38f060c1830efcd8b4e1c59f362cf9f362cb9b3e5c7870e3c0000002e05c00fe0000aaaaaaaaaaaaaaaa000c187060c1830e1c3873e0c187060c18307fc1870e0c183060c1830e003060c1870e1c397367cb870e1c3800000000002aaaaaaaaa8055540ea4755541c1831e5507aa85d5555541ea0000000000000555555555555003e0c197de8c183060c3a31e3c000383063c983c9873e3c39f260c19b2e6cf970e6c5b30e2c7870e3c0000000000001555555555554001c0e060c183060c183a000060c183899f9787263d787263c0703aaa162e818385c2c00000000000155555555555400183060c39f3e1c3870e1c3873f1c183060cfc1e0a060c3870e1e070b85c2e802203faaaa83167cb9f2e0c183073397870ebd9af83d000c1871e1c7933e7c98307fc18b060e170b000005555060c583060c183060c1d1f3e7d79f3e7cf9fa3e8c1c0e8fc5e3f1700183060e7e4c7af879f263cf9f263e267e060c1ff81831703071f858ba166c58baa85c2c00000082003f80002aaaaaaaaaaaaaaa80031e7e3f03060c187561d3d27569c3d0b00183fe0c783061c7871e0c1c2e166cf9f3600000aaaa1c383060c187467e07073f41c3d07060c3d5070f40e1741c3d07165541e8380000000000002aaaaaaaaaaa8040eaaaaaaa81dfeaaa81d000c1830755555400000000000aaaaaaaaaa007e072b4703060e470b000060c9c4cfd131eae1f03859b2371fa3e6e170b0000000000000555555555555000740e061e1e1c38f85c2c0154f83067e00183060c183468cb9f3e5d1d23d68e91a3461c98f1e8c3871e2c5c6c58b4742c78f1e2c78b260000000aaab038193068ea3f1f3e8e3e0c9ff15d548ea07540001c1830f5541eaaaaaa200000000000000555555555555008fa3067c183064c5703aa20e8c18347011f3e1c3870f541e27550000000aaaa7e0707060c7c3c3d7d183060c1df4740003c7870e1c38f1f0385d541c1742c5d0b16004000000000000aaaaaaaaaaaa007cf83060c19f3f03809f8307037f1f8f9f3e7e3f1f3e7e2f1f8fc5c383063c3871e3c3871e3e1e1e0e2c5c0e1742c5d0b17550f1f0f0e2c58f164c0082003f80000000002aaaaaaaaaaaaaaa801f3e0c183067cf83065c0060c99f263cf9f263cb933e4c183367cd8b3e7cd8b2e6cf97266c98005c0b801fc000155555555555400060c183060c1931e4c183060c183060e2f03060c183878f000060c1832e6cf971e4c98f4f1b169e362c000000000001555555555554001c0c183060c180c183060c1830703061c3c0c183061c387061c387060c1830f070e1e0e2cb9b3e5c3870e1c000e0000002aaaaaaaaaaa8003060c183060c583060c1b30e1e4f41e8e9d3c7cfc1c7871e00c19f366cfc2e174003c1e07f5555 24 16777215 10 1023
def hc_68_5 : Nat → Nat := unpackHintV5 0xa4a456990ae79680a28df6238b6ca282e2238058a277ce237544a26cba236c481c6ba02a6312245eed095849a9511dcb4d11034675a73f91b933e2ec2fd503291dae251d001ed19319496213e55910b0cd0d34df09150804f90704383000010e 0x1fa07070f03819f27fc56a0033e0e060c1c0c183060c1c0c183060c1c0c183060c183060c1830e5cf873e5c187060c183063c183060c38f0e3c38b160e060c1c0c583060c19b166c58f1e3c78f0e2c58f164c0600c00fe0000000000008355555555555555554011dc386ec183060c78b163c38b0e2cb970e1c38700102e5cb97060c1832eec3972f0c397060c183060c1831e3c7871e1c783060c18f263ff872e3c7872e4dd9bae6c183060cb972e5c3972e2cb87163c3871e00000000000000ee1c3760c183063c58f161c587161c39b3e1c38008073e7e1873e7dd83060c183060c19f2e7cb83060c18f1e3c38f0e3c183060c397261cb8f1e3c98ffeecdd7360c183067c38b0e7cd8b2e6cf971e1c38f000000000000000f0c3bb060c1831e1c38b0e1c393261c38b261c0040b972e5c183060cbbb2e5cbc32e5c183060c183060c58b16ec9c3260c183065c997265cb931e5c98f362cd8b060c183165c5ff2e5c58b2e5cd93166c5800000000000003b0f0c383060c18f0e2c3930e1c387164c3930e00207cf9f867cf9f760c183060c183067cb9f2e0c183062c58b764e193060c1833e4c79f3e4c797267c99b166c583060c1972e5cb97162c59717fc98b362c000000000000003872e4c387770cf9310770e1bb060c1830eee1c30f0ddbb060c183060c1830e5cf873e5c38f0e3c183060c38f0e3c38b166c59b160c183066c59b163c78f1e3c38b163c593000000000000000010775ebbb060c183764eb93060c183264dd9bae6c183060cd9b266c98000000000000cf83060c1832e0c183060c183060c18f060c183264c183060c183160c183066cd93364c0600c00fe0000008355555555555540101c0c183060c180c183060c1c0c1878183060c1830e1c3830e4c3870e0c183061e0e1c3c1c5972e5cb870e1c38000000000002aaaaaaaaaaa80540ea065555540c1830707aa87d55540eaaaaaa00000000000055555555555500060cb80c183065c001830060c183468c98f464c797265c983060c1a3466c5a3362cb972e5c99b260000000000000aaaaaaaaaaaa000e060c183060c387000060c183060c183060c7c03060c3830e3d3c6c5a78d8b060c1832e5cb971e1c38f00000000000055555555555500060c783060c1872e5e2e5c3c0c183060c183061c397465cbc5cba72e1c3c5c0060c1ff060c18f060c1871e1c7870e3c7870e3c783060c1878d8b4f07165cb972e5cb97165d997163c3871e00000007f0b805c000055555555555555550091d40eaaaaaa8383063ea1707aa2aaaaaa83d40000000000000aaaaaaaaaaaa001d183060c1c7465c1832e3c780007060c7872e4c3971e0f271c18336cc38b0e6c5972e5cb8f0e1c780000000000002aaaaaaaaaaa80540e07540015550f83d03060c1d555551555550000000000002aaaaaaaaaaa8040eaaaaaa81d40eaa47517aaa2e003060c1d43e6755550fa3d40eff5555555555500000001fc80800005555555555555555002f0383a3060c1830e1e83870e2e8383061e0e1eaa070ba2a0e2e8387a0f41c000000000000155555555555402460c1c0d5a32f03a16000cc18326ae1f131f132f40e17172f1788bc2e160000000000000aaaaaaaaaaaa0154110381d48e9f52391d5071e1c7c2eaaa87c4c002000005555a0703803838787aaaa467eaa468e478ea061c183aaaaa0ff1000aaab541c1831f55503a918050541ea1f555545555400000000000000aaaaaaaaaaaa01503a91d5500007060c3d07aaaaaaaa880083e000000000002ab2ed555555555402a803870e1e96aaaa0038306aeaa83ffaaa839f8383063eaaa83c1c0aaaaaaa80a25555555555555 24 16777215 10 1023
def hc_68_6 : Nat → Nat := unpackHintV5 0xc982bb61ec4a924c64ca5698b3b84ff15d9e06772feb09511bae8ad5d8b737a12ecfe1dba083a7040740038e40101c480e34411467a038cbc0e18f8202e60e422ce803d0220548960750d00a61101300701b82a02704004003800020 0xd9b30740c1830740c183067e070f163c587060c787161c583a0703162c387367c387060303f8003555551001830e7c183060c183060c1833e0c183060c183060cf83060c1832e0c183063c78f061c183060c18f060c1830e5c9872e3c78f263ff838e0c183060c583060c19f0e2c39f362cb9b3e5c7870e3c0600c00fe00000000008355555555555555554010183060c183060c39fa0e1e81c0ea8183060e0e1e81c0c183a0e1c580e075507bf83a0e1c0000000000001555555555554001830000703a3f178fc5c183060e263d5c3e271e018381838183aa3713170b260000000000000aaaaaaaaaaaa000e000060c183060c1c0c18b8183060e787263e787263cb932e4c183060cdc0c1838183058b2e2c593166c58000000000002aaaaaaaaaaa800030e1c183060c183061e383060c19781c3c387160c387060c1871e1c387270385930e1c5930e0c0607f0006aaaaa301555557faa81d55503aa060c183aaaaa1f5000000000002aaaaaaaaa80000cb8381830703060c183065c1838183060c1830717060c183060c183162c583660c183060c783060c197265c9972e4c797263c18381830703062c583060c18b2e2ff972e2c5972e6c98b362c0600c00fe00000000008355555555555555554010183060c1c0000e162c1830703060c197267c9b30e4c7b30e4c783060c1972e2c582cb8bfe5e060c1c0c193166c58000000000002aaaaaaaaaaa8001f81c0c3c7060c183060c1870e0c183063c38b0e0c387060c1871e4c3870f038587164c3930e0c0607f0006aaaaa2003071f060c183060e060c19f060c183060c183067c1c0c1838183060c58b160d983060c1831e0c183067c98f3e7c98f2e4cf930703060e062c183060cb972e5cb8b162cb8bfe4c59b1603006007f000000000041aaaaaaaaaaaaaaaaa00903000aaaaaa060c183a0f55555555510789800000000000002aaaaaaaaaaa8003060c0e1c38717011f3f03060c187060c38f1e1c387164e0703060000002aaa8c7c9ff3f13260c387071fa60c9ab1ffff9dcc9c0f0e7c98b1e2b4183060c183060c38f0e3c1c0011f3f03061c383060c183060c19b166c58f1e1c582c78b263e060c1c0c180c000000000000015555555555540123e0e81933f40e0e1e071f2e4ffb1f067e071315b038f937693064ffc7c99381cec9ff 23 8388607 10 1023
def hc_68_7 : Nat → Nat := unpackHintV5 0xb19cdcaf14a2ab34f8a740fda2094e9c31769755378ba6ec86c9377aa30a75754b69c6ec64994b58eaec550cf753e849532032527c2951345251000d50482e4c41024469f638c2ea32599a2e091426fdc31ff5c218f5c013815d075f090001d7 0x5540ea2a838383d5540c1800000c383075541e2754100000002aaaad40e2a838383afaaa8183061c183aa4f55000aaab55552faaaaaaa8383061ea80000a0e2c00000023f800000000aaaaaaaaaa01555527aa0e0c187aaa0f5554000041e1600000011fc00000000555555555500aaa81d55555503aaaaa800383061eaa83d07aaaaaaaaa83c4c00008200000000015555555555555554001832e7cf97263c98f263c98f162c59b166c59b166c58f1e3c78f162c58f164c00007930982cd86c5555555555551402f038183060c1d03060c1d03668c78b163c383063c38b0e2e070b2e5c3870e1c3f8301800aaaa003060c1832e0e060c1c0c183060c183060c197460c1c0c183060c1838b8f1e3c183060c187060c183063c7931ffc3971e3c397260c183060e060c1c0c5972e5cb872e5c5970e2c7870e3c0fe0300180000000000aaaaaaaaaaaaaaaa0000c183060d9a30740c1830747e070f163c587060c787161c5c0e161c39b3e1c387f060300155540060c183060c183060c39f060c183060c183060cfa3060c183067c183060c1971e3c783060c1830e0c183060c7872e4c3971e3c7931ffc183060c1bf060c183062cf87161cf9b165cd9f2e3c3871e07f01800c00000000005555555555555555000060c183061c383060c183060c3a32f0387870e2c383061c3870e4e070b261c38b261c3f8301800aaaa003060c1832e0e060c1c0c183060c183060c197460c1c0c183060c1838b8b162c183060c1b3060c183063cb932e4cb97263cb931e0c183060e060c1c0c58b2e2ff972e2c5972e6c98b362c0fe0300180000000000aaaaaaaaaaaaaaaa0007e0703060c1830e8c183060c183061c38f0e2c387060c3930e1c3c0e161c5930e4c387f060300155540060c183060c183060e3e0c183060c1c0c1833e8c183060c19f0703060e162c583060c183660c183060c79f263cf9f263cb933e4c183060c1c0c183818b2e5cb972e2c58b2e2ff93166c581fc060030000000000155555555555555540018306077e1c387061e3e7e060c1830e0c1871e1c387164e07030004602aaac0e7e1c3c0e3e5c9ff23e8c19f81cdb81d6c9ffb640e0e1d18347038f93fe3feaff23068c1b6c28183060c1d030740c3870e0c183ff03074007061c3872838f0e070e1c59355500183060c18381838187060c18307fc1838183060c183061d587560c183060c383060c1871e1c78700183060c1c0c1c0cd8b362c7803c382d55555555555540060c183067c1c0c1838183060c183060c1839183060c1830703060d1872e7c39f2e0c183060c383060c1831e1c7871e1c58b060c1830703060e062cd8b362c78f1e3c787162c78b2607f01800c000000000000055555555555555550000183060c19f060c183065c183060c183060c1831e4c983060c183060c183062cd9b266c981fc06003000000155555555555402a07503aaaaaa01830740c1d550baaaaaaaa83dfea8000000000000155555555555400183000060c1830e7d3974e7c3970183060c183060c38f0e3c983060c187362d38716ccdb3363c39b0e3c980000000000002aaaaaaaaaaa80038000183060c1830703063e060c1830e1c183060c183078f0e3c783060c1cf8d8b9f1b165cb972e3c3871e000000000000aaaaaaaaaaaa000c0060c1830e1c3870e1cbff060c183060c1870e0c183060c1830e3c383060c1870e1c3972e5cb870e2c3870e00000000000aaaaaaaaaa0005e0703a060c183a06cd983060c18f162c787060c787161c583a0703162cb970e1c387060303f8003555551001970703060e060c183060cb830703060c183060e2e0c183060c183063c78f060c383060c183063c783060c18f263ff872e3c7872e4c1c0c183818b060c1832e5cb970e5cb8b2e1c58f0e1c780c01801fc000000000106aaaaaaaaaaaaaaaa80203060c183060000e1e3c1830703060c1872e3c783c98ffe1e060c183060c183060cb9b3e5e3c6c5c78d8b1e1c38f00000000000055555555555500 24 16777215 10 1023
def hc_68_8 : Nat → Nat := unpackHintV5 0xa1c95341e06e82c044ed0629c10652923c245c324628a48539c6f87481d2879b9982e6c51b8d6f06dade00357c1069486cbec4f54aacba8fc164ef0c29cf03d15e901f2ce43de81c7830e8e0e3e188ce41f8c642b54f035e830001af 0x2a0723a8fd47c38785c0cfd47eaa87c4c826ccdcaad48cfd9ea81d5fea6a4187060ea8180c55460f1c0e15b6d1d5070f07aaa8fc0c3871e8e470381d43e0f1f8fd555555554102aaace7683870e1c387aaaaaa0e0715583870e1eaaaaaa9aa8381c0e072222155555655452a83870e1eaaaaaaff7f6fffff87039101ff81ff97f2fe2ab2aaaaa8a55541c3870f41eaaaaaaaaaff7f6fffffd5070394441ff81ff9117f2fe2ab2aaaaacaa8a555540e9f2391d48e9f51f8fd4871e1c7c2eaaa87c4d1a3158413666e55558f9f060c18ae075441d183068e023e7c00000e1c387aa0f13aa15c42b0002015557fe75499f49ff3eaa3c3931715554fab3d552871e1c7d550b76ee563eaaa3c3871f555555543e2754111050072607667b1d91b28aaaa9f5545eaa0e3c38faa0f50baa0755547e1f507aaaaaaaaaa1f13aaaa088828039303b328208d942aaaaaaaaaaaab2aaa287c015ffa3e7c3ab0e7c164131593383805030e1c183060c8f8783830e0547cfc0c18300000187060ea020703064401c005612aaa89f838306fea20e1e838702071faa8000083c1ea02a88803804412aaa8870e0d183060cfa34607060edd40700f870f6e02d910071d941c183aa838720e1c081d41e3e00000783d501544401c021584aaab28c0e838307030f07a0f070e0c183061e839f0e1e800383061e0e1e0e1c3870e1c5800040e1755071f0787800041c3870e1c593000800008020000e00040aaaaaaaaaaaaaaaa00940efe0e060c183060cf870e7d5ab3e1c39f3e7e3e7e0e3c38f16042e17000c003e2b220264aaaa340efe0ea060c183aaaa56ae0e1eaa1e3e0e1e160542ea9d000c8880080992aaa883061d183060c1ab461cbab3e1cfab2e1c1831e1c7871e1c58001b060c59b166c58f1e0003c382c0000000098006c555555555555004 23 8388607 10 1023
def hc_68_9 : Nat → Nat := unpackHintV5 0x81309f7db4df79451c78144c773c3672912b694e5165b4e65ea1c5563e1952090d4f64a94b1d1246c11740ad853c451a37e9173151a62cad2927a94122f52d2118771f706a1c34cf17ed1213911711fc650d39310ce0160b4c6506553e000195 0x5030eb540c383075ffffffffeabfff06033fff55aa060c383aaaaaabfdfdbffffe0c064403fe03fe5fcbf8aaaaaaaa29555541eaaaa8187060eaaabfdfdbfffff55445100ff80ff80c065fcbf8caaaaaaaaaa295540e3e1c1c7e0703261c18300184c4603060c0efc3870f011f3f03060c0000061c1830e3c3870e2c9c0e060c15871580008c0555514740ea4723060e0753f9fc1c383061c7c3c3c1c58baa919f3f40c183060c1870e1c38f1f40e85d543c7c3c38b163c593a060e858b0603200e1007260711800b3642aaaaaaaaaaaaaaa8a5555541eaaaa460c58307555554d5511100c060301910aaab2aaaaaa280c183060c183061c7871e0e000572b3eacfab81830e1c183060c183060cd8b362c787059b8183070306030000560008c00555555555555004460c1a3464c983064c7931e4c7a3468d197467d19f465c183162c98b1e0cd9b060cd8b362cd8b1e2d163c783064c78b060c060fc1e1311a304602c362aaaaaaaaaaa8a5555540ea4750381d48e46d3fa8b870e1c1870707aaaaa0f130e0703901c3879555691d40eaa0e1e0f5556b061c387aaaa80e07038aaaa1c3870f555554b5282d557faaaaa0f0baaa8381c0e1c0e1c888883942aaaaaaaaa8a555555552d557f5a9403870e1eaaaaa0e2e8387039110728880e1c0e1c555555555514aaaa0755553eaaaaa2f51f0e1c387aaa0f41eaaaaaaaaa0f130e07222820e1070a00e1c0e1c83942aaaaaaaaaaaaaaa8a03aa0e0e0f503a81d41e1f555033f0f061c1c0cfd5540c1d5555503060c8060301caaab3faa0e1c387a0f5555555557fbfb7ffffea8381c880ffc0ffc88bf97f15555555554523f55554feaa8fd071e1c7d507a85d40ea3f5545ea0f50faaaaaaaaa1f13aaaa088828039303b323e1411b28555555555555555514aaaa5aa81d40ea8183060e83d55555550789c403019030a0060c060c81942aaaaaaaaaaa8a55555540ea91c8ea3ed540e0752391870e1c387061c1c1eaaaaa83c4c381c0e0703901c3879555556aaaa3eb555523aa0e1c387a0f555555541e27101c0e41c280387038720e50aaaaaaaaaaaa2941c1d5507061c1d5503060c0603956aaaaaa0e0c383060eaa8180c5581c0e0755070707a81d507061c1d55540ca0060c180c074aaaab541c3870f555555fd6a505aaaaaa0f0baaa8381c880e1c0e1c8883942aaaaaaaaa8a555555554a0b555fd683870e1ea0e2eaaaa8387039441c88880e1c0e1c555555555514a0e0e8381c1d507061c1d552a870e1c3d5455553fa0a83d52d070e1c3870e070e1eaa83d55141eaaaaa83c4d55555555555557fca93a0e0e9dab541c187075540c066b76eeaa56aa9fd2aad52d070e1c38756aa83d54ad555550789870381c0e4441c280387038720e51503aaaaaaaaa7f517aa8fd41c3870f41eaa83d5555555541e261c0e5070a208883850070e070e41ca15595555555555555514 24 16777215 10 1023
def hc_68_10 : Nat → Nat := unpackHintV5 0xa5250b9fcd569885d29485009069078971be82f59f7e6d2272e2e36e21306b64af66654061713d5c7d3d57f9215045ed4be91747791c415d873c1d5036bd583261172f3cc9251a892075291ba53417391b12b9200ded3308f93d02819e0000a0 0x9aa81c0ea07555503060c1d5507aaaaaa98180c88818500301910aaaaaaaaaaaa2934a0d95a81d40eaaaaa77543060c183aa263c98fa1755555555543e260c064403019030a0060c060c819440eff5503aaa81c0ea075555540eaaaa060c183075550f83d50baaaaaaaaaaaa1f13060322282061030a0060c060c81942aaaaaab2aaaaaaaaa2950381d555553507060c183aaaaaaaa9a820600c06440301910aaaaaaaaaaaa280eaff0381d542eaaaa060c187161c183060ea87c4eaa070306403060c060395554183a6077f060c1838793aa8183060e8f9f3e7e8183161c183060e0703aa85a2e8183a060c180c806030180c18030600c8555555555555148183061e0f039a060c18381870f0307030747e0f41c38b17070e1e0703aa838f060c060c060320180c20060c818aaaaaaaaaaa2955554d540eaa81d555550f1f540c183075542e88180c0644410030603062aaaaaaaaaa8a540c19f060ea077f81c0c183070381830703060e060c1c5e3f1f8b83061c183060c1831e3c183060e1e4e162c5c0e060e8183162e0703aa878f878b162c78b260c18030600c064030183081803060306030640c555555555555555514a9260c18faaa81d47eaaaaa0f50faaaaa6aaaa060322079309b32561411b2855555555555514a90e0c187aa0e0c187aa0e070f5555154caaaaaaaaab53503aa3f1faaaaa061c1830f5541eaaaaaa60603222838510070e070e41ca15555976aaaaaaaa29521c1830f555548eff55545eaa83c2eaaaaaa83c2ea0603220387038720e5107285555555555514a9aaaaaaa477faaaa2f55543c983063eaaaaa1e3e8583019113328a9940f2613662aaaaaaaaaa8a0302020703aaa95caea575f0e4c78f561c38f85c6e1755543e260c8800880262b08955546aa077f8fd5540e0752391d547eaa2f517aaaa8b93060c7d5550f1f41ea85d5555542eaaaaaa1f130603222820828079309b323650aaaaaaaaaaaaaaaa280c3830f5554b5282d523bfd55550785d555541c381c380c06444441ca1555555555452aaaaa96a91dfd6a50aa0e0c187aaa838baaa0e0c0641ca2222038703871555555555452aaaaaaa07548e47503aaaa0e0c187a0f5541eaaaaaaaaa0f1306032820e111070a00e1c0e1c83942aaaaaaaaaaaaaaa8a03060000e07070f41cfd03060c180070e1070f40e06014155070380c008200000e0042aaaaaaaaaaa80223468d1c0e8fc5e3f170e0c18f0e8c9c3c3d0385c8cdd541d160c0648c03843f0381c1642aaaaaaaaaaa8a555507aaa07540c183075555fefedfffffaa888807fc07fc06032fe5fc555555555514aa9aaa838383d552a0c383075541e27540c8060c180c072aaa83a07503a0703060e9f54f061c183060e1e1e0e2c5d540c1833f40c1a3063c183061c183a0740eaa1e3e1e1c58b1e2c9d031740c18301900c060c20600c180c180c18030600c19031555555555555555452aaa06b03aaaa060c183aaa0f555555541e260c064440c280183018320650aaaaaaaaaaaa295550381ac0eaaaa060c183aaa0f555555541e260c064440c280183018320650aaaaaaaaaaaa280c18307555540efeb5282d555550785d555540c06030603064441040ca1555555555452aaaaaa505aa077f5aaaa838baa060c183aaa0f440c060322208018301831555555555450180c1d55550540ea06b03aaaa060c060c183060c1d5507a281d55555550789aaaaaaaaaaaaaa8356aaaa9556a06b03aaaa0ea83060c1d550795aaaaaaaa0f1306030180c88818500306030640ca281d555555548ea070381d555541c183060eaa83d5555555541e2740c2880180c88818500306030640ca19555555555555555514aaaa061c183aaa6aa8806030180c885555555514 24 16777215 10 1023
def hc_68_11 : Nat → Nat := unpackHintV5 0xe4760bdc6604d7b52ccb1329c2ca12b5ef37aeb1cfa6a204a1b13c9b998694fda78dd5ca8502357dedc5756e206d2612682d3e5b6f3052ee204613373ef9c636ea04303dab2961b72239ca1f30c2188da914610b14280e0f1944048aa4000122 0x2e5cb97065c1972e5c197160c18b168c183268d1931e8c98f2e4cb93366c183362cd9b060cd9b160d165c593166c5830188d182302e170980b0d8aaaaaaaaaaaa280e1e3c183263cb8717172e5e2e0c197260c78f060c7c83063c98f263cdc2c59b8587360c18b4597163c593169d38274e00c06170b83c260b0d8aaaaaaaaaaaa280c02f178183060c3970e5e93974e1e858b006071e1c7c2e165c5ff2e2cb9b062300026aaaa23c78f2e0c1972e5cbc5cb978ba3060c1832e5cb872e8cb978b974e5cb878b8b162c1831ffc1831e3c183064c7931e4c38f1e4c38f1e6c183166e162cdc2c58b2e2ff972e2c5972e6c78b262c180c46cc198170b85cb81701e130586c5555555555555555140703060c183060c183060c183818317030683261c7c4c38f1e4c7931e0c183066e060c1c0c1a2c597162c78b262c180c060c0183006030180c0603155555555555450183060cb8381830703060c183065c1838183060c1830717060c183060c183162c583064c183060c1831ffc98f263c9871e3c9871e3c1c0c183818b060c183165c5ff2e5c58b2e5cd8f164c5830600c18030180c06030600c18030180c062aaaaaaaaaaaaaaa8a070e0c183061d197060cb871e1e0e1c3c1c1830e1e0000e1c387360c18b0f070e1e0e2c165c587261c3870e000700000380b00555555555555000e8e3830e0e3a32e5cb971e3c38b0e3c98b0e3c38f0e5c9872e3c38f266c59b164c987161cd8b168b2e2c7930e1cd8b00e01c0b85c0e070586c55555555555514063cbc5e060c1830eac3a7a69d3ab4e1d9871600307fc18f060c38f0e3e170b03600170b81b55552e0c1970e8c183060c3870f00007060c3870e1c3870e1cd83062c165c58007803870e1c000000000000155555555555400b83065d5a3060c183a68c58b000060c997265c9d3263d5931e6c183160b2e2c00d9b0262cd8b000b8005c0000362aaaaaaaaaaa80172e5cb972e0cb832e5c58b164c997265c9972e4c797263cd8b362c59717fcb97162cb97364c59b1605c2e172e05c0980b0d8aaaaaaaaaaaa287c1832e1e060c383061c987260e0e7c3870f070e0c3830e4c3ff0e1c3870e1c39b060c597168b0f03061e0e0c3870e1c180c0e07038700e1c038703870381c555555555555514060c18307000038f9f060c1c0c183065c99f26ac3931eac3931e0c183065c582cdc0c1838183262cd8b01800008c0056002aaaaaaaaaaa8021f3e0c19f2e7cf9f060c58b362cb83460c983264cb933e4d1a3263d1931e6cd83066c597168b2e5c183365c583262cd8b06030b87c468c118131982c362aaaaaaaaaaa8a1f060cb931e0c183878f2f0b166c5979063c18f1e4c7931e0c18f89831e3cd83062cb8b45978587370b163c593160c06170f89d38274e03c260b0d8aaaaaaaaaaaa280c0060c1830f49cfa73f41cf873f1f858b006071e1c7c2e165cb97165c5ff06230f8ac0009aaaa88f1e3cf9f060c1833e8cf878f9f4e7cf9f8f9f0e7d19f060cb9f3e5e3e7cbc2c58b060c7ff060c78f060c1930e3c7930e3c7931e4c79b060c59b858b370b165cb972e5c58b165c5ff1e2c98b060311b306607d981f3e05c3e0f0982c362aaaaaaaaaaaaaaa8a03060c1838183060c183070b160c183818306831e4c7931e4c38f89871e3c183060cb8b168b165e060c1c0c18f164c5830180c06030600c18030180c062aaaaaaaaaaa8a03060c1838f83060c1830703060cf83060c183060c1833e0e060c1c0c183062c58b060c983060c183063ff930e3c7930e3c7931e4c78381830703160c183065cb972e5c58b165c5ff1e2c98b060c01830060301830060c0180c06030180c5555555555555555143e0c1970e8c183060c3870f070e1c9878383061c3870e1c003c06c183165c582c3c1c58783870e4c3870e1c00000e000700155555555555400f973e5e3a30e0e3830e8c78f0e2c98b0e3c38f0e3c38f261cf8f0e7c99b166c597168b0e5c58b264c38b1e4c387362c0b87c0e01c0381c161b155555555555450387060c1830e8cf83065c39f0000e0c1870e1c3870e1c39b060c5878000b8b05870e1c38001c260000001cfe00002aaaaaaaaaaa8053460c18306ad19f060cb8b16000cc18326ac98f664c797267c99b060c5972e0005c582c98b362c003e001f02600006c555555555555003e7cf833e0cf9f2e7cb8b162c9933e4c79f3e4c797267c99b166c5972e5cb97162c59717fc98b362c0f81f3e05c3e130161b155555555555452a0723aa85d55547cf8f0e1c7d50f89d5104d9ab1586e5555681d13060c7c3c9c8cb83075540c19f0743c78b0e4c38f1f0385d542d1742c5d0b160c0641f0784c9eac27ab01642aaaaaaaaaaa8a540ea2ed5503aaa8383061e83d55555554c0c0641c28220381c8855555555555514564e000180c18306ae95ab56ae95e32e7cf970e3c38f162e170b1e3c78b1e2c9830f81f562b0000155546a81dfc183a060c1c8c18381a3471f8f9f3f1f8f9f3e7e2f1f3e7e3f172e4c1831e4c38f1e4c38f1f0f270b162e070ba162e858baa878f878b162c78b260c061f3e07c20f8100f2613059b2155555555555555545206d40c1830755503a81d555541ea0755554d55540c064403019030a08855555555555514 24 16777215 10 1023
def hc_68_12 : Nat → Nat := unpackHintV5 0xd2d1caca5220c4657bbe358cba090bb32db7ac05caa6bd52a001af995da98f4a85880dcf7fe20b7b7d197858c971cda36b01b36072a457ca2a518d8f4e58cd499d2f430da43c71a733e2242f59222895b12191c116e6ab0f31ed0716070001c5 0x183060c183000071f3e0c1838183060c38f07870e0c183060c183060c197367cbab8d8b571b163c3871e0300001180000ac5555555555550043e7c1833e4cf9f3e0c18f1e4c793064c983064c7931e8f264c183264c783460cd83366cb9b3e5d1a3362d19b163c9931e0c06170f88d182301e130d91c55555555555514568c183060d5a33f038f9fa366e8383063c387162c3871e2e1e5038580505541c3c1c580100000010aaaaaaaaaaaa00cd1c0d983919f8fd0f85c3e164c7931f13162c99385c3da170b8f9ba371fa164e262c2066107c1e130590aaaaaaaaaaaa29503a91d5500007060c3c1c0028aaaaaaaa0020d8000000047f001555555555554003a3060c183568cf83065c78f0000e0c18f0e4c00038f07c7060cdab0e2c39b165cd9f2e3c3871e001f000f8004c0d802aaaaaaaaaaa801f3e7c19f067cf973e5c78f1e4c7931e4cb93265c78f1e4c7ff366cf9b167cf9b165cd9f2e3c9931e07c0f9f02e1f0784c360aaaaaaaaaaaa290baaa96a9183062d563eb2a8c1832751397d553326cc9c0eff555555546ea8180ca0978442f1784c5e4442e91d5548eaa2f0ba81d547ea460c193a89cbeaaaa1f3fa81dfeaaaaaaaaaaaa06032825e111412f0262f2215555555555595555514a85c0eaa2f0baa8fd5547eaa4750f8fd23060c9d44e5f555555503bfd55555555411f006032825e1104c5e442aaaaaaaaaaaaaaa8a03062c583064c58f1e3c78b162d79fa5e7e91c0e91cbe5f23a89a3060c793a0e8c78fa1e4e1e4ea162e858b060c5ff818b1703075542e85af5e0bd780301923046bc21783c260b21555555555555555450183060c183060c39f0f070e1e060c1830f00003060c1870e1c383818307071603060cd8b362c393061c3870380000001c05802aaaaaaaaaaa8003061c583064c5b33e1cb873eccba3060d187464c3a3060c7930e3c38f260c38b060c58b4183166c59b163c9870e6c58700e00c063300e070586c55555555555514a85c0eaaaaaaaa1f07a260c18f6aaaaa6aaaaaa095803019103c26442aaaaaaaaaaa8a03aa8183060ea838795abaa021e1e02603bfd555004404d55561755555548ea075523a8bd5517a8983063ea1f07aa1ffeaa89c0eff55555555555030194104450403c26442aaaaaaaaaaaaaaa8a1f81c6c583060c18b1743c7931f44c1831f0f6aa261c78f418b858baaa161e858b85c2c180c83e2f560bd580f0982c855555555555514162c59f3e0c183067d1d073e7d79f3e7c39fa3e8cfc0e8fc5e3f171e3c793060c7c1c78f261e1f550f1f43ff83062ffc0c58b8183a162e858baa85c2c180c9f83f03f1c0f9f083e0f0982c8555555555555555514060c00018316000e072f3f4acfd48e5f2f9183060c1afa64c7ab5e4c7c8c99346be27137f03060ffc0c18b00a08183aa85c2c06004108c00000000215555555555555554010183000060c1830e1c3c1cf878183060c3870e1c3870e03060c003c06c59b161c387061c580000000000002aaaaaaaaaaa800302a81c0ea753a95caeaa0e3c38f87ffa8984550320009555441800c183067c387567d59f0e1e39f8e7e3f0f1e1c7871f50f87ff0885c2c1907c560012aaa883060000c183074cfab2eacfd32e0c183074c98f564c7932603060c001830362cd8b262cd8b018008c000000362aaaaaaaaaaa8020b162d183068d19f2e7d197460c193464c7931e4c983062ff83062c583060cd8b362c98b362c180c460004c0586c55555555555514060c183060c183060c1830e7d3974e7c397060c183060c183061c7871e0c1a0c39b162c9930e2cd8b362c7930e1cd8b060301830060c0180c0600c0180c55555555555514a81d40eaaaaa8183060e0f550361f5535555555503019030a08806032215555555555545281d5555555503a81d45e07503aaa0f550f060c183a1ffeaa89d55503bfd555555540c280180c88a08180301910aaaaaaaaaaaaaaaa280e0703060c183060c1d0f1e0c1d03060c1c3c7b0faa060c1838183418baaa161e858b85c2c180c806030600c18030180c855555555555514060c183061cfd030740c183067c183060c183060e3f0381c5c1c0e1e3c7830f0381831e0c18307550f1f43ffc0cdc0c183060c5ffa162e858baa85c2c1830818030180c180306100c06030190aaaaaaaaaaaaaaaa280c183067c183060c197060c183060c183060c783060c193260c19b060c183060c5ff362cd8b262cd8b060c0183006030180c06030180c555555555555140f03060c187265c1832e1c18781830f070e0c187261c3870e1c9870e1cd83062c3c0c18783834597161c3870e0c06070e01c38070381c0e07038aaaaaaaaaaaa280e000060c183060c1c0c1978183060d587263d587263cb932e4c183060cdc0c18381830597164c59b160300118005c0000555555555555004 24 16777215 10 1023
def hc_68_13 : Nat → Nat := unpackHintV5 0xdbbdedd72526cfe9cfc79216c1199ebaf589b469a3ae6581aa90f5a40da19cadd8937e4c86ab3579c7396d1f2a670d8460c19355feb1522cf44b9da44501a73e51ac369ded322d1c2b19c522ee0b1cc98916859112b0f50c15a704edca00013b 0x60c183067c183060c1832ffc183060c1831e0c183065c99f260c183060c18b060c1832e6cf97266c9830600c18030180c06030180c062aaaaaaaaaaa8a54c8ea07555541c1831f5550b83d55555541ea0603222825601c981d9910aaaaaaaaaaaa280c1830183060c183060c1c1c783060e060c1830e1c1870f00003060c1972e5cb8783870f07161c9870e1c3800001c000e06c0155555555555400b8306873e0c183064c983063c7871e4c187460c18f261cb8f0e3c9872e4d183066cb972e5d987161cd8b1e4c3871e0c06170b81c0380726070d91c5555555555555142f0343a3060c1830e1e83870e2e8383061e0e1eaa070baaa0e2e8387a0f41c180c80e070e01c38070381c39071555555555554501c0c060c183060c183a162c183a060c18389979587263d587263e0703aaa000859b998b0000202600010aaaaaaaaaaaa005e06c7c183819b370385c2e068c18327132f3387c4c7c8c1c2cdc5ea2f172f0b370b060320b8cc202633059b215555555555554501830603060001e000060c183061c3870e1c383060c1972e5cb87838b0f070e1c3870e0000000000000aaaaaaaaaaaa015103000a000060c183aaa87c1eaaaaaaaa000000000000055555555555500060c180c180003060000c183065c997277c98f564c783060c1972e5cbab362d59b164cd93018005c002e000002aaaaaaaaaaa802172e0c183065ff973e5c183068c183265c997265cb931e5c98f460c19b2e5cb972e5cb8b2e5c593364c180c2e170b9702e04c0d82aaaaaaaaaaa8a0f1e3cb83065c39752e5c3c8c1831eaa7cfa87541831ffc1831e3c183061c7871e1d98f0e3c9a3060cd878d9b4707365cb972eccdb3363c3871e0c06074601d38170b89c4e070386c4e0f1e3cba3060cb970e1cba32e5c3878b931e0c183063c7973e5cf870e1c1831ffc1831e3c183061c38f0e1c783063c787063c7a3060cd878d9b4707365cb972e5cb97165d997163c3871e0c06074601d38170b85cb8174e01c0e1b138aaaaaaaaaaa97555554501831e3c183263cb972e5c78f1e1c3873e7c1832e8c3873e7cb970e1cba30e0c78f060c78f060c7ff060c78f060c1870e3c3871e7d99b167cf9b168c183361d19b368d387365cd9f2e3c3871e7d381f3e00c06074601d38170f81c0e1b138aaaaaaaaaaaaaaaa283c783060c1931e3c78f162c58b460c1a34e7d3974e7d3970e8d1c8d38781831ffc1831e3c3831e3c183162c183061c7871e6d183062cd870e1c387918b161c38b366c59b163c3870e1c5830189d38274e01d18074e09c4e070382c362aaaaaaaaaaaaaaa8a03060c183060c18381c9cfd273f403060c183060c183162e1e1e81c0e8002aa0e1e0e2c0080007800042aaaaaaaaaaa8043c18381931e8e0747e2f1f8ba0c18f260e1703162e1e4e9183859b919baa8593898b06031384100f0982c855555555555514060c0001830e000c183061c3872e1cf870e1c3874e1d3870e0c183fe0c1830e000c1803060c3870e1c183060c3870e2c3a70e1c3870e6c3a70e1d99b666c3870e1c06000700e2300000000e002aaaaaaaaaaaaaaa80240c002aaaaa8060c18041c2aaaaaaaaa8380000000000002aaaaaaaaaaa8003060000c183061cfa72e9cf872e03060c0018300e3c38f060c1830e6c5a70e2cd9b1e1c38f018008c000026002aaaaaaaaaaa8020f1e3d183068d19f2e7d197060c7ff060c78f060c1931e4c7a3060cda3362cd8b366c793263c180c460003c261b0555555555555148183060c1c0e3f178fc5c1c0e898b164c9c2c18341c3c9d030703070307550b271317030060c0180c806030180c2055555555555514060c1833e0c183060cb83060c183064c183060c1831ffc98f263c183060c183160c183066cd8f264c7830600c18030180c06030180c062aaaaaaaaaaa8a540ea2f5555544c1831f07aa81b55546eaaaaaa0603256141103c26442aaaaaaaaaaa8a038000183060c1830703065e060c1830e1c183060c18307871e0c18306ae362d5c6c5972e5cb8f0e1c780c0046001700001555555555554010b972e4c197065cb93064c783063c793260c1931e4c983064c98f068f263d183066d1a3362d19b165cb972e3c9931e0c06234608c0b85c1e130d82aaaaaaaaaaa8a1781cad183060c1ab4742c5971741c1831e0f0f070e3c5870e2c5c0e17554001070f07160000403c0002155555555555400bc5e91b30703668e1f0b85c3c98f263d1e4e264e1713162e170b8bd45e2e5e164e262c20b8cc201e130590aaaaaaaaaaaa295523a81d500007060c3950041c2aaaaaaa0000000000000555555555555002e0c197568c183060c3a31e3c000383063c1e1c780072600c19b2e5cb970e6c5ab0e2c7870e3c002e00170009800aaaaaaaaaaaa005cb972e5cb832e0cb971e3c7931e4c78f263ff932e3c7932e4cd9b2e5cb972e5cb8b2e5c58f264c78170b85cb81701e130d82aaaaaaaaaaa8a55540ea8dc6eaaa8983063e9a0f5503aaa377faaaaa8180c88958500f0991b28555555555555514 24 16777215 10 1023
def hc_68_14 : Nat → Nat := unpackHintV5 0xf1fa31c826f750afee3e98bbc6adb6086168e8ca4decf98ef33b006761ddc8c3372125a63209ad67d0caa419b5f82aaa30334884352c58001a9 0x48ea074d555541c1831f50b83d5555555541ea0603282561101c0e442aaaaaaaaaaa8a03060c183060c180c183060c1c0c1878183060c387000061c387060c1830f070e1e0e2cb9b3e5c3870e1c000e00000700155555555555400397060c183264d060cb93061c783063c787460c18f261cf930e3c9873e3d183066d987161cd8b2e6cf971e1c38f06030380702e1f0381c360aaaaaaaaaaaa281d183060c1870ec0e0e1e839fa0e0c187aa0e1e81c2e838ba0e1eaa83d070603038700e1c20381c0e072155555555555450183060c183060c81c0c1d030740c18306ac3931eac3931f133f40e074001550b8580100000010aaaaaaaaaaaa0117060e066cbb03a070b81c2d183064e3c3e263e267e9183859b8f9ba371fa170b06032984107c2602c855555555555514060c000060c180073e00c183061c3870e1c3830e4c183060c3c1c58783872e6cf970e1c3870000000000000555555555555008180015005003060c1d43e0f5555555555500000000000002aaaaaaaaaaa80030600003060c001830060c183c64c7ab263cb933e4c183060d59b16acd8b2e6cf97266c980c003e001f00001555555555554010b972e0c197fe0c1972e0c183460c1933e7c98f3e4c797267c9a3060cd9f3e6c59f362cb9b3e5c99b260c061f3e07c0b87c2606c1555555555554526a07503aaaaa060c183aaa85c0eaaaaaaa0f50301911410300603221555555555554501a0c183060c183060c1872e3c7871e4c983060c183061cb8f0e3c983060c183060cb972e5d387161cd8b1e1c38f06030180c060c0183006030180c5555555555551406838183060c183060e83870e2e8183060e0e1eaa0703aaa0e2e8183a0741c180c806030600c18030180c8555555555555140683a060c1c0c1838bc2e1717060c183899797c3e263e060e060e2f517818385c2c180c8060306103006030190aaaaaaaaaaaa280d060d41a5d5060c1832e4cb93ae4dd93060c1832e5cb97ae6dd9b266c9830180c06030180c06030180c197fe0c183060c183065c183060c197265c983060c783060c183060cb972e5c183062c183064cd9306030180c060c0183006030180c555555541aaaaaa2903aa81d5555340eaa160c183075555555507aa061400c06440301910aaaaaaaaaaaa280c183060c183061cf8f1e4c9871e0c1a0c183060c183060c1871e4c39f1e1cd8b4e1c583060c197367cb8f261c38f060c0183006030180c0600c0180c555555555555514060c183060c1830e7e8387a073540c18307070f5030741c5c0e075540e83830600c180301900c06030190aaaaaaaaaaaa2903060c18381c7e171b85839a263d7c3c183060e267e818381838183a371fa166e17030060c0180c806030180c20555555555555514 23 8388607 10 1023
def nh_68 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_68_14 (Nat.sub p 448)) (hc_68_13 (Nat.sub p 416)) (Nat.blt p 448)) (Bool.rec (hc_68_12 (Nat.sub p 384)) (hc_68_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 416)) (Bool.rec (Bool.rec (hc_68_10 (Nat.sub p 320)) (hc_68_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (hc_68_8 (Nat.sub p 256)) (hc_68_7 (Nat.sub p 224)) (Nat.blt p 256)) (Nat.blt p 288)) (Nat.blt p 352)) (Bool.rec (Bool.rec (Bool.rec (hc_68_6 (Nat.sub p 192)) (hc_68_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (hc_68_4 (Nat.sub p 128)) (hc_68_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (hc_68_2 (Nat.sub p 64)) (hc_68_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_68_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 224)
def f_68 : Nat → Nat × Nat := unpackForestF 0xe8a5de895de5355e735de715de5255e5b5de5a5de515500c5fe424de2345e334de2245e204400c5be1265dfb6de0365dfa6d00c57de24dde14ddab45dcb4ddc94ddaa45db34ddb24dda94500c53d9844d5c5bd5c57d5a57d795dd5a55d5957d625dd595500b5fd4a6d00b57d3255d3155d0c6ed214dd0a45d124dd094500b4fcf245cf145ccd62ce155cca5dcd255cc95d00b47cb844c445bc4457c4357c996dc4355c8464c8145c434fc7568c4347c4157c4b5dc4b4fc4b47c415500a5fc136dc2c7cc134fc1d70c134700a57bfb55bf955ba46ebe464be165ba36fbd47cba367bc15dba345bab6fbab4dba14500a4fb8b45b8945b3d62b7568b7165b3b6fb6570b3b67b5145b3b5db4355b395d00a47b0c69b0c68b0c64b1461b09657d56faec58aec54ae8547d56babc7cabc71abc70abb7caba7c7d567a8458aa14ca8454a8354a8254a81557d563a6b64a6a647d46fa59557d46ea457ca435e7d46ba0d7ca0d70a0b7ca0a7ca097ca087c7d4679ed609eb6d9eb6c9cd749cb679c9379c9357d4639b5699b1357d46298d7e98c7298b5498a547d45f9757a9756c7d45b906789067290670946709436c9047a9036c9026c9236a9016c90d6790b6a9006c7d45786e7e8d4658d3468d3448d14586d728b5628b5608b35c86d6486b7e89d72869358726b87a5c8782487263868347d45385d7881e7f8493681d7281d6a8267e8237e8203481d627d14f8056f805637d14d7dd727dc727db5c7da5c7d14700a377c24573b4f7b25d73b477a34573a4f7935d73a47744617445b76d7076834744537545a754527414e7414c73a370095f72a5558b6d70c7c70b7c70a4558b4f6f5706f25d58b476e35558a6d6c47c6c3456c27c58a4f6ad706ab5d58a475f47c5f47164b5f6846c64b5b6706c64b576635c654646503464b535f47063d805f45b5fd805fb8c61c705fb7c60470602705f8345f45358a375e1355923f5d14d592375c2355913f5b24d5913759b4b59b43591275886c0095757355572554f46e564644f36f5525d4f345544644f26f5335d4f2454fd7e4fc724fc584fc545046e4f94c4f2370094f4db454da4541d624c5684c26541b6f4ab6e4aa4541b5d48d6848b6548b5d41a6f46b6f46b4546a6e41a5d45c584267244b7c424734246c43572424614246041a37009473fc683fc643fa652356f3d4583d4543d3543d154235633c1642346f3b2552346e3a2352346339235234623657e37b543647236354361542345f3556c2345b336723336c3316c234573235c3156431034234532fc682fc642326f2d57e2d4722d4582d4542325f2bc6c2bc60232572324f29d6f29a6e2324d26d7226c7226b5c273622695c2324723d6f23c6323b6323a3e2394e23235009372146521368213640156f1eb581eb541ea541e954015631d3681d3640146f1b57e1b3581b3540145f19b6c19b6001457189640136f17b550136e16a56013631545f15246013621257e13a541237212254121540135f1146c0135b0f6720f26c0f16c013570e25c0d4640d024013530134b0b56f0b46e0134a08572083720825c08a620815c0134704d6f04c6304b4e04a4e054620494e0134601d6f01c6301a6301a390194e01246009270003f 9 11
def ch_68 : Nat → Bool := dagCheckNodeV5 fullMask g_68 ep_68 5 31 bds_68 467 (dagTraceF fullMask rootStock 11 f_68) cur_68 nh_68
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 fullMask g_68 ep_68 5 31 467 bds_68 (dagTraceF fullMask rootStock 11 f_68) (cur_68 0) (nh_68 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_0 : treeBlockF 0 32 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_1 : treeBlockF 32 64 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_2 : treeBlockF 64 96 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_3 : treeBlockF 96 128 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_4 : treeBlockF 128 160 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_5 : treeBlockF 160 192 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_6 : treeBlockF 192 224 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_7 : treeBlockF 224 256 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_8 : treeBlockF 256 288 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_9 : treeBlockF 288 320 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_10 : treeBlockF 320 352 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_11 : treeBlockF 352 384 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_12 : treeBlockF 384 416 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_13 : treeBlockF 416 448 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_14 : treeBlockF 448 467 ch_68 = true := by decide +kernel
theorem nj_68_1 : ∀ i, 0 ≤ i → i < 64 → ch_68 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_68_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_68_1 h1 h2)
theorem nj_68_2 : ∀ i, 0 ≤ i → i < 96 → ch_68 i = true := block_join nj_68_1 (fun _ h1 h2 => treeBlockF_at nb_68_2 h1 h2)
theorem nj_68_3 : ∀ i, 0 ≤ i → i < 128 → ch_68 i = true := block_join nj_68_2 (fun _ h1 h2 => treeBlockF_at nb_68_3 h1 h2)
theorem nj_68_4 : ∀ i, 0 ≤ i → i < 160 → ch_68 i = true := block_join nj_68_3 (fun _ h1 h2 => treeBlockF_at nb_68_4 h1 h2)
theorem nj_68_5 : ∀ i, 0 ≤ i → i < 192 → ch_68 i = true := block_join nj_68_4 (fun _ h1 h2 => treeBlockF_at nb_68_5 h1 h2)
theorem nj_68_6 : ∀ i, 0 ≤ i → i < 224 → ch_68 i = true := block_join nj_68_5 (fun _ h1 h2 => treeBlockF_at nb_68_6 h1 h2)
theorem nj_68_7 : ∀ i, 0 ≤ i → i < 256 → ch_68 i = true := block_join nj_68_6 (fun _ h1 h2 => treeBlockF_at nb_68_7 h1 h2)
theorem nj_68_8 : ∀ i, 0 ≤ i → i < 288 → ch_68 i = true := block_join nj_68_7 (fun _ h1 h2 => treeBlockF_at nb_68_8 h1 h2)
theorem nj_68_9 : ∀ i, 0 ≤ i → i < 320 → ch_68 i = true := block_join nj_68_8 (fun _ h1 h2 => treeBlockF_at nb_68_9 h1 h2)
theorem nj_68_10 : ∀ i, 0 ≤ i → i < 352 → ch_68 i = true := block_join nj_68_9 (fun _ h1 h2 => treeBlockF_at nb_68_10 h1 h2)
theorem nj_68_11 : ∀ i, 0 ≤ i → i < 384 → ch_68 i = true := block_join nj_68_10 (fun _ h1 h2 => treeBlockF_at nb_68_11 h1 h2)
theorem nj_68_12 : ∀ i, 0 ≤ i → i < 416 → ch_68 i = true := block_join nj_68_11 (fun _ h1 h2 => treeBlockF_at nb_68_12 h1 h2)
theorem nj_68_13 : ∀ i, 0 ≤ i → i < 448 → ch_68 i = true := block_join nj_68_12 (fun _ h1 h2 => treeBlockF_at nb_68_13 h1 h2)
theorem nj_68_14 : ∀ i, 0 ≤ i → i < 467 → ch_68 i = true := block_join nj_68_13 (fun _ h1 h2 => treeBlockF_at nb_68_14 h1 h2)
theorem nc_68 : ∀ i, 0 ≤ i → i < 467 → ch_68 i = true := nj_68_14
theorem lb_68 : LowerBin fullMask rootStock g_68 12 :=
  lowerDagV5 (kn_cons lb_67 (kn_cons lb_65 (kn_cons lb_45 (kn_cons lb_36 (kn_cons lb_54 (kn_cons lb_21 (kn_cons lb_25 (kn_cons lb_62 (kn_cons lb_64 (kn_cons lb_61 (kn_cons lb_63 (kn_cons lb_60 (kn_cons lb_19 (kn_cons lb_38 (kn_cons lb_14 (kn_cons lb_8 (kn_cons lb_58 (kn_cons lb_66 (kn_cons lb_7 (kn_cons lb_2 (kn_cons lb_12 (kn_cons lb_52 (kn_cons lb_55 (kn_cons lb_51 (kn_cons lb_32 (kn_cons lb_20 (kn_cons lb_40 (kn_cons lb_35 (kn_cons lb_49 (kn_cons lb_56 (kn_cons lb_33 (kn_cons lb_44 (kn_cons lb_41 (kn_cons lb_46 (kn_nil))))))))))))))))))))))))))))))))))) rc_68 nc_68 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.and, [5, 9]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.or, [8, 14]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.or, [11, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3936935936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 3936935936)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 3936935936) = g_68 by decide]
  exact lb_68

end PEqualNP.Outside.L_meta_48581

theorem PEqualNP.Outside.L_meta_48581 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3936935936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3936935936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48581.table2_from_lowerBin (4276676744 * 2 ^ 32 + 3936935936) 13 PEqualNP.Outside.L_meta_48581.root_lb PEqualNP.Outside.L_meta_48581.wg 18 rfl PEqualNP.Outside.L_meta_48581.wfits PEqualNP.Outside.L_meta_48581.weval
