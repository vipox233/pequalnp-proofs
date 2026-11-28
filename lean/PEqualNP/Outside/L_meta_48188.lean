import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48188

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

def m_0 : Nat := 0xaaaa
def s_0 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_0 : Nat := 0x22a
def ep_0 : Nat := 0x28000000000000020800000000000002200000000000000000
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

def m_1 : Nat := 0xc0c0c0c00000000
def s_1 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_1 : Nat := 0x4040c00000000
def ep_1 : Nat := 0x408000000000004000800000000000000000000000000000000000000000004040000000000
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

def m_2 : Nat := 0xcc00cc00000000
def s_2 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_2 : Nat := 0x4004c00000000
def ep_2 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000000000
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

def m_3 : Nat := 0xcccc0000
def s_3 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_3 : Nat := 0x44c0000
def ep_3 : Nat := 0x480000000000000408000000000000000000000000000004400000
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

def m_4 : Nat := 0x4444444400000000
def s_4 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_4 : Nat := 0x4044400000000
def ep_4 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_5 : Nat := 0x222200002222
def s_5 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_5 : Nat := 0x200000222
def ep_5 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000000000000000
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

def m_6 : Nat := 0x202020202020202
def s_6 : List Nat := [0x2000200020002, 0x20200000202, 0x2020202]
def g_6 : Nat := 0x200020202
def ep_6 : Nat := 0x2020000000002000002000000000200020000000000000000000000000000000000000000000000000000
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

def m_7 : Nat := 0x4040404040404040
def s_7 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_7 : Nat := 0x4000404040
def ep_7 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_8 : Nat := 0x22002200220022
def s_8 : List Nat := [0x2000200020002, 0x2200000022, 0x220022]
def g_8 : Nat := 0x200020022
def ep_8 : Nat := 0x2002000000002000000200000000000000000000000020002000000000000000000000000000000000000
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

def m_9 : Nat := 0x4400440044004400
def s_9 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_9 : Nat := 0x40004004400
def ep_9 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
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

def m_10 : Nat := 0x22222222
def s_10 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_10 : Nat := 0x20222
def ep_10 : Nat := 0x2200000000000020020000000000002020000000000000000000000000000000000
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

def m_11 : Nat := 0xcccc00000000
def s_11 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_11 : Nat := 0x44c00000000
def ep_11 : Nat := 0x4800000000000004080000000000000000000000000000044000000000
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

def m_12 : Nat := 0x4444000044440000
def s_12 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_12 : Nat := 0x4000004440000
def ep_12 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_13 : Nat := 0xc0c00000c0c0000
def s_13 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_13 : Nat := 0x40000040c0000
def ep_13 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
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

def m_14 : Nat := 0xcc000000cc0000
def s_14 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_14 : Nat := 0x40000004c0000
def ep_14 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
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

def m_15 : Nat := 0xcccc00000000cccc
def s_15 : List Nat := [0x4444000000004444, 0xc0c000000000c0c, 0xcc0000000000cc, 0xcccc]
def g_15 : Nat := 0x400000000444c
def ep_15 : Nat := 0x4000000000008000400000000000800000000000000000004000000004440
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def nh_15 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_15 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 7 (dagTraceF m_15 s_15 4 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 7 bds_15 (dagTraceF m_15 s_15 4 f_15) (cur_15 0) (nh_15 0) s_15 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 7 ch_15 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 7 → ch_15 i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0xff0000000000ff00
def s_16 : List Nat := [0x5500000000005500, 0x3300000000003300, 0xf00000000000f00, 0xff00]
def g_16 : Nat := 0x1100000000005700
def ep_16 : Nat := 0x20011000000000002001100000000005400
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xb162c4a910604072e0701 0x4cc2060c1831654e9e6cb2e491106442200f 7 127 3 7 9 511 13 8191
def nh_16 : Nat → Nat := unpackHintV5 0xb89702e0582b0150a24440804f082e002 0x0 11 2047 5 31
def f_16 : Nat → Nat × Nat := unpackForestF 0xcea26103019b306065c322316086442200f 4 9
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 11 (dagTraceF m_16 s_16 4 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 11 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) (nh_16 0) s_16 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 11 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 11 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xff0000000000ff
def s_17 : List Nat := [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff]
def g_17 : Nat := 0x1500000000007f
def ep_17 : Nat := 0x400000000000800100000000000200015000000000040
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def nh_17 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_17 : Nat → Nat × Nat := unpackForestF 0x32db2432a32632532400f 3 9
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 7 (dagTraceF m_17 s_17 4 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 7 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) (nh_17 0) s_17 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 7 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 7 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0xf0f000000000f0f0
def s_18 : List Nat := [0x5050000000005050, 0x3030000000003030, 0xf00000000000f0, 0xf0f0]
def g_18 : Nat := 0x1010000000005070
def ep_18 : Nat := 0x20000000000000000010100000000000201010000000005040
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xb162c4a910604072e0701 0x4cc2060c1831654e9e6cb2e491106442200f 7 127 3 7 9 511 13 8191
def nh_18 : Nat → Nat := unpackHintV5 0xb89702e0582b0150a24440804f082e002 0x0 11 2047 5 31
def f_18 : Nat → Nat × Nat := unpackForestF 0xcea26103019b306065c322316086442200f 4 9
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 11 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 11 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 11 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 11 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xf0f000000000f0f
def s_19 : List Nat := [0x505000000000505, 0x303000000000303, 0xf00000000000f, 0xf0f]
def g_19 : Nat := 0x10500000000070f
def ep_19 : Nat := 0x4000000000008000000000000000001000000000002000105000000000400
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def nh_19 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_19 : Nat → Nat × Nat := unpackForestF 0x32db2432a32632532400f 3 9
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 7 (dagTraceF m_19 s_19 4 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 7 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) (nh_19 0) s_19 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 7 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 7 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xaaaa00000000aaaa
def s_20 : List Nat := [0x2222000000002222, 0xa0a000000000a0a, 0xaa0000000000aa, 0xaaaa]
def g_20 : Nat := 0x22a
def ep_20 : Nat := 0x28000000000000020800000000000002200000000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def nh_20 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xffff00000000
def s_21 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_21 : Nat := 0x155f00000000
def ep_21 : Nat := 0x4a000000000000040a0000000000001000000000000000155000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def nh_21 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xaa00aa00aa00aa
def s_22 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_22 : Nat := 0xa000a002a
def ep_22 : Nat := 0xa00200000000a0000002000000000000000000000000a000a000800000000000000200000000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xff00ff00000000
def s_23 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_23 : Nat := 0x15005f00000000
def ep_23 : Nat := 0x4a0000000000000000000000000004000a0000000000100000000000000015005000000000
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
def g_24 : Nat := 0x105050f00000000
def ep_24 : Nat := 0x40a000000000004000a00000000000000000000000001000000000000000105050000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xcccccccc00000000
def s_25 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_25 : Nat := 0x4044c00000000
def ep_25 : Nat := 0x448000000000004004800000000000404080000000000000000000000000004044000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_11, s_11, 4, g_11), (m_4, s_4, 4, g_4), (m_1, s_1, 4, g_1)]
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
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_11 (kn_cons lb_4 (kn_cons lb_1 (kn_nil))))) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0x33003300330033
def s_26 : List Nat := [0x11001100110011, 0x3000300030003, 0x3300000033, 0x330033]
def g_26 : Nat := 0x11001300130033
def ep_26 : Nat := 0x2002000000002000000200000000000000000000000020002000000000000000000000011001000100000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xcc00cc00cc00cc
def s_27 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_27 : Nat := 0x4004c004c004c
def ep_27 : Nat := 0x48000000000048000000000000000000000000000400080008000800000000000000000004004000400040
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xcccc0000cccc0000
def s_28 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_28 : Nat := 0x40000044c0000
def ep_28 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_3, s_3, 4, g_3), (m_12, s_12, 4, g_12), (m_13, s_13, 4, g_13)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_28 : Nat → Nat := fun p => Bool.rec (hc_28_1 (Nat.sub p 32)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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
  lowerDagV5 (kn_cons lb_14 (kn_cons lb_3 (kn_cons lb_12 (kn_cons lb_13 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xff000000ff00
def s_29 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_29 : Nat := 0x150000005700
def ep_29 : Nat := 0x420000000000000000000000000000000000000004000000020000001000000002000000150000005400
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_29_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_29_0 p) (Nat.blt p 32)
def hc_29_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_29_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_29_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_29 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_29_2 (Nat.sub p 64)) (hc_29_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 64 (dagTraceF m_29 s_29 5 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 64 bds_29 (dagTraceF m_29 s_29 5 f_29) (cur_29 0) (nh_29 0) s_29 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 ch_29 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 64 ch_29 = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 64 → ch_29 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 64 → ch_29 i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 6 :=
  lowerDagV5 (kn_nil) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xf0f00000f0f0
def s_30 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_30 : Nat := 0x105000005070
def ep_30 : Nat := 0x402000000000000000000000004000000020000000000000000000001000000000200000105000005040
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_30_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_30_0 p) (Nat.blt p 32)
def hc_30_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_30_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_30_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_30 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_30_2 (Nat.sub p 64)) (hc_30_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 64 (dagTraceF m_30 s_30 5 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 64 bds_30 (dagTraceF m_30 s_30 5 f_30) (cur_30 0) (nh_30 0) s_30 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 64 ch_30 = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 64 → ch_30 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 64 → ch_30 i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 6 :=
  lowerDagV5 (kn_nil) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xf0f00000f0f0000
def s_31 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_31 : Nat := 0x1050000050f0000
def ep_31 : Nat := 0x40a0000000000000000000000040000000a0000000000000000000001000000000000000105000005000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x333300003333
def s_32 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_32 : Nat := 0x111300001333
def ep_32 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000111000001000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xf000f000f000f00
def s_33 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_33 : Nat := 0x100050005000700
def ep_33 : Nat := 0x400020000000400000002000000000000000000000000000000000001000000000002000100050005000400
def bds_33 : List (Nat × List Nat × Nat × Nat) := []
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_33_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_33_0 p) (Nat.blt p 32)
def hc_33_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_33_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_33_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_33 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_33_2 (Nat.sub p 64)) (hc_33_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_33 : Nat → Bool := dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 64 (dagTraceF m_33 s_33 5 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 64 bds_33 (dagTraceF m_33 s_33 5 f_33) (cur_33 0) (nh_33 0) s_33 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 ch_33 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 64 ch_33 = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 64 → ch_33 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 64 → ch_33 i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 6 :=
  lowerDagV5 (kn_nil) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5555555500000000
def s_34 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_34 : Nat := 0x1115155500000000
def ep_34 : Nat := 0x440000000000004004000000000000404000000000011101000000000000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xffff
def s_35 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_35 : Nat := 0x577f
def ep_35 : Nat := 0x28000000000000020800000000000002200000000000005440
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xff00ff00
def s_36 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_36 : Nat := 0x15005700
def ep_36 : Nat := 0x42000000000000000000000000000400020000000000100002000000000015005400
def bds_36 : List (Nat × List Nat × Nat × Nat) := []
def cc_36_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_36_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_36 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_36_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_36_0 p) (Nat.blt p 32)
def hc_36_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_36_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_36_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_36 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_36_2 (Nat.sub p 64)) (hc_36_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_36_0 p) (Nat.blt p 32)
def f_36 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_36 : Nat → Bool := dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 64 (dagTraceF m_36 s_36 5 f_36) cur_36 nh_36
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 64 bds_36 (dagTraceF m_36 s_36 5 f_36) (cur_36 0) (nh_36 0) s_36 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 ch_36 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 64 ch_36 = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 64 → ch_36 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 64 → ch_36 i = true := nj_36_1
theorem lb_36 : LowerBin m_36 s_36 g_36 6 :=
  lowerDagV5 (kn_nil) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xf0f0f0f0
def s_37 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_37 : Nat := 0x10505070
def ep_37 : Nat := 0x40200000000000400020000000000000000000000000100000200000000010505040
def bds_37 : List (Nat × List Nat × Nat × Nat) := []
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_37 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_37_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_37_0 p) (Nat.blt p 32)
def hc_37_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_37_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_37_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_37 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_37_2 (Nat.sub p 64)) (hc_37_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_37_0 p) (Nat.blt p 32)
def f_37 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_37 : Nat → Bool := dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 64 (dagTraceF m_37 s_37 5 f_37) cur_37 nh_37
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 64 bds_37 (dagTraceF m_37 s_37 5 f_37) (cur_37 0) (nh_37 0) s_37 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_0 : treeBlockF 0 32 ch_37 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_1 : treeBlockF 32 64 ch_37 = true := by decide +kernel
theorem nj_37_1 : ∀ i, 0 ≤ i → i < 64 → ch_37 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_37_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_37_1 h1 h2)
theorem nc_37 : ∀ i, 0 ≤ i → i < 64 → ch_37 i = true := nj_37_1
theorem lb_37 : LowerBin m_37 s_37 g_37 6 :=
  lowerDagV5 (kn_nil) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0x33333333
def s_38 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_38 : Nat := 0x11131333
def ep_38 : Nat := 0x2200000000000020020000000000002020000000000000000000000000011101000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xf000f000f000f0
def s_39 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_39 : Nat := 0x10005000500070
def ep_39 : Nat := 0x40002000000040000000200000000000000000000000000000000000100000000000200010005000500040
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

def m_40 : Nat := 0x5500550055005500
def s_40 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_40 : Nat := 0x1100150015005500
def ep_40 : Nat := 0x400400000000400000040000000000000000000000004000400000011001000100000000000000000000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xff000000ff0000
def s_41 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_41 : Nat := 0x150000005f0000
def ep_41 : Nat := 0x4a00000000000000000000000000000000000000040000000a000000100000000000000015000000500000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0x5050a0a05050a0a0
def s_42 : List Nat := [0xa0a00000a0a0, 0x1010202010102020, 0x5000a0005000a0, 0x5050a0a0]
def g_42 : Nat := 0x1010000010500020
def ep_42 : Nat := 0x40002000000000000000000000000000400020000000000000000010100000100000200000000000000000
def bds_42 : List (Nat × List Nat × Nat × Nat) := []
def cur_42 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2ca1cc2e82962242122000f 7 127 3 7 9 511 12 4095
def nh_42 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_42 : Nat → Nat × Nat := unpackForestF 0x1bab86931184c00f 3 6
def ch_42 : Nat → Bool := dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 7 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 7 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42 : treeBlockF 0 7 ch_42 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 7 → ch_42 i = true := fun _ h1 h2 => treeBlockF_at nb_42 h1 h2
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_nil) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0x5500aa005500aa00
def s_43 : List Nat := [0xaa000000aa00, 0x1100220011002200, 0x5000a0005000a00, 0x5500aa00]
def g_43 : Nat := 0x1100000015000200
def ep_43 : Nat := 0x400020000000000000000000000000000000000000000000400020011000000100002000000000000000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := []
def cur_43 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2ca1cc2e82962242122000f 7 127 3 7 9 511 12 4095
def nh_43 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_43 : Nat → Nat × Nat := unpackForestF 0x1bab86931184c00f 3 6
def ch_43 : Nat → Bool := dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 7 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 7 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43 : treeBlockF 0 7 ch_43 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 7 → ch_43 i = true := fun _ h1 h2 => treeBlockF_at nb_43 h1 h2
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_nil) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0x5500aa005500aa
def s_44 : List Nat := [0xaa000000aa, 0x11002200110022, 0x5000a0005000a, 0x5500aa]
def g_44 : Nat := 0x15000a0055002a
def ep_44 : Nat := 0x400020000000000000000000000000000000000004000a0000000800100000000000200000000000000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := []
def cur_44 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e342090d34206263d88d592a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_44 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_44 : Nat → Nat × Nat := unpackForestF 0xc7a635f1a14a8a4c42a49a206084c00f 3 10
def ch_44 : Nat → Bool := dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 10 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 10 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44 : treeBlockF 0 10 ch_44 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 10 → ch_44 i = true := fun _ h1 h2 => treeBlockF_at nb_44 h1 h2
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_nil) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0x4444444444444444
def s_45 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_45 : Nat := 0x4044404444444
def ep_45 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_12, s_12, 4, g_12), (m_9, s_9, 4, g_9), (m_7, s_7, 4, g_7)]
def cc_45_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_45_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_45 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_45_1 (Nat.sub p 32)) (cc_45_0 p) (Nat.blt p 32)
def hc_45_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_45_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_45 : Nat → Nat := fun p => Bool.rec (hc_45_1 (Nat.sub p 32)) (hc_45_0 p) (Nat.blt p 32)
def f_45 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_45 : Nat → Bool := dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45 nh_45
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 43 bds_45 (dagTraceF m_45 s_45 6 f_45) (cur_45 0) (nh_45 0) s_45 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 ch_45 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 43 ch_45 = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 43 → ch_45 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 43 → ch_45 i = true := nj_45_1
theorem lb_45 : LowerBin m_45 s_45 g_45 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_12 (kn_cons lb_9 (kn_cons lb_7 (kn_nil))))) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0x5050a0a05050a0a
def s_46 : List Nat := [0xa0a00000a0a, 0x101020201010202, 0x5000a0005000a, 0x5050a0a]
def g_46 : Nat := 0x105000a0505020a
def ep_46 : Nat := 0x400020000000000000000000004000a00000008000000000000000001000000000002000000000000000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := []
def cur_46 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e342090d34206263d88d592a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_46 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_46 : Nat → Nat × Nat := unpackForestF 0xc7a635f1a14a8a4c42a49a206084c00f 3 10
def ch_46 : Nat → Bool := dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 10 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 10 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46 : treeBlockF 0 10 ch_46 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 10 → ch_46 i = true := fun _ h1 h2 => treeBlockF_at nb_46 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_nil) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0x50505050a0a0a0a0
def s_47 : List Nat := [0xa0a0a0a0, 0x1010101020202020, 0x50005000a000a0, 0x50500000a0a0]
def g_47 : Nat := 0x1010105000000020
def ep_47 : Nat := 0x40000000200000004000000020000000000000000010101000000000200000000000000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
def cur_47 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def nh_47 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_47 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 7 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 7 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47 : treeBlockF 0 7 ch_47 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 7 → ch_47 i = true := fun _ h1 h2 => treeBlockF_at nb_47 h1 h2
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0x55005500aa00aa00
def s_48 : List Nat := [0xaa00aa00, 0x1100110022002200, 0x50005000a000a00, 0x55000000aa00]
def g_48 : Nat := 0x1100150000000200
def ep_48 : Nat := 0x400000002000000000000000000000004000000020011001000000002000000000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
def cur_48 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def nh_48 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_48 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_48 : Nat → Bool := dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 7 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 7 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48 : treeBlockF 0 7 ch_48 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 7 → ch_48 i = true := fun _ h1 h2 => treeBlockF_at nb_48 h1 h2
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_nil) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0x50505050a0a0a0a
def s_49 : List Nat := [0xa0a0a0a, 0x101010102020202, 0x50005000a000a, 0x50500000a0a]
def g_49 : Nat := 0x1050505000a020a
def ep_49 : Nat := 0x4000000020000040000000a0008000000000000000001000000000002000000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := []
def cur_49 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a19343061234349263d88d5d2a549882a109800f 7 127 3 7 10 1023 14 16383
def nh_49 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_49 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4ce3469210a884c00f 3 10
def ch_49 : Nat → Bool := dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 10 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 10 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49 : treeBlockF 0 10 ch_49 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 10 → ch_49 i = true := fun _ h1 h2 => treeBlockF_at nb_49 h1 h2
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_nil) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0x2222222222222222
def s_50 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_50 : Nat := 0x200020222
def ep_50 : Nat := 0x2022000000002000002200000000200020020000000020002020000000000000000000000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_10, s_10, 4, g_10), (m_6, s_6, 4, g_6), (m_8, s_8, 4, g_8)]
def cc_50_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_50_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_50 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_50_1 (Nat.sub p 32)) (cc_50_0 p) (Nat.blt p 32)
def hc_50_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_50_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_50 : Nat → Nat := fun p => Bool.rec (hc_50_1 (Nat.sub p 32)) (hc_50_0 p) (Nat.blt p 32)
def f_50 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_50 : Nat → Bool := dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 43 (dagTraceF m_50 s_50 6 f_50) cur_50 nh_50
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 43 bds_50 (dagTraceF m_50 s_50 6 f_50) (cur_50 0) (nh_50 0) s_50 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 ch_50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 43 ch_50 = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 43 → ch_50 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 43 → ch_50 i = true := nj_50_1
theorem lb_50 : LowerBin m_50 s_50 g_50 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_10 (kn_cons lb_6 (kn_cons lb_8 (kn_nil))))) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x5a005a005a005a00
def s_51 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]
def g_51 : Nat := 0x1000100010005200
def ep_51 : Nat := 0x420000000000000042000000000000000000000000000000000010001000100002000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
def cur_51 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xbcbcde997251300f 7 127 3 7 5 31 8 255
def nh_51 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_51 : Nat → Nat × Nat := unpackForestF 0x3ebc393231300f 3 5
def ch_51 : Nat → Bool := dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 7 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 7 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51 : treeBlockF 0 7 ch_51 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 7 → ch_51 i = true := fun _ h1 h2 => treeBlockF_at nb_51 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x5a5a00005a5a
def s_52 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_52 : Nat := 0x105a0000525a
def ep_52 : Nat := 0x420000000000000000000000004a00000008000000000000000000001000000002000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0xf2c30a3cd08286342164cf626ad2d592a06842c00f 7 127 3 7 9 511 13 8191
def nh_52 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_52 : Nat → Nat × Nat := unpackForestF 0x33d335f3432d32521a43442c21600f 3 9
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 10 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 10 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 10 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 10 → ch_52 i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_nil) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x5a5a5a5a
def s_53 : List Nat := [0xa0a0a0a, 0x12121212, 0x5a005a, 0x5a5a]
def g_53 : Nat := 0x105a525a
def ep_53 : Nat := 0x420000000000004a0008000000000000000000000000100002000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
def cur_53 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0xf2c30a3cd08286342164cf626ad2d592a06842c00f 7 127 3 7 9 511 13 8191
def nh_53 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_53 : Nat → Nat × Nat := unpackForestF 0x33d335f3432d32521a43442c21600f 3 9
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 10 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 10 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53 : treeBlockF 0 10 ch_53 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 10 → ch_53 i = true := fun _ h1 h2 => treeBlockF_at nb_53 h1 h2
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x5050505050505050
def s_54 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_54 : Nat := 0x1010105010505050
def ep_54 : Nat := 0x40400000000040000040000000004000400000000000000000000010101000100000000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xc0c0c0c0c0c0c0c
def s_55 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_55 : Nat := 0x4040c040c040c
def ep_55 : Nat := 0x408000000000408000000000004000800080008000000000000000000000000000000000004040004000400
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xa0a0a0a0a0a0a0a
def s_56 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_56 : Nat := 0xa000a020a
def ep_56 : Nat := 0xa02000000000a000002000000000a000a0008000000000000000000000000000002000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def nh_56 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 0 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) (nh_56 0) s_56 4 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 0 (dagTraceF m_56 s_56 4 f_56) cur_56 nh_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0x55aa55aa
def s_57 : List Nat := [0xaa00aa, 0x11221122, 0x50a050a, 0x55aa]
def g_57 : Nat := 0x150a552a
def ep_57 : Nat := 0x4020000000000000000000000000040a000800000000100000200000000000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := []
def cur_57 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e342090d34206263d88d592a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_57 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_57 : Nat → Nat × Nat := unpackForestF 0xc7a635f1a14a8a4c42a49a206084c00f 3 10
def ch_57 : Nat → Bool := dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 10 (dagTraceF m_57 s_57 4 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 10 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) (nh_57 0) s_57 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57 : treeBlockF 0 10 ch_57 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 10 → ch_57 i = true := fun _ h1 h2 => treeBlockF_at nb_57 h1 h2
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV5 (kn_nil) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0x55aa000055aa
def s_58 : List Nat := [0xaa000000aa, 0x112200001122, 0x50a0000050a, 0x55aa]
def g_58 : Nat := 0x150a0000552a
def ep_58 : Nat := 0x4020000000000000000000000000000000000000040a0000000800001000000000200000000000000000
def bds_58 : List (Nat × List Nat × Nat × Nat) := []
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e342090d34206263d88d592a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_58 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_58 : Nat → Nat × Nat := unpackForestF 0xc7a635f1a14a8a4c42a49a206084c00f 3 10
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 10 (dagTraceF m_58 s_58 4 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 10 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) (nh_58 0) s_58 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 10 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 10 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV5 (kn_nil) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x303030303030303
def s_59 : List Nat := [0x101010101010101, 0x3000300030003, 0x30300000303, 0x3030303]
def g_59 : Nat := 0x101010301030303
def ep_59 : Nat := 0x2020000000002000002000000000200020000000000000000000000000000000000000101010001000000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def nh_59 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 0 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) (nh_59 0) s_59 4 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 0 (dagTraceF m_59 s_59 4 f_59) cur_59 nh_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0x50a050a050a050a0
def s_60 : List Nat := [0xa000a000a000a0, 0x1020102010201020, 0x50a0000050a0, 0x50a050a0]
def g_60 : Nat := 0x1000100010005020
def ep_60 : Nat := 0x402000000000000040200000000000000000000000000000000010001000100000200000000000000000
def bds_60 : List (Nat × List Nat × Nat × Nat) := []
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xbcbcde997251300f 7 127 3 7 5 31 8 255
def nh_60 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_60 : Nat → Nat × Nat := unpackForestF 0x3ebc393231300f 3 5
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 7 (dagTraceF m_60 s_60 4 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 7 bds_60 (dagTraceF m_60 s_60 4 f_60) (cur_60 0) (nh_60 0) s_60 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 7 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 7 → ch_60 i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 5 :=
  lowerDagV5 (kn_nil) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0x3333333333333333
def s_61 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_61 : Nat := 0x1111111311131333
def ep_61 : Nat := 0x2022000000002000002200000000200020020000000020002020000000000000000001111111011101000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 7, g_50)]
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def nh_61 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 0 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) (nh_61 0) s_61 7 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 0 (dagTraceF m_61 s_61 7 f_61) cur_61 nh_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV5 (kn_cons lb_50 (kn_nil)) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xffff00000000ffff
def s_62 : List Nat := [0x5555000000005555, 0x3333000000003333, 0xf0f000000000f0f, 0xff0000000000ff, 0xffff]
def g_62 : Nat := 0x111500000000577f
def ep_62 : Nat := 0x4000000000028000400000000020811100000000002201115000000005440
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 5, g_35), (m_15, s_15, 5, g_15), (m_16, s_16, 5, g_16), (m_17, s_17, 5, g_17), (m_18, s_18, 5, g_18), (m_19, s_19, 5, g_19), (m_20, s_20, 5, g_20), (m_0, s_0, 4, g_0)]
def cur_62 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb4743b01f 4 15 2 3 10 1023 12 4095
def nh_62 : Nat → Nat := unpackHintV5 0x5bb44d49a0173c0005 0x2bd7ab759d671c3ae5ef3bdcbde77bdef7b97bdcbdef7bdef7bddede65c2f72edef7bdef7bbe73781d6b3c31c377aaceb3a75a38730d1c38bcee5df72f72edcbaee5cf72e3b97af7 18 262143 8 255
def f_62 : Nat → Nat × Nat := unpackForestF 0x1d1e1d81f 1 10
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 3 7 bds_62 3 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 3 7 3 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62 : treeBlockF 0 3 ch_62 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 3 → ch_62 i = true := fun _ h1 h2 => treeBlockF_at nb_62 h1 h2
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_35 (kn_cons lb_15 (kn_cons lb_16 (kn_cons lb_17 (kn_cons lb_18 (kn_cons lb_19 (kn_cons lb_20 (kn_cons lb_0 (kn_nil))))))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xf0f0f0f0f0f0f0f
def s_63 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_63 : Nat := 0x105050f050f070f
def ep_63 : Nat := 0x40a02000000040a000002000004000a000a0008000000000000000001000000000002000105050005000400
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 6, g_33), (m_24, s_24, 5, g_24), (m_31, s_31, 5, g_31), (m_55, s_55, 5, g_55), (m_59, s_59, 5, g_59), (m_56, s_56, 5, g_56), (m_46, s_46, 5, g_46), (m_1, s_1, 4, g_1), (m_6, s_6, 4, g_6)]
def cur_63 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x205d305595d205925a3558856751d447105c01f 6 63 2 3 10 1023 14 16383
def nh_63 : Nat → Nat := unpackHintV5 0xda80a669a60071e971806a8e638e365b006c0000 0x14f39c6778c60000b9756e382f65b9ce33cc6300009f2d5abb4e08dda3b702deb19ce3008702a34265538ce3000005d0e3c00b51a74025 16 65535 7 127
def f_63 : Nat → Nat × Nat := unpackForestF 0x205d151d95d111ca5a2558856105c01f 4 10
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 3 7 bds_63 9 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 3 7 9 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63 : treeBlockF 0 9 ch_63 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 9 → ch_63 i = true := fun _ h1 h2 => treeBlockF_at nb_63 h1 h2
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_cons lb_24 (kn_cons lb_31 (kn_cons lb_55 (kn_cons lb_59 (kn_cons lb_56 (kn_cons lb_46 (kn_cons lb_1 (kn_cons lb_6 (kn_nil)))))))))) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xaaaaaaaaaaaaaaaa
def s_64 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_64 : Nat := 0xa000a022a
def ep_64 : Nat := 0xa02200000000a000002200000000a000a00280000000a000a020800000000000002200000000000000000
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 7, g_50)]
def cur_64 : Nat → List (Nat × Nat) := fun _ => []
def nh_64 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_64 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 1 1 0 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_64 g_64 ep_64 1 1 bds_64 0 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_50 (kn_nil)) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xff00ff00ff00ff
def s_65 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_65 : Nat := 0x15005f005f007f
def ep_65 : Nat := 0x4a00200000004a0000002000000000000000000004000a000a000800100000000000200015005000500040
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 6, g_39), (m_41, s_41, 5, g_41), (m_23, s_23, 5, g_23), (m_27, s_27, 5, g_27), (m_26, s_26, 5, g_26), (m_22, s_22, 5, g_22), (m_44, s_44, 5, g_44), (m_2, s_2, 4, g_2), (m_8, s_8, 4, g_8)]
def cur_65 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x205d305595d205925a3558856751d447105c01f 6 63 2 3 10 1023 14 16383
def nh_65 : Nat → Nat := unpackHintV5 0xda80a669a60071e971806a8e638e365b006c0000 0xaf39c6778c60000b56aed384f9ab9ce33cc6300005eae5d5b8e10edc37682deb19ce3004684c38159538ce3000005a8d3a00ba1c78019 16 65535 7 127
def f_65 : Nat → Nat × Nat := unpackForestF 0x205d151d95d111ca5a2558856105c01f 4 10
def ch_65 : Nat → Bool := dagCheckNodeV5 m_65 g_65 ep_65 3 7 bds_65 9 (dagTraceF m_65 s_65 7 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 3 7 9 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) (nh_65 0) s_65 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65 : treeBlockF 0 9 ch_65 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 9 → ch_65 i = true := fun _ h1 h2 => treeBlockF_at nb_65 h1 h2
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV5 (kn_cons lb_39 (kn_cons lb_41 (kn_cons lb_23 (kn_cons lb_27 (kn_cons lb_26 (kn_cons lb_22 (kn_cons lb_44 (kn_cons lb_2 (kn_cons lb_8 (kn_nil)))))))))) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xffffffff00000000
def s_66 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_66 : Nat := 0x1115155f00000000
def ep_66 : Nat := 0x44a000000000004004a000000000004040a0000000011101000000000001115155000000000
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 7, g_25)]
def cur_66 : Nat → List (Nat × Nat) := fun _ => []
def nh_66 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_66 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 1 1 0 bds_66 (dagTraceF m_66 s_66 7 f_66) (cur_66 0) (nh_66 0) s_66 7 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_66 g_66 ep_66 1 1 bds_66 0 (dagTraceF m_66 s_66 7 f_66) cur_66 nh_66 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_66 : LowerBin m_66 s_66 g_66 8 :=
  lowerDagV5 (kn_cons lb_25 (kn_nil)) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0xffff0000ffff0000
def s_67 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_67 : Nat := 0x11150000155f0000
def ep_67 : Nat := 0x44a0000000000000000000000040000004a000000040000040a000011100000100000001115000015500000
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28)]
def cur_67 : Nat → List (Nat × Nat) := fun _ => []
def nh_67 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_67 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 1 1 0 bds_67 (dagTraceF m_67 s_67 7 f_67) (cur_67 0) (nh_67 0) s_67 7 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_67 g_67 ep_67 1 1 bds_67 0 (dagTraceF m_67 s_67 7 f_67) cur_67 nh_67 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_67 : LowerBin m_67 s_67 g_67 8 :=
  lowerDagV5 (kn_cons lb_28 (kn_nil)) rc_67 nc_67 (by decide +kernel)

def g_68 : Nat := 0x1115155f155f577f
def ep_68 : Nat := 0x44a42200000044a000042200004004a004a00280004040a040a020811101000100002201115155015505440
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 6, g_29), (m_45, s_45, 7, g_45), (m_67, s_67, 8, g_67), (m_65, s_65, 8, g_65), (m_66, s_66, 8, g_66), (m_63, s_63, 8, g_63), (m_39, s_39, 6, g_39), (m_37, s_37, 6, g_37), (m_61, s_61, 8, g_61), (m_28, s_28, 7, g_28), (m_64, s_64, 8, g_64), (m_50, s_50, 7, g_50), (m_25, s_25, 7, g_25), (m_33, s_33, 6, g_33), (m_30, s_30, 6, g_30), (m_35, s_35, 5, g_35), (m_9, s_9, 4, g_9), (m_36, s_36, 6, g_36), (m_0, s_0, 4, g_0), (m_38, s_38, 5, g_38), (m_54, s_54, 5, g_54), (m_32, s_32, 5, g_32), (m_7, s_7, 4, g_7), (m_24, s_24, 5, g_24), (m_26, s_26, 5, g_26), (m_21, s_21, 5, g_21), (m_34, s_34, 5, g_34), (m_22, s_22, 5, g_22), (m_41, s_41, 5, g_41), (m_49, s_49, 5, g_49), (m_46, s_46, 5, g_46), (m_53, s_53, 5, g_53), (m_57, s_57, 5, g_57), (m_43, s_43, 5, g_43), (m_48, s_48, 5, g_48), (m_62, s_62, 8, g_62), (m_51, s_51, 5, g_51), (m_60, s_60, 5, g_60), (m_42, s_42, 5, g_42), (m_47, s_47, 5, g_47), (m_52, s_52, 5, g_52), (m_58, s_58, 5, g_58)]
def cc_68_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xc82e403201900c21e103081801be0df02f81781ba0dd02e81740ba05b0ad81681ac25506a815409c3ce02683340980bd3c0f8001 0xeb400852e040570092480f85c0762a038d901b0680c12b05cb00284ec132c007c6c03836018550112be0815b034ab81654c0a2800cb5f059ab82a97c124ae04a37020ad80e54c058cc01b660da378691ac308ce174630b1b7854dac266ce1236308da7844d2c1e68e0d343018920081380207d71c5fb8a2ddbb15ed28a76735fb29add8cd5ec26a76034faf1a5d70d1eb66875925fab92dd5495ea64a751a4fa7d25d3491e9848747a3fa151dcf08de4f4672495f8f4adc6255e222a70e94f844a5c1e51e05286fe13f7dc9dbd04dddf266ea92f74095b8249db8246d605f6402daf415d590a6aa04f4f825a7411d300869083f4541d9ea0dcdb0666582f2fc1593e09c850463c01f1a80d87005c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_68_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c128a504a094118928a40404800f09e03c0780a2940242480710e0182300600c004a0800080000000000000 0x1fc6e7d159db6e74d5b4d6fcf59f2c6fc519f0457bcdbedb67b2d5e2347869ae12638296e024e7a909e23e728c8301032491b8646a1119a7c645f0b124621f0284c5e110a9245a1915834529f1417c24491387c060f12834 11 2047 5 31 11 2047 18 262143
def cc_68_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0eb1a4a729c25290631885f37c1f07c1d26c9a16097150d404c5213ccf03c069090110040000000 0x2fa68768c0a810280c2e94b26082e27024042d260748c2a250a49029150af602b280a2942997ca45c279782208259649e9f080301e0826d7c945806820965b06020949d24964160c2a56fa359e816f9c5ae61679058e395b8c55c5020b19feae778a9404810100803820 10 1023 4 15 11 2047 18 262143
def cc_68_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94241902318c2306e1b0685a064590605805c57058560581603a0d1304a228073184420882000800 0x3f17c7c2b9071be0633bfb6f7d6cef6d1de8a73c93e6b02aee191d43e39864710f8de171da37ba467726dee0d9db9a3b684e6c07cd609961a3ab3475568ed09c199341fa4019020300c1909d8b820634e02c04185301f240 10 1023 4 15 11 2047 19 524287
def cc_68_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x801f17c1e1745d06c9b0685916057158560509404c530448d4304c0300c02c4380c0210801104001 0x9e089384ee6c2243834990492e53e5812499788f2c9269f246be471608f2d91c9d234b24a16f922d72059e30b1c5824872d53b1ae6a31cc26b954c71490e24274403e8604d0859208be40164 10 1023 4 15 11 2047 19 524287
def cc_68_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x90120230c6084508200be17c0e89d03a06c4d81a0b40642c81902e25c0a89502624c09813024148090101010 0xbd6e176da2d1a05c923b86e16cd82cda05a46eb38ad62da2bca656d7cac6e144932a8a650a4ca829948d4288b15095abeadf7959eea37dbc67b58af64d0ac0b7d716bab2cf5258e9cadd3157a52974651e809ec403d 11 2047 5 31 11 2047 19 524287
def cc_68_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x902408c5b86c1b0685a0681a0681a06819164181601715c0bc2c0b02c0b02c0a1280a0280a02800a 0xdd2d5e6dafc1b1f726beb4c7c08cf7c276f03edc04db29f3489a68134ce269b55bf62b3eba6fd64cfaa95f512769a42d12d79e58f34ad9e12dcc24b8d5f32a37e4c67c84df8e9af1533e2263c34978491f042760026 10 1023 4 15 11 2047 19 524287
def cc_68_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4138a704e09c128a504a0902a41402614c090510a203c4780e09a1302584a0940204400708e014409000800 0x7d25c7f15c7d9627d15a7bb508a56f895678826f86a6785a57842418316f8216b809677f9637e95b7e1577c94d7c12b7b1276f84d7a0347912b788346e834778247693f76024749787296474a7c73d7c721607296c72274719647516f7416b731677116370824 11 2047 5 31 11 2047 20 1048575
def cc_68_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xd06834191c86432190c83e9e0f070b8184c058a85408240200c460289408240200884002 0x8e57c9036f8fb678f26f8ea6b8da678d2638ca3b8c2378b83e8b02689c7088c688524087933874708646084a408536e84b5683c688295c81d7c814707da5c8015c 9 511 4 15 11 2047 20 1048575
def cc_68_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x76dd0741d068da0681a060980601625816041900400f13c0f03c0f03c0e1380d1340c13000c00000 0xa9b4fa934ba7b47a6343a524fa3a47a2a3fa1237a084ea003e9f8269ea379e1379d9279ab409b85c9ac549a0349cb4f9c34b9b34799b439904e9883e9737c94144931449214497d6f96d679636f95b679535794a3969a319396b929639195b2013d91135 10 1023 4 15 11 2047 20 1048575
def cc_68_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x7c5e1781e0780ff3c0f03c0e12ccb02c0b02c083200801886014450140320c021080200080000000 0xaf94faf024bcb4fbc34bbab47b7b43b6a4fb624bb4a47b3243b223fb1a3bb0237aea33ae04ead83ead026ab458ac349aba49aaa37a7340a895ca805ca7454a6834a5844a495ca405ca3034a214ca184c 10 1023 4 15 11 2047 20 1048575
def cc_68_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xf0f83c1c2954824120903cdc2d1683054482401c4e07038148a041188c04220100800400 0xbfd7cbed7cbe370c7c6cc7460c6b61c6261c3237c296dc193bc0137bf12bbd927ba340bb95cbb05cb9834b912bb9454b9b44b892bba454b8034b7044b595cb505cb413fb3824b2834b114cb084c 9 511 4 15 11 2047 20 1048575
def cc_68_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c23084a1080600801f17c1f0749d0741d03bc95204802008020080200620cc300c0210802000800 0xcf124ce824cd834cc04ccb124ca824d5b4fd534bd4347d2343d124fd0a4bcfa47ce243cd23fcca3bcba37ca233c984ec903ec8826c5a37c213bc1137bf92bbe927c5237c493fc4133c5d7cc5570c3c70c257cc157cc0c70 10 1023 4 15 11 2047 20 1048575
def cc_68_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xe870763b0d86865120904822310884420300803c4f070381c0a450281404620088402001 0xdf03bde944cb06adfc6bde463dd94edd13eca06bae86370043dc815dac68d8c68d7368dbb59db259da237d9955d913bd8137d792bd6927d3b40d485cd3c54d3134d2834d1844d005c 9 511 4 15 11 2047 20 1048575
def cc_68_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc198320e40c8190320640c81332604c0981301c5380700d85b0322640c0570ae0544a81502624440c010001 0xeea7cef56fee567eda6fed267eca57ec24eeba42cd06bb2063a285b1e02deb025ea46fe9c67e914ed786fcc86bbf067b18638c84b7c047e8815e7370e6368e2b40e5023e4b70e3b60e2340e2c6ee2456b1062a205ae7d6fe6d67e5c6fe4467e3457e1b42dd13dd686fcb86bbd867b0063a105b9d8578c04b7b047e103de0144 11 2047 5 31 11 2047 20 1048575
def cc_68_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xf41e8316620c41883104ea9c138260cc090520230c4188100a00400784e08c81802c2580a092124048080808 0x10256f80ab3c02dbe006ceffb577f91cbae8c5a20d6b68635282d8800f5fd06afdb6f7e9b3bf24f9b20ded086b60c33ad818cc3076528377e00abeb1c1f38d0f62407c419be11c1ee8c0f5a407b1b73d6d596b0c4a485a7dab7be959df24def7a677b52bbd4905e229ad806f67c35b0019d690c6a385b4f02bbd2134c20565182779c9a3ca0ade4268cf06a799b5bc6d8de229cf093e67035acc18c8a066f0015 11 2047 5 31 11 2047 21 2097151
def cc_68_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x845e3781e0781e06cdb06c19264190640eb380b32c0b02c092240901c8701c016040100040000000 0x21f8b110b4988124c3c8de176810d25c864ae42f152162690e34f86da5c30d1e156870a14e84c9f24613cfd08e6683f29c1bc240561046e7e03729813c14d020c2b9054548249a41cd3e0d69705b47821a1c0e53a0627d01b7c 10 1023 4 15 11 2047 21 2097151
def cc_68_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xf42efa5681a0280a0280a028098a338c19a641906419058d51505404c5123c8f03c0f003c0000000 0x12434f91da5c8ad1e416872014e8fc9f24e13d1d096820473b8219a20fcc70765703726019c7c0563846e8e03b40c1b98c0acad04f1ba378d81fc6a0ce38af91bd708d2384791b23b8c11d3618e530c668de320da8d83b4041b98a0acab04f15b408b92e45a5722a2691482b8a62a454d122805715c5489c9a460d3e2f69716347899a1c4a53a2427c9284f468259fe11ceb0866783f3101d9520dc9506711815 10 1023 4 15 11 2047 21 2097151
def cc_68_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xe03c0351ea0d0390b01600bc3782e0d63a83486809da380700e01a13402a0500a0140188300600c000c00000 0x12aa46979a24ba9ba544ad2aa4c969a24a8972574ad2aa4e95d1a4aa8d2586892b2669512f03804e432d4d306a9deb7ced5ae74acf38563995a24c69be614cf2fa5f9712ecb6972594af29a559492a4825ae262c70a95b820a9bae4b65124ad206b5bc31a9816d330a66982d9401283404e4c8d1273599352cc968de4a0aa8f03b4181b9900acb004f22340918ae4891524346921134 11 2047 5 31 11 2047 21 2097151
def cc_68_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xa80a61a609a69438e359b5615415405024e14c14a14244204204204014004004004003843801141000c20a1062041002 0x9a118501162674613f9589f8aa4fa1627c0a917162868ad042045770c4a885a080095095be83ad740d679eeb1cca8c24b2df2296b8ccb3c5858e1e2bf0c15b840abc1654e7a29ada06f6a035b0c19d750c6aa85f53c2da7a15d360a73c84d1ec0f8dc06c4402e0f0139bda24dcd126c6893aa7c9a91a4d2d126868933b449cd2a4e4562710b136b609ada44d491269291340489be2fcdd16e6c8af33c539912fcc495e6049f2f24d96923cb09166647b2215b8aca9c2e52e0a286d385b5d029a9c12d350860e813991a24ba97257489313449592a4aa952606892a264 12 4095 5 31 11 2047 21 2097151
def cc_68_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xd81b03606c0bcf782e0dc0b81702e05c0b05602c0390700e01c0380700d09a0340680540810e114410c10801 0x29e6a34eb4da70aebda4de9b0ba858371640bd3293a942b149858a5eb7d2d5ae95acf49563a21a74905ae302c70e15b838a9d224d5ab0d6bc86354c2da7214e9006a11813a2cac5141628eadf46d6ba32b3d1358e8847d2396b8bcb1c3656e0d2a7439256a835af018d520b69c053a181284404e6f4602c0179b9184da9005702f414709b1180aa05e6b48134a30 11 2047 5 31 11 2047 21 2097151
def cc_68_21 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0340c4f10c4310a9ea0a4690a42907ade0781e0619805c5612ecb02c0b015850140320c0300c003 0xafe39af935af435aee51a964dae95d71927ae45d2d42718017ade39ad759ad1557ed3b7c937acc554803b440371fc1f1c81b178170b013ac64e79943ac1253cc43abc250a8130a4110a012ab761ab16d7e93b7bd37aac6d47c3b434371f41f1c01b16c1709813aa64e78d43aa1253c043a9c2509013a9755a9349a8a4ea8525a8025 10 1023 4 15 10 1023 20 1048575
def cc_68_22 : Nat → List (Nat × Nat) := unpackCursorV5 0x9e07d17c07c07c07c07c07c07447216a46814ce4c04c04c036b3603603602a62a028126110b100100100046040002000 0xb8761b8261a563fa323ba06379d233b7d6d8093f7d1377712f73527b786d4b43f448373602f2f02719c17a523fa2e3b9fe379ca339f927a4e3fa2a3b9f6379c6339f127b7349b6f48b6b44b6649b6248b5e44a4a3fa263b9ee379c233b5948b5544b5048b4c44b4659b41557512b72d27b3c553282b2e82720c1f1d81b194170d813b3639b31356fd23b2c35274230d0130cc110c812b2661b216d74d2b72127b1c6d3242b2dc272041f1d01b188170c013b1639b11356f123b0c35268230b813a7655b0649 12 4095 5 31 10 1023 20 1048575
def cc_68_23 : Nat → List (Nat × Nat) := unpackCursorV5 0x4d020000000 0xa5e3fa3a3ba12379de338113f7d9377792f73d274bc3f450373682f2f8271a417a5a3fa363ba0e379da33 9 511 4 15 10 1023 20 1048575
def cur_68 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_68_23 (Nat.sub p 736)) (cc_68_22 (Nat.sub p 704)) (Nat.blt p 736)) (cc_68_21 (Nat.sub p 672)) (Nat.blt p 704)) (Bool.rec (Bool.rec (cc_68_20 (Nat.sub p 640)) (cc_68_19 (Nat.sub p 608)) (Nat.blt p 640)) (cc_68_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (cc_68_17 (Nat.sub p 544)) (cc_68_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_68_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (cc_68_14 (Nat.sub p 448)) (cc_68_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_68_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_68_11 (Nat.sub p 352)) (cc_68_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_68_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_68_8 (Nat.sub p 256)) (cc_68_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_68_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_68_5 (Nat.sub p 160)) (cc_68_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_68_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_68_2 (Nat.sub p 64)) (cc_68_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_68_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def hc_68_0 : Nat → Nat := unpackHintV5 0xd2b5c98be662e88bd55f9c69b54291d465a398044488aa803238eca4f1d840438a89869c1e4d2e029a4805348802690004cf80a19ec013318305f11c8a685e92f87620c94a3ab1b864e4207bd380c30d20bd3240005e800000000000 0x6c6c6c6c0c0c0d0340c7c0d031703030342c2c2c2c2c2c2c2c00300c0300c0303030303002c222200ca0aa2200070707070707070703030703030303030307070707070700c0ca000787e66a6a17980eaa80e03aa82ea0ba0a80c2a006c6c6c6c0c0c0c0c0c0c0c0c000000327c0000008001c1c1c1c1c1c1c1c0c0c0c0c0c0c0080021f99a9a85e603a80e800002005c5c5c5c2c3c2c3c2c0c2c3c000000000000001c1c1c1c1c1c1c1c1c1c1c1c0080021f99a85ea17a83ea0ba00000801b1b1b1b0b0f0b0f0b0f0b0f000000331f334cd331f1b46c5c6c5c6d0303aaa0000000000000000070707070707070707070707000000200006c6c6c6c2c3c2c3c2c3c2c3c0000000b01f010106c01700030000000000000007070707070707070707070700001c070200087e66a6a17983ea0ba0000000a08002002c4c2d542c2d42c5d542e7d42c2d542c2d1f102c0c02c0c106c0b02c104c02c4c02c2c13102c2c0b130096aaaa69aa2884e9f9f5555555544440b02c155502c2c2c7315556aa8a2955555555550b5550b9f55540c14111102c0b0414144c44440b02c0195595556aa8a213a7c05503035031751f50f03030313030b030343c6d027c4040000000000000000096aaaa69aa000a7e7d5555544000100001543ddc3c015556a8022954055555542d55135555104009f004000000100000000195595556a802029f27c9f01b0b00c27e09f1b0f003a0c6c6c6c6c2c2c2c2c2c2c2c2c00000300006c6c6c6c0002aaaaa802aa86c6c6c6c0c0c0d0340c7c0d031703030342c2c2c2c2c2c2c2c0000000c00c000000000000300002aaaaaaaaa80029f555555000000027c0410000000555544d50b500000595556a80029f5665551351344c4d00000001027c0000130000146c5c6c5d44c4c4c2c4c2c4c4c00001a5a69aa000a7e96a86c6c6c6c4c4c6c4c6c4c06c1b04c001b06c1304c02aaaaa8a283a7d5555550f5555555555550f0f0f0f5565555aaaa5541d55541c1c1c1c1c1c1c1ea46c6c6c6c2c3c3c2c3c2c3c2c3c3c7c3d0f43c3c3d0f0f0f170f6a0f0f0f0f0f0f0f0f0f0b0b0f0f030f03c0c3caaaaaaa8a8aaa07070707070707070707070707070707070707070701c1c1c1ea805555555555104000100000000000001550755550707070700001b1b1b1b2b2b2b2b1b1b1b1b00000001f0101005c00f002c0000000000000000707070707070707070707070070000700c0006c6c6c6c6c6c6c6c6c6c6c6eaaaaaaa81c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1eaa81e1f99a9a85e6a82eaa80eaa81e 23 8388607 10 1023
def hc_68_1 : Nat → Nat := unpackHintV5 0xcfe99ec71a34c17968bbe166b5f97aaf9998a9618ea219d297ba989261568ab1ec8728e282b11e7d595675a1ee6e01e86382a05ce1a8538a564f092048c1924538e24121063c114434e9ca2ee18227c1c81c62d81402180e6966081196000204 0xb0b50b1f550b0b0f0f102c02c10f03c3c1208221000f550f0b0b0f50f0f503c3c82135070b13070b0b0741c4d01c3c8281c2c1d3c6d1c6c2c3c2c3c3c2c3c3c2c3c3c0f03c0f03c02c08888208003c7c3d0f43c3c3d0f0f0f170f4000f030f030a00a13071307130713070f0f070b130701c3c82a07070f81c1cdc6cdc6c4c4c4c4c4c4c4c4c0000001f0101005c00f002c0000000000004c1c4c1c4c1c4c1c4c1c4c1c0004c00055030340c5d1f50f03031303030343c8d00000000000400c0000001350703030303130341c4d0f071307000003035031f55008d43c0c0c0c0c0c4d1b0f1717400000000001003040000004d41c0c4c0c0c0c0d071343c1c4c1c0000dc6cdc6cac4cac4c6c4cac4c00000130000000000007c0404017003c00b00000004c1c4c1c4c1c4c1c4c1c4c1c004c00000c806c6c4c4c6c4c4c06c04c01f447c45c171b4130b02c4c00c03088888800070713071307130713071307130701c4caa807a07130f55a551b1751b1759542e69690b0b47d47ccc0cac33032b11b1b42c2c2c2e5a2a29a6aaa81d41c1c1c1c0707071070741c1c1c1c1c1c1c1ea82c4c2d542c2d42c5d542e7d42c2d542c2d1f51f0b030b02c0c2c46c6d0b0b0b0b968a8a69aaaa07507070707070707070741c1d0707070707070707aaa0787d56a0b82eaa0baa96a17582ea0ba8aea03aaa079555555555555543c3eaa955543c2c2c3c3c0ccc0f033315556a92916a955541c1c1c1d41c5407070707a95550b9f5555555555513555543c2c2c3d510345555aa4645aa555507070707541d07507070707aaa07135555555583e0fa82e0ba555a59562ba80eaa81e000055005555000000000000705555070707070009555556a82e000015555542c1c1c1d55544c4c4c4d55542c2c2c2e1306295556aaaa139555556a82e8aeaaa55555555550b0baaa555533032b0cc0cac55550b0b0b0b454a5555aaaa54507155541c1c1c1c1c1c1c1ea5555555550b5550b9f55540d15155542c2c2c2d4545a5555aaaa507555070755550707070707070707aaa0759555569555555560baa0b82ea2ba80eaa81e550b5590f0b42c2d56946c5c6c5d56aa43d47d1b0f43c2c2c3c3c0ccc0f0333259a6aa2a2aa81d41d070741c1c1c1c1c1c1c07070701c1c1c1eaa81c4e550b0b550b9f43c2d0b0b0b50f1313175543d47d1b0f43c2c2c3c3c0c3c0f030f259a6aa2a2aa81d41d070741c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1eaa81c4e1f55a5a85d60fa82ea0f83eaa13aaa2ba80eaa81e0558551b1751b1751f50f330b0f0f330b0f0f43c6d854905040300c0304828288488001d41c0c0c00c0c0c41c1d0707070700c0c8201540c0d40c5d47d43c0c0c0c4c0c2c0c0d0f1b449f505500c0300c120a0a21220007507030303070307030341c1d0707070700c0ca000787d56a0380eaa03aa96a17583ea0ba0a80c2a0155555400000155555554cc3cac2cac2ccc3c000000000000000155541c1c1c1c0000000155555449f000040010404013002c0000000000000055550707070700001c07020005555555583ea0ba000080c000282000800000550055550000000000007055550707070700095555560faa000005555544c3c4c3d55540c03111100c030130428444488021395555560faa2a032a0545555555330b0f0f330b0f0f555503030a044440300c050a11112200545055550707070700c0c81015555550b5544d555540d4049f4540300c1141684444880141d5541c1d55541c1c1c1c030328001d655555a5555555583ea0ba0aa0380c2a01547d47d1b1b401000000c0d56946c5c6c5d4cc3cac2cac2ccc3c00000000000000001d41d070741c1c1c1c0000008000551f51f46c6d00127c00000304017004c00b0000000000000001d41d070741c1c1c1c0000701c080021f55a5a85d60fa82e8000000282000801b1b1b1b0b0f0b0f0b0f0b0f031f0340d03030340c0c0c5c0d000c0300c0300b27c0c0c00c0c0c8888882828001c1c1c1c1c1c1c1c1c1c1c1c0c0c0c1c0c1c0c0c030328001c4e1f99a9a85e60fa82ea0380eaa038aea82a030a801b1b1b1b0b0b0b0b0b0b0b0b000002c9f0007c0404017000c000000000000001c1c1c1c1c1c1c1c1c1c1c1c0000701c080021f99a9a85e60ba82e80000002820f000801b1b1b1b00000b0b0b0b0b0b0b0b00000000000707070707070707000070070707070087eaaa85e0aa82e000006c6c6c6c4c4c4c4c4c4c4c4c2c2c2c2c2c2c2c2c0707070300c0300c0300c0320888813082888021faaaa17a13aa82e2a032a1b1b1b1b331f334cd331f1b46c5c6c5c6d0b0b0b0b0b0b0b0b0a8a0300c0300c03030a003208888282888001c1c1c1c1c1c1c1c0c0c0c030300707070700c0c82 24 16777215 10 1023
def hc_68_2 : Nat → Nat := unpackHintV5 0xabd47d562062868974ab18889330cecc969cf02a398816724034e04111ba8183748026e4014d940d1b100635e0106b6018d6a009a5c1e347810687020d0c0099ac1b32b02a648038ae46b10e9381be17c27f3f42ec848314b100018a 0x1540c0d40c5d47d43c0c0c0c4c0c2c0c0d0f23409f101000000401f0000c0000c03005c0400b003c0003000000000000000013507030303070313030341c4d0f07130700080001c3c2c3d5555544000100000000000000155543c3c2ddc2c3c3c0000000155543c1c4c1c0000007a555015555550b5544d5554410027c01000004400401010101002c00f000000000000000001135541d55543c1c4c1c00200007552350f43c5d00000000000000231f55231f00000f0f370b370b0f0f000000001350741c4d0f0713070000a03030380c0c0c0d540c7d5402350f030b03030303031346c3c5c5d004104009f0001007c000300c0003001701002c00f0000c00000000000000004d41c0c4c0c0c0c0c0c1d071343c1c4c1c002000071b9f03517174105c5d00c1b05706c4303039f0350400c213071b9f05d45c5d1b0179f0951713071b07d9f9f11f06c2c03021f44c0e7e7e7e7c07c6c3c00e10781b17846c1e1171b1b1b1b0b0b0b0b0b0b0b0b000000c000000000001f51f1b45c5c6d00000000000013071307130713070b070b070000001e80c0c0e03031b1b03030340d031f0340c5c0c0c0d0b0b0b0b0b0b0b0b0000000300300001007c017010000c030000c002c00b0000000000000000004c1c4c1c4c1c4c1c0c4c0c0c0c0c0c1c2c1c2c1c00200007555555000000000010101004c0130000000000000000555544d50b50000047c00011355551307130700080001d50765551351344c4d00000000100008c04013004c000000000000000147c5c7c5d44c4c4c2c4c2c4c4c00001400004c4d44c1d071344c1c4c1c00200007a51381c1d17546c4d44d131340000000402300001004c0130000000000000005c7d545c5c01313130b130b131300000500001350744c1c4c4d1307130700080001c6e944e07073f1b431b0b0f0b0f0b0f0b0f07c0404017003c000000000000000000004c1c4c1c4c1c4c1c3c1c2c1c04c00002c3c2d542c2d0b1743c40b00b040f04820884003d543c2c2c3d0f0f40f0f2084d41c2c2c1c2c4c1d07134070f20a070b07 23 8388607 10 1023
def hc_68_3 : Nat → Nat := unpackHintV5 0xe6c94edfa9c8d7720ecbb2f0c21268bbd190b509b2ae31b6a2c2dc9db94295c1fe8fa98686c23a8231247bd1987489d26a329661b2205b898a55b9744e61d646121440e14c38ca0631f1b62642ec26100c20c9521911ee1239b6061b08000186 0x5455555555b0b0f0f5b0b0f0f555503030a044440300c050a11112200054555550f07130700c0c40728055555542d5513555550350127d1500c030141844448801655555a5555555583ea0ba0a80c2a51313555070755550f07130700c0c0079f0a006c6c6c6d6c7d6d5b56c7c6d1b171b171b42c2c2c2c2c2c2c2c2a280c0300c0300c0c2800c822220a0a22001307130713071307003030300c0c2c1c2c1c0303201ca1b1b1b1b03030340d031f0340c5c0c0c0d0b0b0b0b0b0b0b0b000c0300c0300c0c0c0c0c00b04c8888282888021f99a9a85e603aaa0380eaa0ba82e82a030a84c1c4c1c4c1c4c1c0c0c4c4c0c0c0c0c0c0c1c1c2c1c2c1c0303001e7c2801b1b1b1b0b0f0b0f0b0f0b0f0f1f0f43d0f0f0f43c3c3c5c3da83c3c3c3c3c3c3c3c3c2c2c3c3c0c3c0f030f2aaaaaaa2a2aa84c1c4c1c4c1c4c1c3c3c1c2c4c1c3c07070f1307070f070f07aa1b1b1b1b2b132b131b131b1300000007c0404017003c00b00000000000000004c1c4c1c4c1c4c1c4c1c4c1c004c000c130001b1b1b1b13131b131b133b3b1b1b1b1b133b13aaaaaaaa87e66a6a179aa0baaa03aa84c1c4c1c4c1c4c1c4c1c4c1c4c1c4c1e81e7eaa84c3c101c1d548c5d48c5d41d42c1d071410b0b47c43f0303f03042302c0b04828288488001d41c1c1e81c1c1e41c1d0707070701c1c820b130b550b0b50b17550b9f50b0b550b0b47c40b0300b03042302c0b04828288488001d41c1c1c1c1c1c1c1c1d070741c1c1c1c0707281e7c07a071f1501c1c2c1c2c070070b0701c140707171070b01c1c2c070ac0300c0704c1ea50545555550b0b0070707155554c0c14c0c111102c0b0141444448801556955541c1c1c1c07072829555555550b5550b9f55540c14111102c0b041416844448801075541d55541c1c1c1c0707281e7c07a50710551051515151070b01c1c2c070ac0300c0704c1ea00005523175231751f50f370b0f0f370b0f0f43c8d0000000000000000000000075070303a0303039070741c1c1c1c000005503035031751f50f03030313030b030343c8d027c404000000000000000007507030303070307030341c1d07070707000079f0007c0400300c00030004017003c00b0000000800005555555f0b0f0f5f0b0f0f55550000000000000000000000555a55550707070700000015555550b5544d5554410027c0100000004800000001075541d55541c1c1c1c0001e7c0040011001010101003c00b00000008271b271b531f5354d531f1b49c5c9c5c6d0b0b0b0b0b0b0b0b00000000000000000000000000070707070707070703030380c0e81c1c1c1c000009c6c9c6c0c0c0d0340c7c0d031703030342c2c2c2c2c2c2c2c0000000c00c0000000000003200000707070707070707030703030303030707070707000079f0007c0404017000c0000c030002c00b00000008271b271b0b0f0b0f0b0f0b0f0f1f0f43d0f0f0f43c3c3c5c3d003c0f03c0f03c0b03c0c03c0c088882082828001c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1e0707a01c1c82271b271b2b2b2b2b1b27271b00000007c0404017003c00b00000000000000001c1c1c1c1c1c1c1c1c1c1c1c01c00200c0006c6c6c6c4c4c4c4c4c4c4c4c0000000401f005c0400b003c0000000000000070707070707070707070707000800289c6c9c6cbcbc6c9c9c6c06c270bc0888888001c1c1c1c1c1c1c1c1c1c1c1c0707281e7c07a071f10740707407071710701c1c2c0700300c0701ea5559f5555550b5544d551103050441301515105510517171517171550fc4c2c0b134f0dc0300c37110506185220001c1d55135541d41d51307130701c4caa807a071b555555544441301111220005540554130f430b430b130f0430343030500555551307130701c4c82a55555555567d0b5544d55550305044441301055105431515151510c4c2c0b13470dc0300c3710505a1111220001c1d44c4d5541c1d55544c1c4c1c07132aa01e81c6d542d42d0b0b47c442302c0b0488488004c3d004c3d48c5c8c5d4142d0b00fc0cfc0c280284d41d071342c1c2c1c071320a81c1c2e07070b130b550b0b50b17550b9f50b0b550b0b47c40b0300b03042302c0b01351131f02c02c2c4c0b00b0b0b0b1131704d40b0b0b0b0b02c2c2c4c1300c030ac4828288488000707135070b0b07070b13070741c4d0b070b0701c4caa807a0700c5555555544440b02c111122000554555500b0b0b0b0b000dcc0c1401555542c1c2c1c07132807281e9555555555550b5550b9f55540c14111102c0b041544144c545454540b0b0b02c2c2c1300c030ac141844448800070744d550755550b070b0701c4caa807a07550b50b42c2d231105c0b02c12212200231f55231f0130f130f4050b42c0430343030a00a1350741c4d0b070b0701c4c82a07070b81c1c2c2d542c7d542c2c4c2d542d550b0b50b9f23102c0c02c0c11b05c5c0b02c04d444c7c0b00b0b0b0b02c02c2c4c44c5c13502c2c2c2c2c0b0b0b1304c0300c2b120a0a21220001c1c4d41c2c4c1c1c2c2c1c1d071342c1c2c1c07132aa01e81c6d547d43d0f23400000000000000000148c5c8c5d43c3cdc2cdc2c3c3c000000004d41d071343c1c4c1c000280c0c0e0303 24 16777215 10 1023
def hc_68_4 : Nat → Nat := unpackHintV5 0x99e16090e24090881687ba347b431e76912c70219c6fa0206989866239d462100a62100061e80a61e80061003a61000061000061000060482e59b9a4516216476a7e4151863dd0e03751a02ef21827b9ce1d3aa017b9601009ec0979a400025e 0x5542d5555154155543c3c01c070744440300c5050111102c0f03780de00555507070707503035500c0c070075550b9f555555555550f511100c03141030111102c0f060500555507070707541d07501c0c0c0c0c1e7c1c01d454545441c3c1c3c07070b070b01d544141c400f07201c2f20303039f227d542c2d542e7c1d0f0b42c2c101c1d48c5c8c5d5401c0740c440300c0300c0c00c0c041f08c40b03c20878001d41d070741c1c1c1c1c1c0c0c1c1c1c0c0703030303079f01c01d542c2d542e7d0f0b42c2c2d43c3c3c5d55031100c0300c0303003030107c23102c0f00f803e000750741c1d07070707070707070707070701c0c0c0c0c1e7c1c01c1c7c5407501c1c5c41c3c07070b01c1c3c1c3c070070f0701c00f07201c2f20303035555550000000000000000005555370f2b0b2b0b370f0000000055550707070700005030355555555000000027c0410000000555543d50b500000555541c1c1c1c0001e7c0150741d4404040402f002c00020000440040000c2b0f0b9f551f51f46c6d000000040000000000051b171b1750f2b0b2b0b7b0f000000000750741c1d07070707000079f00280c0ea9547d47d1b1b40000000409f000000016a17583ea0ba0000041d41d070741c1c1c1c0001e7c02a0781e81f0101005c02f002c000000220020000307d47c6c2c03087d13031f1b0f0a10786c6c6c6c2c3c2c3c2c3c2c3c0000000000200007d47c6d1b171b171b40000000000001c1c1c1c1c1c1c1c1c1c1c1c0000280c0ea86c6c6c6c2c3c2c3c2c3c2c3c00000000000809f0087e66a6a1790000002070707070707070707070707000079f00a81e07a07c0404017003c00b0000000880080000c272727270b0f0f0b2b0f0b0f0b0f0f1f0f43d0f0f0f43c3c3c5c3d000c0300c0300c00c00c0c00c0c02f0bc2709c0b03c03e00f8001c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c0c1c1c0c0c030301c01c9c9c9c9c4c3c4c3c4c3c4c3c0000001f0101005c00f002c000000000000000707070707070707070707070039f0000300555555000000001040000001555542d0000555541c1c1c1c000141d5271b271b2b2f2b2f1b27271b00000001007c01701002c00f0000000002702b0000000707070707070707070707070020000c0007272727272b2b272727270300c0300c0300c009c270ac0007070707070707070707070701c0c0c0c0c1e7c1c01c1c7c41d01c1d01c1c5c41c07070b01c07201c2030303130f55a551b1751b175942e69690b0b47d47cfc0cac3f032b11b1b42c2c2c2e5a2a29a6aaa84d41c2c07071301c1d071342c1c2c1c4c1c4c1ea82c4c2d542c2d42c5d542e7d42c2d542c2d1f51f0b030b02c0c2c46c6d0b0b0b0b968a8a69aaaa87d56a0b82eaa0baa96a17582ea0ba8aea03aa84d41c2c2c1c1c2c4c1c1d071342c1c2c1c4c1c4c1e81e7eaa84d55555555542c2eaa955556c0cac5b032b155542c2c2c2d15295556aaa84c54555550b070b0713071307607a9555555550b5550b9f55540d15155542c2c2c2d15195556aaa9655555a5555555582ea0ba8aea03aa944c4d5541c1d55542c1c2c1c4c1c4c1e81e7eaa84c1561546c5d46c5d47d43cdc2c3c3cdc2c3c3d0f1b612414100c0300c120a0a212200135070300c0c00c0d071343c1c4c1c030320805503035031751f50f03030313030b030343c6d127d41540300c0304828288488021f55a80e03aa80eaa5a85d60fa82e82a030a84d41c0c0c0c1c0c4c0c0d071343c1c4c1c0303001e7c280 24 16777215 10 1023
def hc_68_5 : Nat → Nat := unpackHintV5 0x8360b11ff01d07a98a51d6b2766da9009b5003469787919122985f3ca195c44165288911376258476ccd912416e40188f0f6314639a07d8dd512634d84f8c4a1d82df8660a3229825786a08122981bb89205722f811d47e832e28e0a94448212126051866000028c 0x5559f5555550b5543d55555540c0d555540c5d540c5d5540c0c0c2c0c0c0d3d55034545503030303030303554546517543c6cfc3c0cfc0e03030380c0c0c0d55135541d41d50f071307030327030303030303079f130713075555555555503030303555555550f0f430b430b0f0f403035455550f1b3f0f030303033f06e3f06e55550f07130703030340c0c4c5451307130755555567d0b5543d555540c0d555540d555555540c0c0c2c0c0c0d1d03454555503030303030303454655550f1b3f0f034b0380c0c0e0303030344d550755550f071307030327030303030303079f13071307550350b42c2d0350340c0d030303030303550f0f5231723175030350340c0c0c030303030307d47d232342c2c2c2c0c0c0c0cfc3f8fc3f84d41d071342c1c2c1c0c0c0c0c4c07070b01c1c4c1c4c1c2c3c2d542c2d42c5d542e7d42c2d542c2d030355031f03030303030b0303030303030b030b50317030350303030b030b0303030b030350303030300c0c0c40c0d030303030303031f51f0b02e0b02e48c8d0b0b0b0b032f0380c0c0e03030303135070b0b07070b13070741c4d0b070b07030313030303030303079f130713078fc3c2c9f0713555555555555030303035555555503030b0b03030303403035455550b0b0b0b030303033f1ce3f255550b070b070303030340c0c1e7c4c545130713075555555542d5542e7d55540c0d555540d555555540c0c0c2c0c0c0c2d03454555503030303030303454655550b0b0b0b032f0380c0c0e0303030344d550755550b070b07030313030303030303079f13071307550b50b42c0d0350340c0c0c0d03030303231f55231f50f0f03035030350340c0c0c030303030308d46d171742c2c2c2c0c0c0c0d0c1b90c1b84d41d071342c1c2c1c0c0c0c0c4c07070b01c1c4c1c4c1c2c2d542c7d542c2c3c2d542d550b0b50b9f030355031f03030303030b030b03030303030b0350317030350303030b030b0303030b030350303030300c0c0c40c0c0c0d030303030303032351b0b02e0b02e45c5d0b0b0b0b032f0380c0c0e03030303135070b1307070b0b070741c4d0b070b07030313030303030303079f130713070b0f0b550b0b42c5d0350303030303030340c0d03550f0b0b0f43c3d030303031f51f0b0b82c2e48c8d030303030f0f0f0f135070b0b070b130741c4d030303030f070b07130713070b0b50b1f550b0b0f0350303030303030340c0c0c0d0f550f0b0b0f50f035030303032351b0b0b82c2e45c5d030303030f0f0f0f135070b13070b0b0741c4d030303030f070b07130713074f2747270b0f0b0f0f0b0f0f0b0f03030303030303030303030303030f1f0f43d0f0f0f43c3c3c5c3d0303030300c0c0c0c0c2f2f2f2f272f2f270f0b2f0b0f0f030303030f03e0f03e13071307130713070f0f070b1307030303030f01c1c3c4c1c1c4c1c4c1d547d43d0f2340000000e55a52317231750f0f330b330b0f0f00000000000000001350741c4d0f071307000000002154041701f50f003c0b043c8d030355031f00003003030050317030350303030b0303032f000000000000c127c0000000000000c8004d41c00704c1071343c1c4c1c0000c09f0055555544440300c504555550f0f3f0b3f0b0f0f003035014514522000a0a55550f07130700d0151609555555555555540c0c0c2c0c0c0cbd11100c0300c0c0c49f05145220a0a000155550f542d5035550340d54150306555543c1c4c1c0003030079f82541d135555555555555550303030b0303032f00000000c00000000000055550f07130700003027c01555554000001555555543c3ccc2ccc2c3c3c00000041000000000155543c1c4c1c003009f00000004100049d540b0003d555400c0c000000d555555540c0c0c2c0c0c0cbc0000000000030000127c10000000000130001d55543c1c4c1c0000c09f00551f50f43c6d031100c0300c03154146c5c6c5d43c3cfc2cfc2c3c3c00c0e804884880024144d41d071343c1c4c1c0380a8a82551f50f43c6d030355031f50317030350303030b0303032f031100c0300c03030305127c848803282a80005a85d60fa82ea03aaa0380ea823ba80e030544d41d071343c1c4c1c0003030079f82aa0707a1313a45d51b2350f43c5d031100c0300c231f55231f5003143c3d0c2d0c2c3c3c00c0e804884880024144d41d071343c1c4c1c0380a8a8245d51b2350f43c5d030355031f50317030350303030b0303032f031100c0300c030303146127c148803282a8021f55a020fa82ea03aaa0380ea82a030544d41d071343c1c4c1c0003030079f82aa0707a1313a01006d5422350f02c000f43c5d030355031f0030300000031b50317030350303030b0303032f000000000000c040000049f00000000c8004d41c130001d071343c1c4c1c0000c09f001b1b1b1b0b0b0b0b0b0b0b0b03030340d031f0340c5c0c0c0d0303030b030b0303030b032f0300c0300c0300c030303222202c9f0a0a0a0087e66a6a17902038beaa0380ea82a030a84c1c4c1c4c1c4c1c2c1c2c1c0003030079f82a81e13a3f1b3f1b0b0b0b0b0b0b0b0b000000331f334cd331f1b4cc5ccc5c6d0303a0380c0c000000000002c9f00000013071307130713070b070b07000c027c000000fc6cfc6c0401f005c042c2c2c2c2c2c2c2c203030340d031f0340c5c0c0c0d0030300000030303030b0303030b000000000000c000000000b27c0000004c1c4c1c4c1c4c1c130001c2c1c2c1c0000c09f00551f50f43c6d00000000400000001a85d83ea800021350741c4d0f0713070000aa13917546c8d43d0f17400000001040000021f5a020faa000084d41d071343c1c4c1c0002a84e3f1b4b1b2f0f2f0f1b0f2f0f00000007c0404017003c00b00000000000003c000013071307130713070f071307000204c0130027270f0f270f0f03030340d031f0340c5c0c0c0d0303030b03030303030303030303030303030303030327270f0f030380c0c0e0303030313071307130713070f0713070303030303030303079f13071307 26 67108863 11 2047
def hc_68_6 : Nat → Nat := unpackHintV5 0x7ea4d03e78369e6f334e84acc6f8d26365a5b1a15460c8421a6100c82e428f95ea4dca9917052709627a26593152f09121e24578c620d47a0fa53147549f832c1f916acad0a3b46c49e1fe22a4930f5e7d066f500281ad80eb9550446c5815e3140002bc 0x9c9c9c9c2c3c2c3c2c3c2c3c003c0003c000f0101003c00f000c000000000000000707070707070707070707070070000700c0015555540000000041000000055543d54000155550707074000141d5271b271b0b0f0b0f0b0f0b0f00000001007c0170102003c0000000009c000f000001c1c1c1c1c1c1c1c1c1c1c1c00800070001c9c9c9c9c2c3c2c3c2c3c2c3c3c3c3c9c3c9c3c2c2c3cbcbc9c9c9c9c3c2c2c3cbc3c3c1c1c1c1c1c1c1c1c1c1c1c1c1c2c1e7c1c1c1c1c1c1c1c1c1c7c1d0741c1c1d070707170741c1c1c1c0c1c0c1c1c1e0707070781c1c1d5567d5555542d550f554440c141100c031454545c5c41544154545c5c44d3c0b130b0dc0707110506117141b04c003720fc955135541d41d5130713070303079f030301c0c0c0c4c01d41514151554ac2c4c3cac2c4c3d5555414111100c03006e01b844441b04c000c0d55555544c1c4c1c030304c01d5555559f42d550f555540c14111100c0314dc415441454545444d1c0b130b0dc07070506111106c13000dc84b25131355507075555130713070303079f030301c0c0c0c4c01c0551f1751f17513513130b130f130b130f44c4d0000000000000100111008c013004c000000000000000000131351307030351303070741c4d130713070079f0000300015555550b5543d55540000000000041f10000101004c0130000000000000000001035541d135555130713070079f0000300171755171f45d523004d44c4c2c4c3c4c2c4c3d1313131340000000000023010111000004c013000000000000000000004d41c4c0c1c1c0c0d51307131344c1c4c1c01e7c0000c013c9d1c9c2c3c2c3c2c3c2c3c3c7c3d0f43c3c3d0f0f0f170f400300c0300c03003003030030300bc2f0bc2702c0f00f803e0013071307130713070f0f070b1307030307070f03070700c0c13007372737270b0f0b0f0b0f0b0f00000007c0404401705c00f0000000000000013071307130713070f070b07000130055555500005555130f2b0b2b0b130f000000000000000000000055551307130755030350000555555000000101010100bc00b00009f01040000000000155550f542d4000000141000555544c1c4c1c01e7c0000c0150744d5547d44d131b4000146c5c6c5d44c3cac2cac2c4c3c00000000000000000000004d41d071344c1c4c1ea80c0e800001547d44d131b40000001f0101005c02f002c0001027c000000000005a85d60fa82e80002030000a080011350741c4d130713070079f0000300a81e13a45d51b2351344c5d231f55231f0000130f2b0b2b0b130f000000000000000000000001350741c4d13071307aa0303a0000045d51b2351344c5d00000007c040401700bc00b00010009f010000000087d568083ea0ba0000000a080011350741c4d130713070079f0000300a81e13a3f1b4b1b2b132b131b132b1301007c01701002c00f0000000000000000000004c1c4c1c4c1c4c1c4c1c4c1c030020004c009c9cac4cac4c9c4cac4c0c0300c0300c0307c507c9d05c5c44c0b130b0070700270ac13000821307130713071307130713070303079f030301c0c0c0c4c01c2c3c2d542c2d42c5d542e7d42c2d542c2d0350303030300c0c0c40c0d030303031f51f0b02e0b02e48c8d0b0b0b0b0303030307507070707070707070741c1d070707070303079f0303030307070707031f550303030b030b03030303030b033b030303035030303175030b0303030b03030303030380c0c0cbc0e0307035555555542d5542e7d55540c0d1543b555503030303454655550b0b0b0b0303030341d55075555070707070303079f03030303070707075033b55555030355555555030b0303030b03030303030380c0c0cbc0e0307032154041701f50f003c0b043c8d0000000000127c00000000007507001c07041c1d07070707027c03000031f55030300003030033b005030303175032f0303030b030300300000155555511100c03049f0514522000155550f542d4150306555541c1c1c1c01e7c0c0c20950741d5555555540cbc0c0c0c2c0c0c0c0c0e80295540c0d40ced54055555500000000000000555507070707027c0300055555555032f0303030b0303003000000104001275502c000f5555000c0003b000000000049f040000001c0007555507070707027c030000033b00000030355555555032f0303030b0303003000001547d43d0f1b40c440300c0301449f212200016a17583ea0ba0a80c150750741c1d070707070079f0303082aa0707a073ba031f5503035030303175032f0303030b0303030303a00aaaa0303a033baa006c6c6c6c2c2c2c2c2c2c2c2c0c0300c0300c03088880b27c28021f99a9a85e400a80c2a0707070707070707070707070079f0303082a81e07a031f0340d03030340c0c0c5c0d030b0303030b0303030303a00aaaa0303a032faa009c6c9c6c0401f005c042c2c2c2c2c2c2c2c20000000c0003b00000000000b27c001c1c1c1c1c1c1c1c070001c1c1c1c1c09f00c0000c7c0d0340c0c0d0303031703400cec000000c0c0c2c0c0c0c2c0c0c00c00000272727270b0f0b0f0b0f0b0f0f1f0f43d0f0f0f43c3c3c5c3d030303030303030303030303030303030303030300c0c0c2f2f2f2f272727270f0b0b0f0f03e0f03e0303030307070707070707070707070707070707070707070700c0c0c0c1c1c1c1c9c6c9c6cbc3cbc3c6c3c9c3c0000000401f005c0400b003c000000000000000707070707070707070707070020001c0007272727270f0f270f270f030303030303030303030303272727270f0f030303030707070707070707070707070303079f0303030307070707031f0340d03030340c0c0c5c0d030303030b03030303030380c0c0c0e030703 25 33554431 10 1023
def hc_68_7 : Nat → Nat := unpackHintV5 0xba09d2aea2daa2b2fc9e810c9a012093b99287daf87e426670ab66667a8c60f96057e2465788164eba3442431e3ce95634223233b81a2c21e6218aa621600a21600021380a2138002038402038002038002038001f6834175a040bd2e20002f4 0x45d51b0b50b42c2d231f55231f51702c5a0707aa2352345c5d0b0b0b0b43032b10c0cac9669aa8985aa1350741c4d0b0781c4c3eaa84c1c4c1ea917546c2c2d542c7d42c5c2c2d42d42d0b0b41c1c1c8d48d171742c0c2c0b030b02c2c2c2e55969fa582ca8aaaaaa87d56a17a0baaa0b82eaa0ba82ea2ba80e951350741c4d0b0b270b0b0707070b079f13071307aaaa0707a1313a05d445c6d56a0b0b550b1f0b0b0b0b00b002c0b170b1b50b170b0b50b50b0b0b02c0b0b0b42c2d07070723100305c0306d05c0b0300b0300b02c146146969f02c2820ba220013507131301c13070741c4d0b0b270b0b0707070b079f01c4c82550b50b42c2d00400000000000001a85daa0b820001350741c4d0b0781c0002a84e45d51b0b50b42c2d004100000000000087d680aa0b820001350741c4d0b0781c0002a84e3f1b4b1b0b0b0b0b0b0b0b0b07c040401702001c000000000000000002c0000004c1c4c1c4c1c4c1c2c1c2c1c081300004c006c6c6c6c2c2c2d0b42c7c2d0b170b0b0b42c2c2c2c2c2c2c2c1c1c1c0c0300c0300c0c0c0c00c0c0b00300c22220a0a2200e9f2207e4686817902c2a80b0aa02e80ba00e284c1c4c1c4c1c4c1c2c2c3c2c2c1c1c1c2c1e7c030320a80704e8fc6cfc6c2c2c2c2c2c2c2c2c0c0300c0300c030cc7ccd334cc7c6d331733171b401c1c0c0c0c0a0380888888032003a7c28284c1c4c1c4c1c4c1c2c2c1c1c0c1c2c1e7c030303c3c00c0c0c823f1b3f1b0b0b0b42d0b1f0b42c5c2c2c2d0b0b0b0b0b0b0b0b07070700c0d1031f1031700c0d00c00c2c0c2c030030b0300c0c2c03030b0300c0300c03030030300300c288888282888032b00c803a7c4c1c4c1c4c1c4c1c2c2c3c2c2c1c1c1c2c1e7c0c4c0300c0c1c03032089c9c2c2c2d0b42c7c2d0b170b0b0b42c2c2c2c2c2c2c2c1c1c1cacac9cac9c2c0c2c2c2c0c2c2c2c2c2c9c9c2c2e0b0b0b82c2c2c2cacac4c1c4c1c4c1c4c1c2c2c2c2c1c1c1c2c1e7c4c1c4c1c4c1c4c1d5555550314440300c555555550f0f0450030303030111102c0f00047811e555507070740303001c1d141c01d55555540e7d451500c0315515143c50b103d111102c0f00120bc555541c1c1c1c1c2c1e7c0303050741c41c01d555555541c3c1c01c0303030307030045070750704078001e0707079f227d542d43d0f0b40c0c540e7c40300c0300c0d541c0d48c5c8c5d43c3c02c0f0f0030303030107c23102c0f000822e0750741c1d07070707070b079f0700c0c007070701c1c1c01d542d43d0f0b40c0c540e7d00c0300c030303505c7c5c43c3c0b0b0b03c5107c23102c0f0007c82f20750741c1d07070707070b079f00c0c01c1c1c1c1c0707007071f5507075070707175070f07003030303000701c1c1c1c1c7c1c01c078001e07070755555555550f0b0b0f5555aaaa544555550f0f5553f03c0c3c0cfca88a555507070741c1c1c1ea941c1d5555555555543c2c2c3d69f55555aaaa5555550f542d52b540d59555507070707070b079f07070707aa541d07555555555072f070701c0c1c0c1caa8807a5550707507550707070f00e7d542d43d0f0b43d47d1b0f43c2c2c3e559a6aaa87c5507146c5c6c5d43c3eaa80f030f038f162241d41d070741c1c1c1c1c2c1e7e07070707aaa0707aa550b50f43c2d0f51f46c3d0f0b0b0fa55a7da6aaaa1f96a17583ea0ba8aea03a541d41d070741c1c1c1c1c2c1e7c1c1c1c1eaaa0781e81c7d541c1d41c1c1c5d41cbc1c1c07030703072a22aaa81c1e81ea81c1c1c7d47c6c2c3c0c21f44c1c7c6c3c00e10706c6c6c6c2c3c2c3c2c3c2c3c0c0300c0300c030888888200c1f51f1b46c5c6c5c6d0f0f08a0030303030a00a0707070707070707070707070b8030320801c1e286c6c6c6c2c3c2c3c2c3c2c3c0c0300c0300c0308888888803a7e1f1929285c60f282c80f8a070707070707070707070707070b079f00c0c82281e072071f0741d07070741c1c1c5c1d070f070030303030a00a08a0707a0708070707272727270b0b0b0b0b0b0b0b0f1f0f43d0f0f0f43c3c3c5c3d0707070f0f0f0f0f0f0f0f0b0b0b0b0f030f03c0c3c2f2f2f2f272727270b0b0b0b0f03e0f03e0f0f0f0f07070707070707070707079f070b0707070b070707070707070707 24 16777215 10 1023
def hc_68_8 : Nat → Nat := unpackHintV5 0x875cb920c022e8060541f00230767cb09c302de69a4e3999e196636462977b2bc584cb4152e1ca4f78a812a327642890090880343e64778e5328c3440a18b05416294859899517a23186787eb1b619ccbc05c415e12c48984091500d6058824e21405b47080002da 0x2a5505d47c5c42d42c0b0b0b0b0b02d0b0b47c400c2b00c1f42302c0b169f1a148488001d41c070707070701d070741c2c1e7c1c1c1c1c07072081c7d541c1c01c07070707071f0713007141c1c1c5d41c2c1c01c0c1c0c280281c1c1d55555555542c2c2c2d69f55555aaaa5555550b542d52b540d595555070b079f0707070707070707aa541d07555555555070b070701c0c1c0c1ca88a5550707507135507070755555544440b02c111122005555070b079f0707070701c1c8255555555070b070070307030a00a07070755511549d5542c2c4542c4d555403110ad11102c0b047c5569f145220041c45075555070b079f0707070701c1c825071304045070755555555070b070070307030a00a070707550b50b42c2d1f51f46c6d0b0b0b0ba55a7da6aaaa1f96a17582ea0ba8aea03a541d41d070741c2c1e7c1c1c1c1c1c1c1c1eaaa81c1e81c4e81c7d541c1d41c1c1c5d41c2c1c1c07030703072a22aaa81c1e81c4ea81c1c1c6c6c6c6c2c2c2c2c2c2c2c2c0c0300c0300c03088888803a7c881f91a1a05e40ba02e8038a0707070707070707070b079f0707070700c0c82a01c07a071f0741d07070741c1c1c5c1d070b070030303030a00aaa007001caa070707271b271b0b0b0b0b0b0b0b0b00c0d1031f1031700c0d00c0c2c0c2c03030b03130300c0300c0300c28888888032b00c803a7c1c1c1c1c1c1c1c1c1c2c1e7c1c1c1c1c0c1c0300c0c1c03032081c7c1d0741c1c1d070707170741c2c1c0c0c1c4c00c00300c0c1c1c00c0c0c0c280281c1c1c9c9c9c9c2c2c2c2c2c2c2c2c0000002c07c0404017000c00b0000000000000001c1c1c1c1c1c1c1c1c1c1c1c01c0001c03000271b271b0b0b0b0b0b0b0b0b00000001007c01701002c080000000002c000001c1c1c1c1c1c1c1c1c1c1c1c00800070001c9c9c9c9c2c2c2c2c2c2c2c2cacac9c9c9c9c2c2c2c2c9c9c9c9c2c2c2c2cacac1c1c1c1c1c1c1c1c1c2c1e7c1c1c1c1c1c1c1c1c1c1c1c1c1c7c1d0741c1c1d070707170741c2c1c1c1c0c1c0c1c1c1e0707070781c1c1d5567d555555550b0b555550b17550b175555542d550b550707075540d5517550b030b0b0b030b370b0b0b0b5545d55945d50b3f0b82c2c2e0b0b0b0b2b1b3f1b5544d5507507542c2c9c2c2c1c1c1c2c1e7c4c1c4c1c4c1c4c1d55555555555555541c1d5555542c2c2c2d0c0cac43032b155542c2c2c2cfc1b8fc1b8ac6cfc6d55542c2c1d070b130f555130713071307130755555567d42c2d555542d555555550b5542d55541c1c1d03554ad55542c0c2c2c2c0c2cdc2c2c2c2d2f55655550b4b0b82c2c2e0b0b0b0b2b1b3f1b44d550755550b0b270b0b0707070b079f1307130713071307550b50b42c2d0b1547c523172317503030707030303030350340c0d0303030350300d0307d47d232342c2c2c2cdc378dc3780c0c0c0c4d41d071342c1c0c1c3c3c0c0c0c0c0c0c0c0c0c0c4c1c4c1c0c7c0d540c0d40c5d42c2d542c7c0c0c0c0c0c0c2c0c0c2c2c0c0c0c0d42c5c2c2d42d42c0c0c0c2c0c2c0c0d0b0b41c1c1d40e7d40c0d540c0d030303030300c0c0c2c030303031f51f03030380cbc0e48c8d0b02e0b02e0b0b0b0b0303030313507030303070313030341c4d0b0b0f0b0b0707070b079f03030303130713078fc2b039f070f5555555445555550707555555550303030303030300c0c0c55550b0b0b0b3f1de3f20303030355550b0b070741c2c1e7c3c3d5540c0c0c0c4c1c4c1d555555550b0b555550b5555555542d550b5555070707503555039f55503030300c0c0c030303034bd55955542c0b82c0b82c2c2c2c0c0c0c0d135541d55542c2c3c2c2c1c1c1c2c1e7c0c0c0c0c4c1c4c1d542d42d0b0b0b0b48c7d548c7d45c0b140c0c1c1c0c0c0c0c0d40d030340c0c0c0d40c0340c2351b45c5d0b0b0b0b3706e3706e030303031350741c4d0b0703070f0f0303030303030303030313071307030355031f550303170b0b550b1f03030b0b030303030303030303030b50b170b0b50b50b030b03030303030b42c2c2c2d0707070355035540c0d40e7c0c0c0c0c0c0303030b00c0c0c0c8d46c0cbc0e0303039171742c0b82c0b82c2c2c2c0c0c0c0c4d41c0c4c0c0c0c0c0c1d071342c2c3c2c2c1c1c1c2c1e7c0c0c0c0c4c1c4c1c055030340c5d0b50b030303030b0342c2d00400c0000000000000001350703030303130341c4d0b070307000003035031f55002d42c0c2c0c0c0c0d0b0b0b0b401003040000000000000004d41c0c4c0c0c0c0d071342c1c0c1c0000dc9cdc9c2c2c2c2c2c2c2c2c00000002c07c0404017000c00700000000000000004c1c4c1c4c1c4c1c2c1c2c1c004c000c13000550b50b42c2d0b956948c5c8c5d401c1c2c1c2c1f1108c0b02c33030330301221220a0a001350741c4d0b070b07130f0130f070071320aa5505d47c5c42c2d542c7c02c0b1f0b0b0b0b0b00b142c5c2c2d42d42c0b0b0b0b0b02d0b0b41c1c1c7c400c2b00c1f42302c0c02c0c02c0b169f1a14840b0a082e888004d41c130707131301d071342c2cbc2c2c1c1c1c2c1e7c07132095555555115555541c1d5555542c2c2c2cfc0cac3f032b1555556aa2a2aa955542c1d07130f55513071307aa5555555555555507070755550b030b02c0c2c0b0b0b0b5a7d555562a2aaaa95555542d5542d0b5542d50b54ad50356555542c2cbc2c2c1c1c1c2c1e7c4c1c4c1ea950744d5555555555555541c1c1d11102c0c02c0c02c0b044442828880155542c2cbc2c2c1c1c1c2c1e7c07132095555555555555401c1d5111102c0b0cc0c0cc0c05145148828280155542c2c1c1d070b079f130f05401c4c8255511549d5542c2c101142d555555550b1142d55541c1c1c03110ad11102c0c02c0c02c0b047c5569f1450a0a220044c450755550b0b2f0b0b0707070b079f01c4c82550b50b42c2d0b1547c51b171b175a0707aa1f51f46c6d0b0b0b0b3f032b0fc0cac9669aa8985aa1350741c4d0b0781c4c3eaa84c1c4c1ea9542c2d542c7d42c5c2c2d42d42d0b0b41c1c1c7d47d1b1b42c0c2c0b030b02c2c2c2e9569f6982ca8aaaaaa87e5a85d60baaa0b82eaa0b84ea0b82ea2ba80e951350741c4d0b0b2f0b0b0707070b079f13071307aaaa0707a1313a 26 67108863 11 2047
def hc_68_9 : Nat → Nat := unpackHintV5 0x93a88ca2df416856cc21fd13147a80989d502a070f08a1b5a1c46848a4196915262c45c179b22c5aa878962211055c858140a2d04cb46e91d32b43f94f70e8d2b0321d030bbc1962c445589fe22624547487b82ba1b147985682ba128c62834d2ac0550fc80002a8 0x117548c8d48d171748d48d171748d46d171746c6c6c6c1d541d41e7c1c1d41c1c1c1c1c1c1c1c1c1c1c1c1c7d541c1c1c5c1c1c1c1c1c2c1c1c1c1c0c1c0c1c1c1e0707070795131355131f55070707030355031f0303030303130313030303030313032750317030350b50b0b0b0b0b0b0b0b0b42c2d03030b0350303030300c0c0c40c0d03030303030303030b03132351b1304e1304e45c5d03330380c0c0e0b0b0b0b030303031355075541c1d41e7c0c0c4c4c0c0c0c0c0c0c1c1c2c1c2c1c0c0c0c0c4c1c4c1c4c4d544c7d541c1c1c0b510b1f02c02c4c2c4c0b00b130b2710b1702d42d42c2c2c2c2c2c2c2c2d0b0b6a23104c0c04c0c105c00c0b00c3b0b02c120a0a2102c4c0ba82e9f001355075541c1d41e7c2c2c4c4c0702c1c2c1c1c2c1c2c1c07132084c5d545c7d541c1c1c8d43c4c2c3c3c4c2c3c3d0f1740351031f00c00c4c0c4c030031703271031700d403030b00c0c4c0c4030300303040300c030a120a0a212200c6c03200e9f1355075541c1d41e7c3c1c4c1c0c0c4c4c0300c0c0c1c1c03032084c5d545c7d541c1c1c8d44c4c2c4c5c4c2c4c9d131748d48c5c0c4c5c4c0c5c9d171744cec4c8d46c5c9c4e1317179171744c6c4cec6c6c4d541d5507075079f1307130713071307130713075555555555555550313035555030b039f0303030303030355550f0b0b0f03030380c6c0e0303030355555079f07070707030303070307030303030303070707075555550f542d50340d55034ad5515034644541d55555554444030b039f030302d454545440c0c0c130b111102c0b0002c81b255555079f0707070700c0c01c1c1c1c1c07070075555550b542d415030045542d0f04600541d5555555555555550b151555540c0d1500c0d0355551b06e1b06e0b0b0b0b0303030355555030303030303070707070707030303030707070755555555555555503030b555503030303030303030b035555031b0380c0c0e0b0b0b0b0303030355555079f0307030303030307070707070303030307070707555555035550340d550b542d515034644541d555555544511300c0c4e7c44440300c01555541e7c0c0c0c0c070701c01d5555540d50350544c18015075555555511100c031555550413140c0d554154044440b03c0006e01b955541d0707070700c0c007070701c1c1c01d555555511100c0c0b030b03515155151317103030302c2c44440b03c0013206c9555541e7c1c1c1c1c03030070707070701c1c01d5555543d50b50540c011551341180150755555555555555555555550f0b0b0f0f030f03c0c3c55550f0b0b0f0f03e0f03e0f0f0f0f555507070707070707070707070707070707070707070707555555004100001010101003c00b00000000000000155541c1c1c1c01c0001c030005555555555555551b1b1b1b1b1b1b1b55555079f070707070707070707070707555555542d5540d5951b541d5559f5555550b5543d55555545c5d555543c3d55545c5d41c1c1d55035545d543c2c2c3c3c0c3cdc3c0c3cdd5517556517543c2c2c3c3cfc6e2f3f0f8bc3c3c6d55135541d41d5070b079f0b0b07070b0b0b13070f071307130755555555555555070755550f033b03c0cec55550f0b0b0f2f06e2f06e55550f0b0b0f2f0f0f1b0b0b555555541c2c1c4c1c3c1c4c1c4c1d5555559f42d550f5555543555550f0f5555555507070740d552b55550f0b0b0f0f030f370f030f374bd55955543c2c2c3c3d0c6e2f4b0f8bc3c3c6d44c4d5541c1d55541c2c1e7c2c2c1c1c2c2c2c4c1c3c1c4c1c4c1c3c3c3d547c5d47c5d42d0f43c3c2c2c3c1d41c1d0f0b543c3d43c3c3c3d5543c3c3c8d41c1c1c3d43c3c0c3c3c3c0c3c3d0f0f43c2c2c3c3c3c3c3c3c3c3c3c7d47c7c7c7e1f2f1f9232343c2c2c3c3c3c3cbc3cbc3c3c3c3c3c3c4c4d44c1c2c2d44c2c1c1d071341c2c1e7c2c2c1c1c2c2c2c3c1c3c1c4c1c4c1d555555542d55075543d5543c7d55543c3d55541c1c1d035543d55543c2c2c3c3c3c3c3c3c3c3c3d2f55655550f0b0b0f0f0f0f2f0f2f0f0f0f0f0f0f42d550744d55541c2c1e7c2c2c1c1c2c2c2c3c1c3c1c4c1c4c1c5c5d545c7d17548c3c3c3c2d43d41c1c2c2c3c1d0f0f0b43c3c8d543c3d5543c3c3c3d43c3c1c1c1c3d43c3c0c3c3c3c0c3c3d0f0f0f0f43c2c2c3c3c3c3c3c3c3c3c3c8d46c5cbc5e17171792717171743c2c2c3c3c3c3c6c3cbc3c3c3c3c3c3c4d41c4c2c1c1c2c2d51307131341c2c1e7c2c2c1c1c2c2c2c3c1c3c1c4c1c4c1cdc9cdc9c2c3c2c3c2c3c2c3c00000f0003c040400f001c0030000000000000004c1c4c1c4c1c4c1c3c1c2c1c003c000c0b00055544555555555507075555550f033b03c0cec0f0b0b0f55558a8aaaaa5555550b0b541c2c1c4c1c3c1ea9555555555555541c1c1d55543c2c2c3c3c0c3c0f030f169f55555aa8a8aaa5555550f542d50f43d552f5552b540d595555070b079f0b0b07070b0b0b13070f07aa541d135551f1547c51b171b1750b50f43c2da0707aa0f51f46c3d0f033b03c0cec0f0b0b0f96698589aaaa1350741c4daa0b0ba81c2c2c2c1c4c1c3c1ea9542d43d0f0b47c7d543c7d43c5c6c5d41c1c1c3d47d1b0f43c2c2c3c3c0c3c0f030f29569f69aa8a8aaa87e5a85d60f83ea0b82ea0f83eaa2faaa2ba80e951350741c4d070b079f0b0b07070b0b0b13070f07aaa81e13a45d51b231f55231f51705c50b50f43c2da0707aa0f52345c3d0f033b03c0cec0f0b0b0f966a98589aaaa1350741c4daa0b0ba81c2c2c2c1c4c1c3c1ea917546c2d43d0f0b48c7d543c7d43c5c5c5d41c1c1c3d48d170f43c2c2c3c3c0c3c0f030f255969fa5aa8a8aaa87d56a17a0fa82ea0f83eaa2faaa2ba80e951350741c4d070b079f0b0b07070b0b0b13070f07aaa81e13a3f1b4b1b01007c017010b0f0b0f0b0f0b0f20001c0000000000000000003c004c1c4c1c4c1c4c1c0b0020f070b070004c009c9c2c3c2c3c2c3c2c3c7c3d43c7c9d0f17170f41c1c1c3cec3cec3cec3c9c3c2c2c3c3c0c3c3c0c3cbcbc9cbc9c3c2c2c3c3cbe2f0f8bc3c3cec4c1c4c1c4c1c4c1c1c2c1e7c2c2c1c1c2c2c2c4c1c3c1c4c1c4c1c0c7c0d540c0d40c5d42d42c0c0c0c2c0c2c0c0d0b0b540e7d40c0d540c0d030303031f51f03030380cbc0e48c8d0b0b0b0b0303030307507030303070307030341c1d070b079f070707070303030307070707071f550707030303030303070703030713030303035070707175070b070300c0c0c0c0c0781c0701e0707075555555542c2d5542c4d555540d5540e7d5540c0c0c0d2f55655550b0b0b0b0303030341d55075555070b079f0707070703030303070707075071355555070755555555070b070300c0c0c0c0c0781c0701e070707 26 67108863 11 2047
def hc_68_10 : Nat → Nat := unpackHintV5 0x8d486f221a2708314aaa0151607da0569e691fe75a0809cd911e6f947a1a9b29467845d17de4065904ce95152584f48a191cb40e42e0898fa122e37fcd10d0c1e62e50bc0ac519e278871885431c1d607e05da2fc14146a84221c60a38ca015127a02b452000015a 0x551f51f46c6d031100c0300c1221222200e9f07c4c12946c5c6c5d43cac2cac2dfc3c00c0c0c0c280281d5641c1d0707070700c0c820589551f51f46c6d031100c0300c1221222200e9f87c5494a17184ca0b20ee281c1d541e7d070741c1c1c1c0303208a0781c81c7c1d41c1c1c5d41c3c1c1c1c2c1c1c00c0c0c0c280282281c1e81c215550b1f50f0f43c3c2c8d0f1f550f0f50f0f0f1750707070f50f43c3d0f0f0b0b0f0f0f030f03c0c3c1f51f48c8d0f0f0b0b2f0f0f03e0f03e0f0f0f0f0750741c1d07070707070707070741c1d41c1c1c1c1c1c1c1d547d47d232341f000023000ac07c0404017003c00b00000000000000001d41d070741c1c1c1c01c00100c001547d47d232340000000401f005c0400b003c0000001f023000bc0000001d41d070741c1c1c1c0080040007551f51f48c8d1f51f48c8d1f51f48c8d070755079f41c1d070707070707070707070707071f075070707175070707070b0707070703070307070781c1c1c1e555555555555555555555550f0b0f0b0f0f0f030f03c0c3c55550f0b1b0b0f0f0f03e0f03e0f0f0f0f55550f0f070b13070f0f07070f1307070f070f071307130755555500410004c00404040400f002c0000000000000005555130713070013000304c0015555555555555542c4555550303030340c2c0c4c0c0d15155542c2c2c2c6c1b86c1b80c0c0c0d555542c1c2c1c4c4c0c0c0c0c0c0c0c0c0c0c4c1c4c1d5555555555555555550350303555555542d0b503030b55555440d00c0c0c0c0c0c0c0c2c0c4d555519140c6c0e03030382c2c2c2c0c0c0c0d5541e7d5544c0c4c0c0c0c0c0c1c2c1c2c1c0c0c0c0c4c1c4c1d55555555555550b5555555035133b1355555646d44c6c6c4c6c6c6c6d5541e7d5545c4c1c4c1c4c1c4c1c4c1c4c1d17548c2d43d0f0b40c7d540c0d40c0c0c5d40c4c0c0d40d030340c2c0e7c0c0c0c0c0c0c0c8d46d171743c2c2c3c0c0c0e034b0380c0c0c0c1d541d41e7c1c1d41c1c1c1c0c0c0c1c0c1c0c0c0c0c0c0c1c1c1c1c1c7d541c1c1c4c1c1c3c1c1c1c2c1c1c0c0c0c0c0c0c1c1c0c0c1cac0c0c0c0c0c030303030301e0701c079545d5230b50b42c2d031100c030b039f030302c2c7c540b502c2c5c40c0c0c130b106c17102c0b0002c84b20755075079f070750707070700c0c01c1c1c1c1c0707007071f550707071307070b0707070b0707003030303000701c1c1c1c1c2c1c3c01c078001e5517548c4d544d44c0d42d42d0b0b42c1c1c1c0d40d030340c0c0c0c0c0c0c0c8d46d171744c4c4c4c2c2c2c2c0c0c0c0c1c7d41c1c1c4c1c1c4c1c1c1c1c1c2c1c0c0c0c0c0c0c1e070707917548c8c7d548c7d44c4c0c0d42d42d0b0b42c07070701c1c0d40d030340c0c0c03030300c0c0c0c8d46d171754c1b94c1b82c2c2c2c0c0c0c0c1d41d030740c0c0d0303507070707030303030707070745d523030355031f50317030350b50b42c2d03030b0350340c0d03030303030303030b032351b45c5d034b0380c0c0e0b0b0b0b030303030755075079f070750303070303030303030707070707070303030307070707071f550707071307030307030303030303030303030707070b0707070b07070300c0c0c0c0c0781c0701e5517548c0d40d030344c444c131300c0c4e7c41b05c40300c001d541d41e7c1c1d40c0c0c0c0c0c070701c01c1c7d541c1c1c4c1c0c0c0c0c0c0c0c0c01c1c1c4c01e00079545d5230b50f43c2d031100c0300c231f55231f41304c4c4c4c4c00c0c1c1c1c1c1c0c00c0c0c0c041b05c40b03c0006e01b81d541d0707070741c1c1c1c03030141c0741c01d17548c2d43d0f0b40c440300c0c0b030b03131f1504d44d04c4c5c4c5c40c0c0c0b0b106c17102c0f0004c84b20755075079f070750707070700c0c01c1c1c1c1c0707007071f550707071307070f0707070b0707003030303000701c1c1c1c1c4c1c01c078001e5517546c2d43d0f0b48c7d548c7d04c4c4c4c281c1c1c1c1e0f1103c0f02c0f0300f030122120b02e0a0a000750741c1c1c1d07070707050701d01c1c8245d51b0b50f43c2d131f1504d41313171a83c440f03c0b0030ec0304c48860ba7c0ba02c2c001d541d41e7c1c1d41c1c1c1c070707070701c07072081c7d541c1c1c4c1c1c3c1c1c1c2c1c1c01c07070707071307007001c0c1c0c28029545d51b1355135130b50b50b42c2d81c1c1c8c441704c1302c0b048848888001c7d41c1c1c4c1c1c4c1c1c1c1c1c2c1c01c1c200917546c8c7d548c7c04c4c2c2d02d42d0b0b681c1c1e0707231105c4b0304b0300b02c12210a0a22000750741c1d0701d050707070701c1c8245d51b02d442c7c42c5c0b50b50b42c2da88c441700302c030ec2c0b048840b1302ea0ba7c001d541d41e7c1c1d41c2c1c0701c1c1c1c1c1c1c1c1c07072081c7d541c1c1c4c1c1c2c1c01c00701c1c1c1c1c2c1c1c1c2c1c1c01c0c1c0c281e000729545d51b2352345c5d031100c0300c231f55231f41713171302f0f2b0b2b0b2f0f003030303012212200300c0a0a0750741c1c1c1d0707070700c0c050701d8245d51b2352345c5d031100c0300c231f1507d417171712b1302cac2c132848848803a7c03200c0c1d541d41e7c1c1d41c1c1c1c03030070707070701e081c7d541c1c1c5c1c1c3c1c1c1c2c1c1c00c0c0c0c001c07070707073b0700728029545d51b1350f43c4d1355135130350f13130f031100c0300c803048848888001c7d41c1c1c4c1c1c3c1c1c1c1c1c4c1c03030303200917546c8d43d0f1748c7d548c7c05c4c0c0d03c3d2c2d2c2c3c3c0c440300c032800e01221220a0a000750740c1d070707070300d0500c0c8245d51b2350f43c5d00d440c7c40c5c03500c0c2c030313031100c0300c28488488031b00c803a7c1d541d41e7c1c1d41c1c1c1c0c0c1c0300c0c0c1c1c03032081c7d541c1c1c5c1c1c3c1c1c1c2c1c1c0c0c1c00c00300c0c1c1c00c0c0c0c281e0007295550b50f43c3c2c5d0f1f550f0f50f0f0f1750707070f50f43c3d0f0b0b0f0f030f03c0c3c2351b45c5d0f0b0b0f0f03e0f03e0f0f0f0f0750741c1d07070707070707070741c1d41c1c1c1c1c1c1c1d548d48d1717400005c0007c0404017003c00b0000000000000001d41d070741c1c1c1c01c00100c001548d48d171740000000401f005c0400b003c0000001b0170006c0000001d41d070741c1c1c1c0080040007 26 67108863 11 2047
def hc_68_11 : Nat → Nat := unpackHintV5 0x7fe0771f471627a285e9d8320e7364551ad041264c0d0180e2445b4c9d94b643a4e908912f41604bb00412e500e473c8b10373303d50718dd62fc31e0af0bb318a2b606d894432824dc0688471e01bdca8060b1d81228c0834d27a0a086581a71b60040cb8000020 0x55555546d550b5543d555540c0c144111100c030141844448803a7c88415441685454545413a02e8038a51f555079f5550f07130700c0c82a01c13a5555551515151500c0c2c03031344440300c28444488033300c803a7d55543c1c4c1c0c4c0300c0c1c030320955555511100c030155155543c3ccc2ccc2c3c3c2940444488032003a7c14155555543c1c4c1c030304c4c00c0c0c8255555546d550b5543d555441544140c5454545403030b00c0c4d0305044440300c281418444488033300c803a7d47d5541e7d5543c1c4c1c0c4c0300c0c1c03032095555555542d55555540d555555133b13555955544c4ceced47d5541e7d5544c1c4c1c4c1c4c1c4c1c4c1d542d43d0f0b40c7d540c0d40c0c0c5d40c4c0c0d40d030340c2c0e7c0c0c0c0c0c0c0c7d47d232343c2c2c3c0c0c0e033f0380c0c0c0c1c1d541e7d070741c1c1c1c0c0c0c1c0c1c0c0c0c0c0c0c1c1c1c1c1c4c1d41c1c1c5d41c3c1c3c1c1c1c2c1c2c1c1c0c0c0c0c0c0c1c1c0c0c1cac0c0c0c0c0c030303030301e0701c0795550b50b42c2d031100c030b039f030302c2c7c540b502c2c5c40c0c0c130b107c23102c0b0002c83f2070755079f41c1d0707070700c0c01c1c1c1c1c07070070713075070707175070b0707070b070700700c0c0c0c1c0c001c07070707070b070f00701e0007955503551344c4d0b50b42c2d0b0707070350340c0d03030303030303031f51f48c8d131313130b0b0b0b0303030307130741c1c1c5d071307070707070b070303030303030781c1c1e55030355131352317231750b50b42c2d0b01c1c1c07070350340c0d03030300c0c0c030303031f51f48c8d5314e5314e0b0b0b0b030303030750341c1d03030340c0d41c1c1c1c0c0c0c0c1c1c1c1d540c0d540c7d40c5c0c0d42d42d0b0b40c0c2c0d40d030340c0c0c0c0c0c0c0c2c0c7d47d232340cfc0e03030382c2c2c2c0c0c0c0c1c1d541e7d070740c0c1c0c0c0c0c0c0c1c1c1c1c1c1c0c0c0c0c1c1c1c1c1c4c1d41c1c1c5d40c0c1c0c0c0c0c0c0c0c0c0c0c1c1c1c2c1c3c1c1c1c2c1c2c1c1c0c072b0303030303030301e0701c0795550350340c0d13111304c4c0303139f107c23100c0300070755079f41c1d03030303030301c1c070070713075070707175030303030303030300701c1c1c4c1c01e000795550350340c0d1311348c8d030303030303107c23100c0307f070755079f0341c1d03030303030310707070079f9f227d542d43d0f0b40c440300c0c0b030b0304c4c104c4d48c5c8c5d40c0c1c1c1c1c1c0c00c0c0c0c041f08c40b03c00207f81c1d541e7c1d070741c1c1c1c03030141c0741c01d542d43d0f0b40c440300c0c0b030b03131f1504d44d04c4c5c4c8c40c0c0c0b0b107c23102c0f0004c83f2070755079f41c1d0707070700c0c01c1c1c1c1c07070070713075070707175070f0707070b0707003030303000701c1c1c1c1c4c1c01c078001e55542d43d0f0b44c4c104c4d48c5c8c5d681c1c1c1c1e0f1103c0f02c0f0300f030122120b02e0a0a000750741c1d07070707050701d01c1c82550b50f43c2d131f1504d41313171a83c440f03c0b0030ec0304c48860ba7c0ba02c2c001c1d541e7d070741c1c1c1c070707070701c07072081c4c1d41c1c1c5d41c3c1c3c1c1c1c2c1c2c1c1c01c07070707071307007001c0c1c0c280295550b50b42c2d1f51f46c6d0b0b0b0b966982e9faaaa87d5696a17582e8eea03aa81c1d541e7d070741c1c1c1c1c1c1c1eaaa0781e81c4c1d41c1c1c5d41c2c1c1c1c2c1c1c1c07030703072aa201cbeaaa81c1e81cbea95550b551344c4d0b50b42c2d81c1c1c7c442304c1302c0b048848888001c4c1d0707071741c4c1c1c1c1c1c2c1c01c1c2009542c2d004c4d48c5c8c5d42d42d0b0b681c1c1e07071f1108c3f0303f0300b02c12210a0a22000750741c1d0701d050707070701c1c825502d442c7c42c5c0b50b50b42c2da87c442300302c030ec2c0b048840b1302ea0ba7c001c1d541e7d070741c2c1c0701c1c1c1c1c1c1c1c1c07072081c4c1d41c1c1c5d41c2c1c01c00701c1c1c1c1c2c1cbc1c1c1c2c1c2c1c1c01c0c1c0c281e00072959f0f00d542d43d0f0b43d47d1b0f43c2c2c3e59a6aa0ba7eaa131355a51b171b1750f01c1c1c1c1c03c0c3c0e4ca88a07559070741c1c1c1c1c1c1c1eaa96a5542d43d0f0b43d47d1b0f43c2c2c3e59a6aa0ba7eaa1f55a5a85d613a3ba80eaa070755079f41c1d0707070707070707aaa81e07a0713075070707175070f0707070b07070701c0c1c0c1ca88aaaa0707a07aa55547d47d232340c440300c0307c4c107c4d48c5c8c5d4bc3cac2cac2cbc3c00c0c0c0c048848800c03028281d41d070741c1c1c1c03030141c07609547d47d232340c440300c0307c7c541f505c8c5c4ac4c0b2b0b04ca12212200e9f00c80303070755079f41c1d0707070700c0c01c1c1c1c1c0782071f075070707175070f0707070b070700700c0c0c0c1c0c001c07070707073b07007280295551f50f43c6d031100c0300c12212200e9f2207d4686817504e80ba00e281c1d541e7d070741c1c1c1c030320a80701e81c7c1d41c1c1c5d41c3c1c1c1c2c1c1c00c0c0c0c2a8001caaa007001caa55544d43d0f1340d544d131343c4c4c3c0c440300c03200c122122220007130741c1c1c5d070f0707070707130700c0c0c0c802551f50f43c8d0303401f1352317231750f0f3f0b3f0b0f0f031100c0300ca003804884882828001d40d070741c1c1c1c0c034140303209547d43d0f2340351031f1031700d403030b00c0c4c0c440300c030a12212200cec03200e9f070755079f41c1d0707070703030700c030303070700c0c82071f075070707175070f0707070b0707030307003000c0303070700700c0c0c0c0c0c281e00072959f2b0f0b 26 67108863 11 2047
def hc_68_12 : Nat → Nat := unpackHintV5 0xb1f116ac9956a509e49fb15697aa0290a1c28b295e8322027f40f87a31447301cc6b89de67590c63310a5ed1185b50e05741044f49fe4ae11a4331ec3b71f03b380e3aa8243339dc28ca9c2479141f813e1782001229560ca162049a02000126 0x155555555543c2c2c3d5556a6a95555543c1c1c1c4c3c3c4ea9555543d55540d65544d55555555550f0b0b0f5555a9aa555555550f1550fc0f030f033f2911555541c1c1c1c1c1c1c1eaa81c1ea955555555543c2c2c3d5556aa0ba7ea95555555613a37a80eaa5079f555550707070707070707aaaa0707a07a5555550f542d51503464456655655507555555511100c03115415554bc3cac2cac2cbc3c154044448800141555541c1c1c1c0303001c1c1c07078255555544440300c515151512b1302cac2c132844448803a7c03200c0d41e7d555541c1c1c1c03030070707070701e095555543d50b50540c0115537411801507555555511100c03044448803a7c885454545413a02e8038a5079f555550707070700c0c82a01c07a5555550f542d41503060056604045541d555555055455550f0f3f0b3f0b0f0f44440300ca050111122050500555555070707070300c0c01c1c03032095555545454545403030b00c0c4d11100c030a11112200cdc03200e9f5079f5555507070707030700c03030700c0c825555550f542d503410115415030600541d55555544440300c111122005555551313131300c0c8255555542d05060544d55555544440300c1111220045505555370f2b0b2b0b370f0550a00555550707070700c0c82007078a55555544440300c1111222200e9f5151515184ca0b20de2941e7d555541c1c1c1c0303208a81c1e81c95555543d50b50540c18014115590441d5555555555555555555543c2c2c3c3c0c3c0f030f155543c2c2c3c3c0f83c0f83c3c3c3d55541c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1d5555540100000404040400f002c000000000000005555070707070070000700c0015555540000000404040400b003c0000100004000005555070707070020001c0007555555555555555079f55555070707070707070707070707555555542d5540d595541d5555555555133b13555513133b3b55551307130713071307130713075555555555133b135555131b1b131b1b1b1b555551307130713071307130713075555555555555555555543c2c3c2c3c3c3c0c3c0f030f155543c2cbc2c3c3c3c0f83c0f83c3c3c3d55543c3c1c2c4c1c3c3c1c1c3c4c1c1c3c1c3c1c4c1c4c1d5555540100013001010101003c00b000000000000000155544c1c4c1c004c000c130005555555555555503030b555503030303030303030b0313555503330380c0c0e0b0b0b0b03030303555503130303030303070b070b0703030303130713075555555555555503030b555503030303030303030b03135555031b0380c0c0e0b0b0b0b030303035555503130303030303070b070b07030303031307130786b04e6b01c4d5555555555555542c4555550303030340c2c0c4c0c0d15155542c2c2c2c6b9ac80c0c0c0d5555542c1c2c1c4c4c0c0c0c0c0c0c0c0c0c0c4c1c4c1d555555555030355555035555555542d550b555503030b40d15155540c0c0c0c0c0c0c0c2c0c4d151955540ccc0e03030382c2c2c2c0c0c0c0d44d5541e7d5540c4c0c0c0c0c0c1c2c1c2c1c0c0c0c0c4c1c4c1c40415404415400f02c15400000000001000000004c001540813055130713070004c0155555555542c2c2c2d55560ba7eaaa9555555560ba37a80eaa55550b070b0713071307aaa81e13a55555546d5542c2d5542cbd55550345455550b0b0b0b4546555582e9faaaa58bd555569555555560ba37a80eaa513555079f5550b070b0713071307aaa81e13a55151515155555a911100302c030dc2c0b044440b1302ea0ba7c0155542c4c0702c1c1c2c1c2c1c071320955555415515555695511102c0b0cc0c0cc0c044440ba20ba7c1414015555542c1c2c1c4c4c02c2c1c01c4c8255555546d5441544142c545454550b5542d5556a40c14111100302c030dc2c0b0141844440b1302ea0ba7c0144d5541e7d5542c4c0702c1c1c2c1c2c1c071320955555511100c03044448803a7c885454545413a02e8038a55550f07130700c0c82a01c13a 24 16777215 10 1023
def hc_68_13 : Nat → Nat := unpackHintV5 0xfec0147bb8753b6c4e1c9b236dec0c36ac493b3e03058ab28ac010a95b1c9da98481541c14c96415447b46da0de5f8f3926c72f0db3368c2177e46ca6f2a04ad91421e4710e625206801622fd086152858085048838913e1470fb06787801f628c0001f6 0x9f9f130713550b0b550b9f90f0b42c2c12946c5c6c5d542240c440300c0300c0c00c0c048848828288803a7c1351f46c4d0f0b0b0f1313071313870700c0c82550b0b550b9f43c2d0b0b0b50f0f0f175540c440300c0300c0c00c0c048848828288803a7e1f1525285c60f282ca0f83c820f8800f8a1351f46c4d0f0b0b0f0f0f0f070f3b0f0700c0c82281e1321b1b1b1b0b0f0f0b2b0f0b0f0b0f0f1f0f43d0f0f0f43c3c3c5c3d000c0300c0300c00c00c0c00c0c08888a282828004c4c4c4c4c4c4c4c3c2c2c3c3c3c3c1c3c4c3c1c03032086c6c6c6cac3cac3c6c3c6c3c0000001f0101005c00f002c00000000027c0003337333b1b1b1b1b0f2b2b0f00001c130001b1b1b1b13131313131313130300c0300c0300c2222220013131344d131f1344c5c4c4c4d130f130b130b130f0030303030a00a130713130713130713071b130713131307003030a0a006c6c6c6cacac6c6c6c6c0c0300c0300c0308888888803a7e1f1929285c6282c88a3b3b1b1b1b1b3b2b2b00c0c82281e2550b1f50f0f43c3c2c8d0f0755070750f0f0f1750f0f0f0f50f43c3d0f0b0b0f0f030f03c0c3c1f51f48c8d0f0b0b0f0f03e0f03e0f0f0f0f1350741c4d0f0f070b1307507070f41c1c3c1c3c1c4c1c4c1d547d44d132341f000023000070101005c00f002c000000000000001350741c4d13071307001300031000550b50b42c2d030355070752317231750b0b0b02c0b0b0350340c0d0303030303030300c0c0c1f51f48c8d0b0b0b0b5f17e5f17e030303030350741c4d0b070b07503030340c0c0c0c0c0c4c1c4c1c1c1c1d544c4d44c5d40c0d540c7c0c0c0c0c0c4c0c0c0c0c0c0c4c0c4d40c5c0c0d42d42c2c2c2c2c2c2c2c2d0b0b40c0c2c0d40c0c0c0c0303031030340c0c0c0c0c0c0c0c2c0c4c7d47c4c1384c139232340ccc0e03030382c2c2c2c0c0c0c0d41e7d41c1d541c4d0303131303030303030307070b070b07030303031307130710001c170015502c000f1f51344c8d000000000000001f02300000040084d41d071344c1c4c1c0013000707075513135131750b50b0b0b0b0b0b0b0b0b42c2d1f51f13031304c0c4c46c6d0b0b0b0b968a8a6982e9faaaa87d56a1384eaa138bea96a17582e8eea03aa941e7d41c1d541c4d0b070b0713071307aaa81e13a550b50b42c2d0b0740070752317231750b0ba0b82c2c7c442302c0b0cc0c0cc0c04884882828002d41d071342c1c2c1d402d07007132081c1c1d544c4d44c5d40b510b1f02c02c4c2c0b00b130b1310b1702d42d42c2c2c2c2c2c2c2c2d0b0b6a1f104c0c04c0c108c00c0b00c3b0b02c120a0a2102c4c0ba82e9f005079f5070755071342c2c4c4c0702c1c2c1c1c2c1c2c1c07132081c1c1d544c5d46c5d47d43c4c2c3c3c4c2c3c3d0f1b40c4030300303040300c030482828848803a7c881f51a04c2a81f0aa1a05d413a02e8038a5079f5070755071343c1c4c1c030320a80704e9547d43d0f2340c440300c0300c0d001c1d48c5c8c5d43c3ccc2ccc2c3c3c280e0122122000a0a0350741c4d0f07130700c0c500340c8207070755131751f1751f50f130b0f0f130b0f0f43c8d00d440c7c030031f0300c00c4c0c4c40c5c03500c0c2c03031303100c0c00c0c100c0300c284828288488033300c803a7d41e7d41c1d541c4d0f0713070303131300c030303070700c0c8207070755131751f1751f513130b13130b131f44c8d1f51f13031f1f03131f48c8d133b131f51f131f1f87c4e48c8d13133b3b5079f5070755071344c1c4c1c4c1c4c1c4c1c4c1d555555555555540c4c0d55540c2c0e7c0c0c0c0c0c0c0d55543c2c2c3c0c0c0e033f0380c0c0c0d41e7d555541c1c1c1c0c0c0c1c0c1c0c0c0c0c0c0c1c1c1c1d5555543d50b540d035540d2b554540d1911507555555511100c2c0e7c0c0c0b5151515103030304c2c44440b02c000b20fc941e7d555541c1c1c1c03030070707070701c1c01d5555542d50b50540c011550b43c118015075555555555555542c54555550303454030340d5554fc3f8fc3f82c2c2c2c0c0c0c0d5555540c0c0c0c0c0c1c1c1c1c1c1c0c0c0c0c1c1c1c1d555555555555540c0c2d55540c0c0c0c0c0c0c0c2c0d55540cfc0e03030382c2c2c2c0c0c0c0d41e7d555540c1c0c0c0c0c0c1c1c1c1c1c0c0c0c0c1c1c1c1d5555540d5540d035542d50b54540d1911507555555511444c0303139f111100c03005079f555550303030301c1c1c4c0700755555503540d415130600541d55555544440300c5555550307070700c0c111102c0f0004c1355550f5505044d40155555544440300c4550555503035550550111102c0f0003780de41d55541c1c1c1c0303001c1c1c0707070075555554444030302c0c2c0d454554544c8c40c0c0c0b0b111102c0f0004c83f25079f555550707070700c0c01c1c1c1c1c1c4c1c07070075555550f542d415030045544d04600541d55555545505555a55544440f02c0f0300f030111122050500555507070707007070701c1c070720955555545454546a44440f02c00c3700c13111182e9f02e80b0b005079f555550707070701c1c1c1c1c0701c1c825555550f542d411551341015030600541d55555555550b0b0b0b555582e9faaaa5555555582e8dea03aa941e7d555541c1c1c1c1c1c1c1eaaa0781e95555542d50b54540d19115995592f5541d55055455555555a55544443f0303f0300b02c1111050522005555550701c1c01c1c1c1c1c1c070720954545454555556a444400c0b00c370b02c111102c4c0ba82e9f005079f55555070701c0707070707070701c1c825555550b41011550b542d415030600541d 25 33554431 11 2047
def hc_68_14 : Nat → Nat := unpackHintV5 0xe3b228de016cd5ea06cd821ac7598abe324ab59a26afc176a72a26a021c296726c8f31d089397e83417e7d797274da286ee97c66f1fe6019b6541b005348344d8172457a023e61c63213142bb9962511aa1c12401312400c89a207514e0001d4 0x5559f5555550b5543d551103050440300c5151517171055105515171712b4f02cac2c37284414186148803a7c03200c0d55175541d45d52f272b2700c0c0dc9c1cdcfc0782505450545552b0b2f0f2b0b2f0f5555505044440300c050511112200371327073713270755552f272b2700c0c8255555567d0b5543d55550305044440300c537105510515151512b4702cac2c372841416844448803a7c03200c0d335541d5554bc9cac9c03030372707374301e080551f1751f1751f51f1f0b1f0f1f0b1f0f48c8d0000000000000100111008c02b00ac0000000000000027c0001f51f1f1f1f071f331f0748c8d2b2b2b2b0000ec3b000015555550b5543d55540000000000041f1000010100ac02b0000000000000009f0001335541d5554acacacac0003b0ec0005c5d545c7d17546c023523170b170f170b170f46c5c5c5d0000000000008c04044400002b00ac0000000000000027c00023523173317071717170746c5c5c5d2b272b2700009c3b0004f1b471b0b0f0b0f0b0f0b0f0f1f0f43d0f0f0f43c3c3c5c3d000c0300c0300c00c00c0c00c0c088882082828004c4c4c4c4c4c4c4c3c2c2c3c3c3c3c1c3c4c3c1c0303208dc6cdc6c2c3c2c3c2c3c2c3c0000001f01011005c17003c0000000000013131313131313130f0b0b0f00001c130003f1b431b13131313131313130300c0300c0300c13131344d131f1344c5c4c4c4d130f130b130b130f0030303030222222000a0a130713071307130713071307003030020086c6cacbcacbc6cbcac6c0c0300c0300c0307c507c6d05c5c4ac0b2b0b0a22222200e9f00c803033b3b1b3b1b2f2b2b2f00c0c0ec1cec07820b0f0b550b0b50b17550b9f50b0b550b0b40c4030300303040300c030482828848803a7c881f51a02c2a80b0aa1a05d40ba02e8038a1f51f0b0b0b070b3b0b0746c6d0b0b0b0b00c0c82a01c13a5555555542d5542e7d55540c0c144111100c030141844448803a7c8841544168545454540ba02e8038a4ed550755550b0b0b0b00c0c82a01c13a1b1b1b1b0b0f0b0f0b0f0b0f07c04040170200000000000000000000000004c4c4c4c4c4c4c4c3c2c2c3c00704c000006c6c6c6c4c3c4c3c4c3c4c3c000000000000000401f005c0400b003c000000004c1c4c1c4c1c4c1c3c1c4c1c00000021b1b1b1b0f0f1b0f1b0f0300c0300c0300c22222200e9f2207e46868179280ba00e286c6c6c6c3c3c030320a807295567d5555542d550f5515151055105031715031715500c0c2c03034f4440c141100c030a1105061852200c6c03200e9f5545d5507517543c9cfc3c0cfc0300c0c1c0303209555555511100c030155015503c3d2c2d2c2c3c3c294044448803000c141555543c9cfc3c03030fc4c9c1cfc4c9c1e095555559f42d550f55551055105031515151500c0c2c03034740c14111100c030a050611112200c6c03200e9f4cd550755550f273f0f034300c03030700c0c82550350b42c2d031100c0300c0303400f0f5231723175050340c0a03804884880028287d47d232342c2c2c2c03030fc4cfc1cfc4cfc1e082c3c2d542c2d42c5d542e7d42c2d542c2d00d440c7c030030b0300c00c2c0c2c40c5c03500c0c2c0c2c03030b0303100c0c00c0c100c0300c284828288488032b00c803a7c7d47c2c2c2c1c2ccc2c1d232342c2c2c2c0c4c0300c0c1c030320a7c1cfc3c2c4e15555555511100c0301551555402c2c0c0c0c0a5011112200c800e9f050555550b0b0b0b00c0c3f1397073f1307825555555542d5542e7d55441544140c5454545403030b00c0c2d0305044440300c281418444488032b00c803a7d335541d55542c2c2c2c0c4c0300c0c1c0303209542d42d0b0340c440c030300c0308c7d548c7c03c3c0c0d0140d030280e0122122000a0a2352345c5d0b0b0b0b00c0c4b1327074b132707820b0b550b1f550b0b0f0b550b5542c2d42e7c0351031f00c00c2c0c2c030030b031031700d403030b030b00c0c2c0c0c4030300303040c030300c030a120a0a212200c6c03200e9f235230b330b070b0b0b0745c5d0b0b0b0b031300c03030700c0c820b0f0b550b0b42c5d03100c0c0303100c03550f0b0b0f43c3d2030482088400884d44c2c2c1c2c2c1d13134030303c3c3c3e082c2d42c7d542c2c3c0c4030300c0c40c030303d543c2c2c3d43c0d480c12082210022135130b0b070b0b0744c4d00c0c0f0f0f0f824f1b471b0b0f0b0f0f0b0f0f0b0f0300c0300c030300c0c0f1f0f43d0f0f0f43c3c3c5c3d00280e02222082000a0a13131313131313130f0b130b0f0f00c0c0f0f0f070f130f07823f1b431b130f130f130f130f131f1344d13131344c4c4c5c4d0f0f130b130b0f0f0300c0300c0300ca003808888882828004c4c1c4c1c4c1c4c4c1c3c3c1c4c1c3c000c0c0c0c8021b1b0f0f1b0f0f00c0d1031f1031700c0d00c0c2c03030300c0300c0300c288888880300c803a7c6c6c3c3c0c0300c0c1c0303209550b5555455055550f0f08a44440300c50501111220a050055550f0b0b0f131337071313370700c0c825550b9f555555555550f511100c0314103011112206052200e9f5151515183e0f282e0b2551058400f8a55550f0b0b0f541d3b500c0c82281e132 24 16777215 10 1023
def hc_68_15 : Nat → Nat := unpackHintV5 0xce798ac5fa20bf21b6b58a66ae49d0a809909e6a6897e1a28f721c89e1648219f27c018672ea4672302e6d593667199060c196575a5a51c1664bd97a4579983caa3436519631c1242b61982ac02824918c1d59ce17717a11099a06ca900001b2 0x371b371b0b0f0b0f0b0f0b0f000003c000f0101003c0800300000000000000004cdc4cec4cec4c6c3c2c2c3c0000703c000fc6d0c6c2c3c2c3c2c3c2c3c4c4c4d1344c7c4d1317131313681c1c2c1c3e0f03c0f03c0f02c0f0300f0302222220a0a0013071307130713070f0f070b070f00070f20086c6c2c3c2c3c2c3c2c3c7c507c6d05c5c6a0f03c0f03c0f02c00c00c222282e9f02e80b0b00131313131b0f0b0b0f04c1c4c0703c3c8201540c0d40c5d42d42c0c0c0c2c0c2c0c0d0b0b449f505500c0300c120a0a2102c9f0a0087d56a0380eaa038bea96a175002a030a87d47c0c0c0c1c0c4c0c0d1b1b42c2c2c2c030320aa078ee8055555550b0b5550b2f555550350127d1500c030141844440b27c280162f55555a55555555002a030a9135541d55542c2c2c2c030320aa078ee86c6c6c6c2c2c2c2c2c2c2c2c0000002c07c0404017000c00b0000000000000000ecdcdcec6c6c6c6c2c2c2c2c0000704c0006c6c6c6c2c2c2c2c2c2c2c2cecacecac6c6c6c6c2c2c2c2eaaaaaaa84c4c4d1344c7c4d131713131342c1c2c2c2c07071304c0c4c0c4ca88a13071307130713070b070b0b0b0713071307aaaa86c6c6c6c2c2c2c2c2c2c2c2cacac6c6c6c6c2c2c2c2eaaaa0ba7eaaaa1f99a9a85e60baa80eaa1b1b1b1b0b0b0b0b2b2baaa81ea5559f5554545441544142c5c542c5c555550b5542d56a4440c141100302c030dc2c0b04414186140b1b02ea0ba7c0155135541d45d50b3f01c0b0b070b0b0b0b09cfc825555555055405545a5544440b02c4b0304b030111102e20b05050055550b0b0b0b3f1327073f13270709cfc8255555567c41544142c545454550b5542d5556a40c14111100302c030dc2c0b0141844440b1b02ea0ba7c01135541d55542d0c0702c2c1c2c2c2c2c273f209542d42d0b0b4000148c5c8c5d40c0e80e030300000000000000000000001f51f48c8d0b0b0b0b3713370737133707000001540c0d40c5d40401f0000c0000c03005c042d42c0c0c0c2c0c2c0c0d0b0b42027c40400000c000000000000000000b27c007d47c0c0c0c1c0c4c0c0d232343b0001c2c2c2c2c00027c1cfc4c038555555000055555a5510000400000000000000b27c00000155542c2c2c2cfc4e6c1cfc4c1c0000055555500110010040404050b5542d55542104009f0040000000000000000000b27c01135541d55543b0001c2c2c2c2c0001542d42d0b0b0b0b48c7d548c7c00000c0e80e030300000000000000000000002352345c5d0b0b0b0b37132707371327070000030355031f55000401f0000c030000c005c042d42c0c2c0c0c0c0c0c2d0b0b0b0b42004104009f000c000000000000000000b27c008d48c0c4c0c0c0c0c0c1d171743b0001c2c2c2c2c0000055030340c5d0b50b030303030b0342c2d00400c0000000000000001f51f03030703030348c8d0b0b0b0b000003035031f55002d42c0c2c0c0c0c0d0b0b0b0b401003040000000000000008d48c0c0c0c0c0c1d171742c2c2c2c0000dc6cdc6c2c2c2c2c2c2c2c2c00000002c07c0404017000c080000000000000003b37373b1b3b3b1b0b0b0b0b03b0000704c000fc6d0c6c4c7c4d1344c4c4d131313171342c2c2c2c2c2c2c2e81c1c2e0b073b0ec1b0ec13030130300b02c22220a0a220013130713071307131307002c1c2c2c2c1c01c4c20086c6c0b0b442c7c42c5c0b0b42c2c2c2c2c2c2c2ea01b000c0b00c0b02c222202c0ba82e9f001b1b0b01c0b0b070b0b0b0b0825555550000000555555550000000000000000000055550f0b0b0f00131347071313470700555555127c00010004101003c00b00000000809f00000055555555000002030000a0800255550f0b0b0f00001c13000a81e3ba9f9f130713550b50f43c2d00127c0000030355a51b171b17500000000000002027c0000001351f46c4d0f0b0b0f0013130713138b0700550b50f43c2d00127c00000304017003c00b00000000809f00000087d5696a1750000000028200084d47d1b1343c2c2c3c0000704c002a078ee86c6c6c6c2c2c2c2c2c2c2c2c1f0101005c0800000000000000227c0000013131313131313130b0b0b0b001c13000001b1b1b1b0b0f0b0f0b0f0b0f000f0000f0003c040400f003c00300000000000000004cdc4cec4c6c4c6c3c2c2c3c0000703c0006c6c6c6c2c3c2c3c2c3c2c3c3cec3cec3c6c3c6c3c2c2c3eaaaaaaa84c4c4d1344c7c4d131713131343c07070b070f0f1303c0c3c0c4ca88a130713130713130713071b0f0f070b070f13070f0f0f07aaaa86c6c6c6c2c3c2c3c2c3c2c3c3c3c3c6c3c6c3c2c2c3eaaaaaa0ba7eaa1f99a9a85e6aa80eaa1313131b131b0f0b0b0f130f0faaa81ea 24 16777215 10 1023
def hc_68_16 : Nat → Nat := unpackHintV5 0xce59c2ca0914c00a80b849f0b3b126ad11a8a3227c9da1609759928fa1ee87e1f082c1487a422075094e6c024265919c5d99fe57219e5209464a51ee45f91641113a3aa19c34c97630a10a2c591223ea1c1e995416b1fa0eaa02089984000226 0x55101011555555540000c00c0c01555400b02c000000000000c00c0000049f000000000001555400704c00c9c0c0c0c0c0c1c2c2c2c2c000155454555555150b14444100312f0115a7c5445c8801555450749c49c9c9c9c272720917546c2d43d0f0b40c7d540c0d40c0c0c5d40031100c02c9f03030030303146127c14882828021f55a020fa82ea0380eaa038aea82a030544d48d171343c2c2c3c0c0c0c1c0d0c0c0c030320aa0784e917546c2d42d0b0b400000b27c001f0101005c00300040027c04000000021f55a020ba82e80000002820f00048d48d171742c2c2c2c0000710c002a0784e917546c0104002d42d0b0b400000000021f5a002aa0b80008d48d17174002c2c2c2c0281ea45d51b231f55231f5003142d42d0b0b42a280c440300c0c2800c81221090522002352345c5d57132707571327070b0b0b0b00c0c8245d51b030355031f50317030350b50b42c2d000c440300c0c0c0c0c00b051849f0500ca0aa220087d568080eaa80e03aa82ea0ba0a80c152352345c5d03430303030303070b0b0b0b00c0c82a81e13a45d51b0350340c0d0000000c9f040027c04008021f55a0203a80e8000011352345c4d030303030000a81e13a45d51b0b50f43c2d000000231f55231f0000000c0eaa80000100000000000004d48d171343c2c2c3c004c4c9c1c4c4c9c1c0117546c2d43d0f0b40000000b01f01011005c17000c0010009f010000000087d568083ea0ba0000000a080011352345c4d0f0b0b0f00001c43000a81e13a550b50f43c3c2c5d0f1f550f0f50f03c5d6a0f50f43c3d0f0b0b0f0f030f03c0c3c9669aaa8985aa1351344c4d0f0b0b0f0f0f0f070f130f070f0f0f0faa552352345c5d0000170001f0101005c00f002c0000000000000002352345c5d2b272b2700001c13000551351344c4d2352345c5d131313139669aaaa131355131f5131713144c3c4c2c4c2c4c3c4c1303130313162244c4d41c8d0717131344c1c4c4c4c1c4c1c9c4c4c1eaaaa45d51b2352345c5d2352345c5d9565a7e96aaaa1f55a85eaa0baaa03a548d48d171749c9c9c9eaaa07a80401b55080c0d540c7c00c0c000000c6d40c5c0c0d42d42c0b0002d0b0b400000000000c00c000100000127c000003200002352304c000745c5d03330303030303070b0b0b0b000005d445c6d56a23523170b05c0b171b45c5d23100305c0306d05c2f0146146969f220023523171b01c17170745c5d2f272709c825555555555555550111100b27c0c0c00c0c0c441449f220a0a005555010f542d50340d55034ad54150306555543c2c2c3c0c0c0c1c0c9c0c0c030320950744d5555555400000b27c004040404003000001027c000000015554042d50b500000005043c00155550b0b0b0b00001c27000541d1355555555455055550545444403030500310445142828880155549c4c9c1c9c4c9c1c2c2c2c2c0303209555555555555554044440303030303002c1105127c282888015554040d5540d035542d50b50540c19555503270303030303070b0b0b0b00c0c82541d13555555550000000c9f0001027c00015554040d503500000555540c0c0c0c000150744d5555555400000155540000003035550000000000000000055550f0b0b0f00131327071313270700555555500000002c1010110105c003000001027c000000015554043d50b5000000050400155550f0b0b0f00001c27000541d13555555555555555545555543c2c2c3c3c0c3c0f030f15556aaa2a2aa955543c2c2c3c3c3c3c1c3c4c3c1c3c3c3c3ea955555401040000404040400f002c00000000000000055552727272700001c130005555555555555555a7eaaa955555550b5550356555549c9c9c9c9c9c9c9ea950749d55567d5555542d550f55515151717105510551517171a91103050440f02c00c3700c3711050618582e9f02e80b0b005544d5507517543c2c2c3c3f1307133f01c0f0f20941514151555556955543c0c03c0c111103c0b01414444488004c4c9c1c4c4c9c1d55543c2c2c3c0f0f2095555559f42d550f555554710551051515151a90305044440f02c00c3700c3710505a111182e9f02e80b0b0044d550755550f0b0b0f10c4c1c4d0c0703c3c8201547c5d47c5d42d0f43c3c2c2c3e5a43c2d00100111008c080000000000000000000000002c9f0000004d44c4c4c4c1c4c4c4c1d131343c2c2c3c01304c00000055555542d559550f55107c40000404080000000000000000000000002c9f000001135541d55543c2c2c3c01304c000005c5d545c7d17546c00b50f5a0b0b0f90f0f0b43c230101110000200000000000000000000000000b27c0000013513131313071313130744c4c4c4d0f0b0b0f004c1300000 24 16777215 10 1023
def hc_68_17 : Nat → Nat := unpackHintV5 0x98c1769598ca9398809108a48b816287191a8299207e09247da01a7d281e7889287161ca6bd9626808f45e0a805661ea5219124bb998417a903c315238310037f01037702031498a29e1da2162201bc966134a200ee11a09496604d11e000134 0x155555555544c4c4c4d5556aaa9551555544c3c4c2c4c2c4c3c4c13031303132a2295555544c1c4c1c4c1c4c1eaa9555555555555a7d55556aaa955555550b555035655556a9507555555551110bc0444488015554bcbc2095555551110bc044514880155549c9c9c9c2727209555555555555554044440f00b00f0300f03011110820a0a0055550f0b130b0f0f0f0f0f070f130f0703c3c82555555004000ac00404040400f002c00000000000000055552b2b2b2b03b0000704c001555555555555540000000c00c00000000000000155540ccc0c0c0c0c0c1c2c2c2c2c0001555555555555540000000c00c000001000000000155540c9c0c0c0c0c0c1c2c2c2c2c00001c6f1301dbc4e1555555555555540000000003000000000041000000000155542c2c2c2c4dbc1dbc4c1c0000104001550030300000035555555502c000b5555000000000003003000000049f0400000000004c0007555503330303030303070b0b0b0b00005555555555130b130f130b130f5555130301303044441304c0a0a1111220001555544c4c1c4c1c4c01c4c20095544555542c45555500c4444442f011f155a7c51488011141d5554bcbc209542d43d0f0b40c7d540c0d40c0c0c5d40031100c02c9f0303003030305127c848828280005a85d60f83ea0b82ea0380eaa038aea82a030544d47d1b1343c2c2c3c0c0c0c1c0cfc0c0c030320aa0784e9542d42d0b0b400000b27c001f0101005c0030001027c000000000005a85d60ba82e80002030000a083c0011f51f46c6d0b0b0b0b00001c3f000a81e13a55004000b50b42c2d000000000001a85d0aa82e0001f51f46c6d000b0b0b0b00a07a9540c55051b171b1750b50b42c2d0a8a031100c03030a003204884241488007d47d1b1b58c4d8c1d8c4d8c1c2c2c2c2c0303209540c0d540c7d40c5c0c0d42d42d0b0b40031100c0303030303002c05127c8403282a8880005a85d603aaa0380eaa0b83ea0b82e822ba80e030547d47d1b1b40cfc0c0c0c0c0c1c2c2c2c2c030320aa0784e9540d40d03034000000327c0409f0000200016a17580ea03a00008011351f46c4d030303030000a81e13a550350340c0d0046c6d0303aa01027c00002001351f46c4d0303030313137b009f9f9f130713550b50f43c2d00000002c0000146c5c6c5d40c0eaa800000409f000000000004d47d1b1343c2c2c3c004c4c1c4c4dec1c01542d43d0f0b40000000b01f01011005c23000c000409f0000000000016a17583ea0ba0000000a080011351f46c4d0f0b0b0f00001c3f000a81e13a550b1f50f0f43c3c2c6d0f1f550f143c3c3c5d6a0f50f43c3d0f0f0b0b0f0f0f030f03c0c3c9669aaa8985aa1351344c4d0f0f0b0b130f0f0f0f070f130f070f0f0f0faa551f51f46c6d07c00006c002b01f0101005c00f002c0000000000000001f51f46c6d2b2b2b2b003b000704c001544d44d131347d47d1b1b44c4c4c4e59a6aaa84c55131f5131713135130f130b130b130f1304c0c4c0c4c588913135071f41c6c4c4d13071313130713073b131307aaaa9547d47d1b1b47d47d1b1b69569f69aaaa87e5a85d6a82eaa80e951f51f46c6daaa81ea55555555555555550111103c02c03c0c03c0c0444420828280155543c2c4c2c3c3c3c3c3c1c3c4c3c1c0f0f2095555540104002b001010101003c00b000000000000000155549c9c9c9c09c0001c13000555555555555550000000000c0000000000400000000055550b0b0b0b27132707271327070000 24 16777215 10 1023
def hc_68_18 : Nat → Nat := unpackHintV5 0xb658c8b15142acc124a9c0c0a1c20098027093b9129030e28ac15c87b0c481f1707c416c76c16070699666827a5fe1a858d1c453a14c4de96e4512363e01c43841703049fe29d19e24b9461d01ee18991a1528dc10693009e1a2041972000106 0x1540d40d030340000327c000000004d44d131340c0c0c0c0000055555555543d5540c0d5400000000000000000000000113551313130713131307550f0b0b0f0000550b50f43c2d00000002c004005c03000000000000001351344c4d0f0b0b0f00004c1300055555544440300c111102c0f0055550f0b0b0f00c0c1301b171755171f45d2345d23000d40d40c0c0c0c0c0d030303030340c010410009f00c9f0000000000000013513131313071313130744c4c4c4c4d13030303030000171755171f45d2345d23002d43d40c0c2c2c3c0d0b0f0f0b0b43c0000000000000b02301011100000030000000000000000000013513131313071313130744c4c4c4c4d130f0b0b0f00004c1300017231723030303030303030300000327c000000004c4c4c4c4c4c4c4c0c0c0c0c000005548d55235540d550340d400000000155135513131313030303030001175548d552342d55035543d0350000000000002c00000000000001135541d1355131313130f0b0b0f000055555015503035540d500000000551313131355030303030055555555015540c0d5550342d40000000000000b000000000000000551313131313131313541d1350f0b0b0f0000172317230b0f0b0f0b030b0f00000002c08c0004030000000000000013131313131313130f0b0b0f00004c13000171717170b0f0b0f0b030b0f0300c0300c0300c08c2305c1702c0f0013231323131713170f0b0b0f00c0c1303f1b4b1b0b0f0b0f0b0f0b0f00000001007c0170102000c000000000003c0000133f133f134b131b0f0b0b0f0004c000704c00fc9d0c9c2c3c2c3c2c3c2c3c0c0300c0300c0304c4c4d1344c7c4d131713131340c0c1c1c2c1c3c0c00c0c0c0c03f0fc4309c0b03c0004e01384c1c4c4c1c4c1c4c1c3c3c1c2c1c3c00c0c001300070b0f0b0f0b0f0b0f0300c0300c030302c0c2c0c7c507d05c5c40c0c0c0b0b0002c0f00082131313130f0b0b0f00c0c04c1c4c07130550b1f50f0f43c3c2c8d0f956943c3c3c5d400f1103c0f02c0f0300f03012210820a0a001351344c4d0f0b0b0f0f0f0f070f130f0703c3c82551f51f48c8d07c00008c0020101005c00f002c0000000000000001f51f48c8d2b2b2b2b00001c13000550b50b42c2d03956948c5c8c5d4000000000000000000000000007d47d232342c2c2c2d8c4d8c1d8c4d8c1c00008550105c00c0d540c7c0000c00c0c0140c5c0c0d42d42c00b02c10b0b400000000000c00c00049f000000000003200001f51f001c13048c8d03330303030303070b0b0b0b0000a55139544c5d44c4d44d44c4c2c4c3c4c2c4c3d131347c4130301303042304c1304828288488004c4d41c7c041c8c4c4d1307130701c4c802a9541751f1711f51f02c7c7c2c1f48c8d1f100300307d08c2f05a7c6852122001f51f07c7c1c7c0748c8d2f2f082555555555555550111100b27c0c0c00c0c0c49f05145220a0a000155550f542d50340d55034ad54150306555543c2c2c3c0c0c0c1c0cfc0c0c030320950744d555555400000b27c00404040400300027c04100000000000555542d50b500000005043c00155550b0b0b0b00001c3f000541d135555045555555550545444403030500310514514282888015554fc4cfc1cfc4cfc1c2c2c2c2c030320955555555555554044440303030303002c127c14514282888000555540d5540d035542d50b50540c195555033f0303030303070b0b0b0b00c0c82541d1355555550000000c9f027c04100000000555540d503500000555540c0c0c0c000150744d5555554000000004100000005543d54000155550f0b0b0f000055135555554000000000155540c0d5540000000000000000155543c2c2c3c004c4cdc1c4c4cdc1c015555540000000b04040440423000c0009f0104000000020000555543d50b5000000050400155550f0b0b0f00001c3f000541d1355555555545555555555543c2c2c3c3c0c3c0f030f15556aaa2a2aa955543c2c2c3c3c3c3c1c3c4c3c1c3c3c3c3ea95555540100000404040400f002c00000000000000055552b2b2b2b00001c13000 24 16777215 10 1023
def hc_68_19 : Nat → Nat := unpackHintV5 0xcd7924c5e9e4be11f6b282e4ac41909f8b2e96ba348daa4484ea307f097875e24a6ed1c469316863018c59427053916c4e594e4b10d245a95a4228e03dc11a3ac8be3770d63131902ab1a02720e42039ba17723212813c0c119c06f1480001bc 0x15400001555555540001555400000000000c00c0015554000c9c0c0c0c0c0c1c2c2c2c2c01555555555555540c0c2d55540c0c0c0c0c0c0c0c2c0d55540c6c0e03030382c2c2c2c0c0c0c0d55540c1c0c0c0c0c0c1c1c1c1c1c0c0c0c0c1c1c1c1d555544d555555555030303130303031355550b0b0b0b03030b55550303030303030303030303030b0313555513131313031b0380c0c0e0b0b0b0b0303030355567d5555555540c5d5555540d40c0d555555542c3d42c2d40c0c2d5555542b50303403030303030303030b035551b55165140c6c0e03030382c2c2c2c0c0c0c0d5548d55507513503270303030303070b0b0b0b030303031b1b1b1b3f1b4b1b07c040401700b0b0b0b0b0b0b0b0202c0000000000000000000b00000ccfcccfc6d2ccc6c00704c02c2c2c2c00003f274327131f1344d13131344c4c4c5c4d0b0b0b0b0b0b0b0b0b01c1c2c2c2c1c0c0c0c0c0c0c0c0c0c0c0c03030300c0c0c0cccfcccfc9d0ccc9c4c1384c1382c2c2c2c0c0c0c0c4c4c1c4c1c4c1c4c4c1c0c0c0c2c1c2c2c2c1c0c0c0c0c0c0c4c4c1c4c1c0c0c0d0340c7c0d031703030342c2c2c2c2c2c2c2c0c0c2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c2c0c0c0e03030382c2c2c2c0c0c0c0c0c0c0c0c0c0c1c2c2c2c2c0c0c0c0d5567d5555542d550f554440c141100c0c0b030b0351515171710551055151717103030302c2c44141845c502c0f000dc83f25544d5507517543c2c2c3c03030371307133f01c4c06d59f555555555543d0b544445040c00c0c0b030b0351515515231715510523231003030302c2c444418140b03c001b206c9555550744d43c2c2c3c03030271307132701c4c06d415117415415555540c0d5555414111100c03006e01b844440b03c004c4c9c1c4c4c9c1d55543c2c2c3c030304c06d5555559f50b0b5550f0f55555030305104444030302c0c2c0d4dc415441454554545c5c40c0c0c0b0b0506111102c0f000dc84b244d550755550f0b0b0f00c0c0dc4c1c4d0c071301b555504554108c5555550303035554444502c550030302c0c2c0c1111b1406e01b80b03c015548d513132707131327070f0b0b0f00c0c1301b5555554444030302c0c2c0d454554548c5c40c0c0c0b0b5151aa282aa255550f0b0b0f00c0c09c4c1c4c9c07aa5555554444030302c0c2c0d454554548c5c40c0c0c0b0b111102c0f0006c81b255550707070700c0c01c1c1c1c1c070700755567d5555555543c3d42c2d5111144140c0c00c0c0b030b03515155152317155105371003030302c2c4446c50584140b03c001b206c95548d555075131350f0b0b0f00c0c09c4c1c4c9c071301b5559f555555035540d40d54445c141445c0303379f110506117140300c0155135541d45d50303030304c4c1301b567d55555555550340d511448c5048c00c0cde7c444418140300c01555550744d40c0c0c0c131304c06d555555511445c373714111106c1b0055551327132704c4c1301b55555567d40c0d5540d55553705044511700c0cde7c141844440300c01135541d55540c0c0c0c131304c06d55555511448c3763379f14444441b06c0155544c9c4c9c131304c06d55515448d55503550337039f551111b141b06c0300d5548d513271327030303031301b55555544512300c0cde7d4546a8a155540c0c0c0c13132a955555511448c0303379f111100c030055550303030301c1c0700755567d5555540d5550350303544512314414dc00c0cde7c4446c50584140300c015548d555075131350303030304c4c1301b373737370f0f0f0f0f0f0f0f27c9f27c9f27c9f27c9f27c9f00c00000027c9f27c9f13131313131313130f0f0f0f27c9f27c9f0003030303030303030003039f0000c0300131313130303030304c4c13001547c5d47c5d40d0340c0c0c0c0c0d40c0d0303409f10100000327c00000000000004c4d44c4c4c4c4c1c4c4c4c1d131340c0c0c0c00000551f1751f1750b43d0f0f0b0b0f035030343c2d0000000000002c00100111002308c0030000000000000000000131351313131313071313130744c4d0f0b0b0f00004c1300001555555035540d550355104009f001000c9f0000000000000044d550744d55540c0c0c0c004c00015555550b5540d550f550000000000002c107c400004404000c0000000000000000001135541d1355550f0b0b0f00004c1300055555555015550340d550340d40009f100400c9f0000000000000055544d135541d13503030303000055555555015550f42d550342d40000000000000b0404000400105c030000000000000000000055544d135541d1350f0b0b0f00004c13000 24 16777215 10 1023
def hc_68_20 : Nat → Nat := unpackHintV5 0x80995a3eae679eae2a4eb6284710d2937105d9aea278cc92b061114e2dd8ac162c300a9b1ec4ef97825f262916e62c81428c3c311c1bf4890cde47061815c2dc0c014749b097032845598a1dd1370d1076052e5681f22940be0ec036ca100bc3e8000178 0x550b2350f0f42c3c3c2c5c2e7d0f1f550f0f50b0f03c5c3c5d40c0c0c0d40d030340c0c0c0c0c0d40c0340c2351b45c5d0f0b0b0f0f03e0f03e030303031351344c4d0f0b0b0f0f0f0f070f130f070303030313131313555540d5503030303030b50b555554500c0c0c0d540c0c0c0d542c2c2c2c0c0c0c0d540c0c0c0d542c2c2c2c0c0c0c0c6c6c6c6c1f010550105c08d43c00f02c10f1740000000000001b0005c00000023523001c13045c5d0f272f0f0000131f5513135513144c5d44d43c4c2c3c3c4c2c3c3d0f1340d40d40c0340c40c0d030303032351b1304e1304e45c5d0f13130f0303030313135072303030341c5c4c4d0f07130703030303030313071307030355031f550303172350f030b030303030343c5c5d0355035540c0d40e7c0c0c0c0c8d46c0c0e0303039171743c6c3c0c0c0c0c8d48c0c0c0c0c0c0c1d171743c9c3c0c0c0c0c6c9c6d5555555555555554044440300300303003030111102c0f00f803e0055550f0b0b0f0f0f0f070f130f0700c0c1301355555544515039f0300c515155142c417444441b06c00481b155552727272700c0c141d2711b01b5559f5555550b5543d55555540c5d555540c0d55540cdc0d550345455030b039f03030303030303554546517543c2c2c3c0c0c0e033f0380c0c0c0d55135541d45d50f0b0b0f03030307033f0303030303031327131b567d55555555550f42d5555555555540c0d40c8d540cdc0d555551034030b039f03030303030303555546450f0b0b0f03030380c6c0e030303035555541d1350f0b0b0f030303070327030303030303131b131b55555567d0b5543d555540cad555540c0d555555540cdc0d40c0d1542b5555030b039f03030303030303454655550f0b0b0f03030380d2c0e0303030344d550755550f0b0b0f0303030703430303030303031327131b555555555555550337035555030b039f030303030303035555aaaaaaaa55550f0b0b0f030303070327030303030303aa555555555555550337035555030b039f0303030303030355550f0b0b0f03030380c6c0e030303035555070707070303030703070303030303030707070755567d5555555543c3d42c2d5555555555540c0d40cad540cdc0d5555542b503034030b039f030303030303035551b551650bd43c2c2c3c0c0c0e031b0380c0c0c0d5548d555075131350f0b0b0f030303070327030303030303131b131b3f1b4b1b0b0f0b0f0b0f0b0f01007c0170102003c00000000000000000f000004cfc4cfc4d2c4c6c3c2c2c3c130001c0000fc9d0c9c2c3c2c3c2c3c2c3c4c4c4d1344c7c4d131713131343c07070b070f0f03030303030303030303030303030300c0c0c2f3f2f3f27432f270f0b0b0f1304e1304e0303030313071307130713070f0f070b070f030303030303030303130713070b0f0b0f0b0f0b0f031f0340d03030340c0c0c5c0d03030303030303030303030b039f030303030303032f2f2f2f0f0b0b0f03030380c0e03030303131313130f0b0b0f0303030703030303030303132f135559f5555550b5542d55110305044030b039f030302d454542c3c41544145440c0c0c370b110506117140b02c000b20fc955135541d45d50b0b0b0b00c0c02c2c1c2cfc071b01b567d55555555550b42d5111141030030b039f030302d45454545544142c3c400c0c0c370b1111060502c0b0002c81b25555541d1350b0b0b0b00c0c02c2c1c2c9c071b01b55555567d42c2d5542c3d5555030504444030b039f030302d42c3c415441454545440c0c0c370b0506111102c0b0002c84b244d550755550b0b0b0b00c0c02c2c1c2d0c071b01b5555554444030b039f030302d454545440c0c0c370b5151aa282aa255550b0b0b0b00c0c02c2c1c2c9c07aa5555554444030b039f030302d454545440c0c0c370b111102c0b0002c81b255550707070700c0c01c1c1c1c1c070700755567d5555555542c3d42c2d5111144140c0c00c2c0e7c0c0c0b51515151551050b0f100303030dc2c4446c50584140b02c000b206c95548d555075133b50b0b0b0b00c0c02c2c1c2c9c071b01b373737370b0b0b0b0b0b0b0b00000000c0307c0404401705c0030000000000000013131313131313130b0b0b0b00001c130003f1b4b1b0b0b0b0b0b0b0b0b00000001007c01701000c080000000002c000000ccfcccfc6d2ccc6c2c2c2c2c00130001c00fc9d0c9c2c2c2c2c2c2c2c2c0c0300c0300c0303c3c3d0f43c7c3d0f170f0f0f42c1c2c0c0c0c1c1c00c0c0c0c03f0fc4309c0b02c0003e00f84c1c4c1c4c1c4c1c2c1c2c2c2c1c00c0c00130070b0b0b0b0b0b0b0b0300c0300c030b039f030302c2c7c42d02c2d02c2c5c40c0c0c0b0002c0b0002c823b3b3b3b0b0b0b0b00c0c02c2c1c2c073b05559f5555555540c0d555540c5d540c5d555550b5542d540c0c2d55034545503030303030303030b03554546517540cfc0e03030382c2c2c2c0c0c0c0d55135541d45d5033f0303030303070b0b0b0b030303031b271b567d55555555555555540c8d40c0d55555550b42d40c0c2d55555103403030303030303030b0355554645031b0380c0c0e0b0b0b0b030303035555541d13503270303030303070b0b0b0b030303031b1b1b1b55555555555555550b11555540c0c0c0d030b03030345455550b0b0b0b5706e5706e0303030355550b0b0b0b5713270757132707030303031b271b55555567d40c0d555540d555555550b5542d55540c0c2d03454555503030303030303030b0345465555034b0380c0c0e0b0b0b0b0303030344d5507555503430303030303070b0b0b0b030303031b271b5555555555555550b02d15555540c0c0c0d030b03030303455055550b0b0b0b1b06e1b06e0303030355550b0b0b0b2713270727132707030303031b1b1b1b5555555555555503030b555503030303030303030b035555aaaaaaaa555503270303030303070b0b0b0b03030303aa 25 33554431 10 1023
def hc_68_21 : Nat → Nat := unpackHintV5 0xd9e14ccfba8ac63262c0896abb594cb1328aa7ea52a3a9109d9984938a848e41528432847bba1e75f17271d9066c117267b1185faa025b51165369fa4e893846221a40896638221a3149b62ae998226a201c51861479f60f31520749fa0001d2 0x550b50f43c2d01007c00b01020100000000000001700000f00004d48d171343c2c2c3c130001c001300550b50f43c2d131355131f5130b0b0b5507070b070f43d48d170f43c2c2c3c3c0c4c0f031308d46d171743c2c2c3c4c1384c138bc3c3c6c4d41d0717131343c3c1c2c1c3c3c3c3c4c1c3c1c4c1c9c4c4c1d542d543d42e7c2c2d45c7d543c5c2c2c2d50f52345c3d0f0b0b0f0f030f0f030f172351b45c5d0f0b0b0f0f171785c3e2f0f0f1b1352345c4d0f0b0b0f0f171307130f07130f0f271327131b550b50b42c2d08c00001727c000b01f0101001705c003010000000000000008d48d171742c2c2c2c0000704c0001f010550105c02d42c08410b0b40000000000001b0005c000b00008d48c00704c1171742c2c2c2c00004c7d544c4d544c3d44c5d42d42d41c1c2d0b0742c2d2352313031304c0c4c45c5d0b0b0b0b2351b1304e1304e45c5d0b0b0b0b2b1b331b1313507230b0b0b41c5c4c4d0b070b0b0b0713071307130713070b0b550b1f550b0b170b550b5542c2d42e7c8d48c2c0c2c2c2c0c2d17171742c2c2c2c8d46c2c2e0b0b0b9171742c2c2c2cac6c6c8d48c2c2c1c2c2c2c1d171742c2c2c2cac9c9c6c9c6d5555540104000f001010101003c00300000000000000155543c2c2c3c0000703c00155555542e7d5555545d55550f0b0b0f5503555550f0b0b0f5646d46c3c3c6d55543c2c2c3d50749d44c3c3c9c4c6c4c6d542c7d43c3d0f0f0b2343c7d543c50f0f0f1750303030350340c0d03030303030350300d0307d47d232343c2c2c3c3c0f83c0f80c0c0c0c4d44d131343c2c2c3c3c3c3c1c3c4c3c1c0c0c0c0c4c4c4c4c0401f5505c0047d43c0b0003d0f2340000000000001f0008c0000001f51f04c000748c8d0f2f2f0f0000131544c7d544c5d44c4d44d43c4c2c3c3c4c2c3c3d0f1340d40c0d03140c40c0d030303031f51f1304e1304e48c8d0f13130f0303030313135071f03030341c8c4c4d0f07130703030303030313071307031f035503035031751f50f030303030b030343c8d5039f5030355030340c0c0c0c7d47c0c0c0e03039232343c3c0c0c0c0c7d47c0c0c0c1c0c0c0d232343c3c0c0c0c0d555555555555554044440300300303003030111102c0f00f803e0055550f0b0b0f0f0f0f070f130f0700c0c1301355555500000001010101002c00f00000400000000015554bcacacbc00130001c0155555511100c031555555544c3c4c2c4c2c4c3c00c0c0c0c044441304c0004e0139555544c1c4c1c00c0c00130075555555039f514540300c554545142c41f444442b00048155553b2b2b00c0c141d13b055555555545555555555540c0c0c0c0c0c0c0c0c030303155543c2cbc2c3c3c3c0f83c0f80c0c0c0d55543c2c4c2c3c3c3c3c3c1c3c4c3c1c0c0c0c0c4c4c4c4c044004415400f02c15554000000000000400010003c00000704c155543cbcbc3c00004555555555130b0f0f130b0f0f555503030300c0c0c5555030303031304e1304e55550f13130f03030303555555543c3c1c4c1c3c0c0c0c0c0c0c4c4c1c4c1d555555542d555555503555039f55503030303555955543c3c0c0c0c0d5541d55543c3c0c0c0c0d542c7d43c3d0f0f0b2343c0d540c0d43c3c3c5d40031100c0300300303003030107c23100b00f00f803e001351344c4d0f0f0b0b130f0f0f0f070f130f0700c0c13013551f51f48c8d00000001000c01701002c00f00000007c08c002b0000001f51f48c8d2f2b2b2f0004c00070ec01544d44d131340c440300c0300c0d544c0d44c5c4c4d44c3c4c2c4c2c4c3c00c0c0c0c041f08c41304c0004e01384c4d41c7d0723131344c1c4c4c4c1c00c0c00130007551f51f48c8d030315039f40300c0300c0c0d4171f1711f02c7c2c1f1441f08c42b0001f2087d47d23234ecacac030301f1f071f01cec155550b5555550b55540c0c0303140c0c0c0c0d542c2c2c2d542c2c2c2c0c0c0c0d542c2c2c2d542c2c2c2c0c0c0c0c6c6c6c6d5555559f50b5555555550b45555540c0c0c0c0c0c0c0c0c030303155543c2c6c2c3c3c3c0f83c0f80c0c0c0d55543c2c4c2c3c3c3c3c3c1c3c4c3c1c0c0c0c0c4c4c4c4d555555555555542d55540e7d5540c0c0c0c0d5555591b50f1b1b0f030303035555541d2750f27270f030303031b1b1b1b550b50f43c3c2c5d0f1f550f0f503030f035000c440300c00c00c0c00c0c041b05c40b03c03e00f8004d44d131343c2c2c3c3c3c3c1c3c4c3c1c030304c04d548d48d171740000000401f000c0400b003c00000005c000000008d48d17174bc9cac9c00130001c1b00551351344c4d031100c0300c131355131f5130303035130f130b130b130f0030303030106c17104c1300013804e1350741c5c4c4d13071307003030004c001d548d48d171740c545039f030310300c171f1505c0c0c0c5c0b170b05c5106c17106c1b0005c822352345c5d3b272b2700c0c05c5c1c5c071b01b 24 16777215 10 1023
def hc_68_22 : Nat → Nat := unpackHintV5 0xab1a02a709049e223a9a010895e10890e93e8de8c089c9088748a08440c280a0e87c790a7679807131526c014c61da8a59621e55310c51190649a1de4421603fa91e3b69103381fa2ea13829216023b95a1912aa0ffa460b3930052186000148 0x5555555555130b130f130b130f555513031304c0c4c5555131313131304e1304e555513131313331b331b555555544c4c1c4c1c4c4c4c1c4c1c9c4c1c9c4c4c1d5555559f42d55555540d555555555955546c6c6c6d5541d55549c9c9c9c6c9c6d555555555555555555555550f0f0b0f0b0f0f0f0f030f03c0c3c55550f0f0b1b0b1b0f0f0f03e0f03e0f0f0f0f55550f0f0b130b130f0f0f0f0f070f130f070f0f0f0f1313131355555555550f0f0f0f55550f1b1b0f1b0f0f1b55550f13130f130f0f27131b131b55555555550b0b0b0b55550b0b0b0b1b1b1b1b55550b0b0b0b272727271b1b1b1b555555101010100ac02b01010101003c00b0000000000000000155549c9c9c9c02709c000704c0015555551110ac2b044441b06c0155549c9c9c9c272706c06d55555555540c0c0c0d55540c0c0c0c3c6c6c3d55540c0c0c0c3c9c9c3c6c6c6c6d55555555555556aaa955549c9c9c9c9c9c9c9ea9544446c555551b01b4444002f055551b01b2727272709c9c555555555555551b1b1b1b1b1b1b1b555507070707070707070707070755555235555544c4c4c4d55549c4c4c9c4cec4d55546c4c4c6c4c6c6c4c6c6c6c6d5559f55555555550b555555550355551b555651b51b1b1b1b1b1b1b1b5552355541d49d49c9c9c9c9c9c9c9c6c6c6c6d542d42d0b0b41f0000230002c07c0404017000c04000000000000001f51f48c8d0b0b0b0b00001c1300001007d54170010b50b100242c2d00000000000007c00230002c0001f51f04c000748c8d0b0b0b0b0000130f55131f5513175131350b50b0b42c1d41c1d0b0b47d47c4c0c4c1303131232342c2c2c2c7d47c4c1384c139232342c2c2c2cacecccac4c4d41c7c2c2c2d0723131342c1c2c2c2c1c4c1c4c1c4c1c4c1c2c7c2d542c2d42c5d542e7d42c2d542c2d1f51f0b030b0b030b0b48c8d0b0b0b0b1f51f0b0b0b82c2e48c8d0b0b0b0b2b2b1f51f0b0b0b070b0b0748c8d0b0b0b0b2b2b5555550040003c00404040400f000c0000000000000055550f0b0b0f00001c0f0005555550101010102003c000000000010000000f000155543c2c2c3c130001c0001555555555555543c3c1c1c2c1c3c3d55543c2c2c3c3c0c4c0f0313155543c2c2c3c4c1384c138bc3c3ced555543c3c1c2c1c3d513070f07130713075550b9f555555555551f555543c2c2c3d540d555543c2c2c3d5952f0f0f55550f0b0b0f541d5130f0f132f13555555004100000b04040404003002c00000000000000055550b0b0b0b03b0000704c0000440044154080b0555500000000000010000402c0000001c13055550b0b0b0b0000155555555542c2c1c1c2c2c2c1d55544c0c4c130313155542c2c2c2c4c1384c13955542c2c2c2cacecccad55555550b070b0b0b0713130713072b13130713075555555542d5542e7d5550355555542c2c2c2d55655550b0b0b0b2b2b5550755550b0b0b0b2b2b550b50f43c2d03c00003c03c000b0101003c0400300000000000000004d47d231343c2c2c3c003c001c0f000550b50f43c2d01002c01701020100000000000007c08c00003c00001351f48c4d0f0b0b0f04c00070004c01542d43d0f0b42c2d544c2d44c5c4c4d541c1c2c1c3d0f51f48c3d0f0b0b0f0f031303c0c4c1f51f48c8d0f0b0b0f1304e1304e2f0f0f3b13135071f41c8c4c4d0f0f070b070f0f0f0f13070f0f0f0713072f131307550b0b550b9f43c2d0b0b0b50f171f175543d47d230f43c2c2c3c3c0c3c3c0c3c7c7d47d232343c2c2c3c3c7c7e1f0f8bc3c3c4d47d231343c2c2c3c3c7c4c1c4c3c1c4c3c3c4cbc4d55555401049f000002c101011010003002c00000000000000055550b0b0b0b0270000704c00155555555550b9f5550b55555540d42c2c2c2d5555591b50b0b0b0b1b1b1b1b5555541d2750b0b0b0b272727271b1b1b1b550b50f43c2d00000f00f0003c040400b01000c000000000000001352345c4d0f0b0b0f00001c0f000 24 16777215 10 1023
def hc_68_23 : Nat → Nat := unpackHintV5 0xaf9388216c45de223d100011e 0x5559f5555550b5545d5555035545d555517556517546c6c6c6d55175541d45d5272727271b271b567d55555555552342d5555552340d55555591b51b1b1b1b1b1b1b1b5555541d23527272727272727271b1b1b1b55555555555555555555543c2c3c2c3c3c3c0c3c0f030f155543c2c2c3c3c0f83c0f83c3c3c3d55543c2c2c3c3c3c3c1c3c4c3c1c3c3c3c3c4c4c4c4d5555540100102b001010101003c00b0000000000000015554ac9cac9c0000704c000044004415400f02c15554000000000000400400006c00000704c15554bc9cbc9c001b00 20 1048575 9 511
def nh_68 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_68_23 (Nat.sub p 736)) (hc_68_22 (Nat.sub p 704)) (Nat.blt p 736)) (hc_68_21 (Nat.sub p 672)) (Nat.blt p 704)) (Bool.rec (Bool.rec (hc_68_20 (Nat.sub p 640)) (hc_68_19 (Nat.sub p 608)) (Nat.blt p 640)) (hc_68_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (hc_68_17 (Nat.sub p 544)) (hc_68_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_68_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (hc_68_14 (Nat.sub p 448)) (hc_68_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_68_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_68_11 (Nat.sub p 352)) (hc_68_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_68_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_68_8 (Nat.sub p 256)) (hc_68_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_68_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_68_5 (Nat.sub p 160)) (hc_68_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_68_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_68_2 (Nat.sub p 64)) (hc_68_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_68_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def f_68 : Nat → Nat × Nat := unpackForestF 0x62f80316ede6c36f261b78b6dbc1b4018af69b49b4da45a6d12d349369a48b4d225a6522d328969848b4c2200314ecf4b367955b3c2a802d7ecb47365935b2c1a802d6ec74c36396db1c36802d5ec347361935b0c1a802d4ec149200b4faf51cd7a4d6bd06a00b4bae528d72576b90ba00b47add1c802d0eb36b359955acc2a80297eaf49d57925abc1280296eab6c35596daac3680295ea749d53925a9c1280294ea46ab5234900527d4093aa024b5002500525d36d469b69b4d95da6c2e80291e9949c00a43a42b7d215ae90acf49958a4c2c52158e9026b480350051fd0d5be86ad743567a28ac51416286ac74323ea1892d0c094014773cd6f9e6b5d051c279acf3e4589f0ac4f85527c0b13e0549e6b1cf25367909a00a37942b7ca15ae754f9285679c52a4e2562710b12856399a2fccd16e6d6c1334579a1a44d0912682913404899a29ccc8f6506893234494137cc4d12504cf303449412fcbad125d4dd2825d9412e4b4d12504af2a34495d1a4a899a554692a25e9412aca09525024b2802500519c94d664a4b3264689291bc94154012bf1f34f8f9a5c8c5723e68f214549091a4844d23e6871f14e8f89f47c054012b71946c8ca30464d86324c31a57c8d2b846a0fe350671a4708c91bc641b4012af11b4f88da5c5a9722d2b911b4789e2a450d12298a91402b89c9a446d0e2329d1193e88c0a80254e1e6930f24987e2c43c8dc0129f0934f849a5c32972192b90934785a2a42c4d2126870914e8489f4240540129708237004a3c0cd3e066970615c819a3c131520926903343818a740c4f801286fed6f80dbe3fb59dfd6defeb677f5abbfa8e5fd06a0093f7e1b7bf0d9df827cfc0150049dbd35bdf58e0f4d677ce343d29bdf1066f84707a533bdd181e94aef5b6e7adab3d2905e909a0093779c9a3c0dade5056f2134781b1bc0539e027cf001500499bad5bddd4f8eb56775937bac99dd64aeeb24e759213ac0940125ee8c6f74633ba2539d102a0092b70ab7b9cdc1c2acee636870a37b9408dc96e0e146771db038515dc48dce2456709a13840f40124ee01446e635b7c0edbd288dcc636e4a73724f9b902a009236b5acb5a965b58d0d6a376b4aab5a4edb18d0d69376b495b5cda1ad24e0085f645a7b22d2da90b8c8b476962a34a4d1a5068c8b4368c2232293d91496d005c64523b3a4919d048c8a4366c1a3228fd91476cc04c6451bb2a49195048c8a33644273220f99104c0085b5ee362f71817b6c2bda6161ebe30f5c18827ec413361e382f68dd7b2dac257c5ec9db035f1818e0bd9375febe2f64ad7caf8be3705ec9380215d5a69ead34b5d8ae2ec1715a68eb84545c5a22e515171256b8034569a1adc1115a49ead24b5a8ae2d41715a48eb413f59c122b490d65068ad23f5691dac253161098ad23757ca7abc0915a466ad04e5681f2b4098010a6aab4955524aad1615546e0084f4fda7a7ed2d502b8a805c4fda3a9b1514d0689fb4352c2227e93d482b8a405c4fd23a8c0d13f47ea194c50c2627e8dd3f09c9f83e4fc1300212d3b46e9d9374ec9380211d3169e98b4b4dc2e262d1d348a89a0344c5a1a621393107c0084348ab7a5cdf122ace9136f489b3a44d5d2247294144488b5a4c511222c692144488ada444d40107e8b36f459b3a2c9bd164d68e57c45933a2c98d164768b2374581f22c098010767b56f44e381ed59d118d07b26f43c99a1d1c0f64ce864603d92ba12db9096ac7b24141e341ec5bd052b87b16b40abe2051c0f62ce8015c3d8b19fc570f62b67b1573e8b11f4568f629a7b12b3dda81ec49c0106e7a034371b59e44acf10686e3633bc121b89aced27e76024371319c45bce94f87116b39ebe1c459ce52d871a7438cb21c458ce10486e233370271b80f8dd2d46e026004199995bcd94f8665673313799899ccc4ae6624e331211a44d0cc2d668134330b199c4d0cc2b666125004179811bcc08ce6026f3013598d5f0c04ce602633012598091cc009c60026004159415bcbd6e0505672edb41411bcb92465c3702823396cd80a08ae59c6e2ce2b140d08b16d05016f2bca61405acacaf856370280b3954530a02c65414c280ad94055ca029652350280a3942588a12b45013d0041393c110868d64e13b26c2210d18c990484326b25ca792c090864c64616f24d3e1185ac91af84616723cb611a9d08d2c84616322c1210c90c8609c4303e21cb510c09801046421641e6379045f0798ce401641e5b78fc5f0796ce3e15c1e5a38f25387927c0081f1dc320d71bc750f835c671cc320d6dbc710f835b671bc2e0d6d1c6b09c3583e1ac1300206c39ade342700e6b38cc9a0398de3213b18d3807319c614c01cc5717d34072dbc5d2962e2700e5b38b4980396ae22e7f15ac00aca0045cee2356f148be0a45c046ace2316f13d3e08c5ac4daf82316712cb60929d0492c823163118ad88c55c454a01cb470e53587298c394b61ca4e0fa3707d158394841ca3e0e9b7074d5839464008170dc320051bc350880146b0c53e0625f0310f8014670bc2200518c2d0c80136f0ac1a004dac274f81397c09c3e004d9c2506801363009a7804d2c1f4b80f95c07c2e004d1c1b8a80db6406c1a004d0c076be0c12b05cb000ed5c074be0a13b04cb000e95c0b2be0595b03a3601c1b00b2ae0615402ca98145000746e0395b01ca9804490058cc0104e00db30040f8010260003f 10 11
def ch_68 : Nat → Bool := dagCheckNodeV5 fullMask g_68 ep_68 6 63 bds_68 740 (dagTraceF fullMask rootStock 11 f_68) cur_68 nh_68
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 fullMask g_68 ep_68 6 63 740 bds_68 (dagTraceF fullMask rootStock 11 f_68) (cur_68 0) (nh_68 0) rootStock 11 = true := by decide +kernel
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
theorem nb_68_14 : treeBlockF 448 480 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_15 : treeBlockF 480 512 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_16 : treeBlockF 512 544 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_17 : treeBlockF 544 576 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_18 : treeBlockF 576 608 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_19 : treeBlockF 608 640 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_20 : treeBlockF 640 672 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_21 : treeBlockF 672 704 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_22 : treeBlockF 704 736 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_23 : treeBlockF 736 740 ch_68 = true := by decide +kernel
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
theorem nj_68_14 : ∀ i, 0 ≤ i → i < 480 → ch_68 i = true := block_join nj_68_13 (fun _ h1 h2 => treeBlockF_at nb_68_14 h1 h2)
theorem nj_68_15 : ∀ i, 0 ≤ i → i < 512 → ch_68 i = true := block_join nj_68_14 (fun _ h1 h2 => treeBlockF_at nb_68_15 h1 h2)
theorem nj_68_16 : ∀ i, 0 ≤ i → i < 544 → ch_68 i = true := block_join nj_68_15 (fun _ h1 h2 => treeBlockF_at nb_68_16 h1 h2)
theorem nj_68_17 : ∀ i, 0 ≤ i → i < 576 → ch_68 i = true := block_join nj_68_16 (fun _ h1 h2 => treeBlockF_at nb_68_17 h1 h2)
theorem nj_68_18 : ∀ i, 0 ≤ i → i < 608 → ch_68 i = true := block_join nj_68_17 (fun _ h1 h2 => treeBlockF_at nb_68_18 h1 h2)
theorem nj_68_19 : ∀ i, 0 ≤ i → i < 640 → ch_68 i = true := block_join nj_68_18 (fun _ h1 h2 => treeBlockF_at nb_68_19 h1 h2)
theorem nj_68_20 : ∀ i, 0 ≤ i → i < 672 → ch_68 i = true := block_join nj_68_19 (fun _ h1 h2 => treeBlockF_at nb_68_20 h1 h2)
theorem nj_68_21 : ∀ i, 0 ≤ i → i < 704 → ch_68 i = true := block_join nj_68_20 (fun _ h1 h2 => treeBlockF_at nb_68_21 h1 h2)
theorem nj_68_22 : ∀ i, 0 ≤ i → i < 736 → ch_68 i = true := block_join nj_68_21 (fun _ h1 h2 => treeBlockF_at nb_68_22 h1 h2)
theorem nj_68_23 : ∀ i, 0 ≤ i → i < 740 → ch_68 i = true := block_join nj_68_22 (fun _ h1 h2 => treeBlockF_at nb_68_23 h1 h2)
theorem nc_68 : ∀ i, 0 ≤ i → i < 740 → ch_68 i = true := nj_68_23
theorem lb_68 : LowerBin fullMask rootStock g_68 12 :=
  lowerDagV5 (kn_cons lb_29 (kn_cons lb_45 (kn_cons lb_67 (kn_cons lb_65 (kn_cons lb_66 (kn_cons lb_63 (kn_cons lb_39 (kn_cons lb_37 (kn_cons lb_61 (kn_cons lb_28 (kn_cons lb_64 (kn_cons lb_50 (kn_cons lb_25 (kn_cons lb_33 (kn_cons lb_30 (kn_cons lb_35 (kn_cons lb_9 (kn_cons lb_36 (kn_cons lb_0 (kn_cons lb_38 (kn_cons lb_54 (kn_cons lb_32 (kn_cons lb_7 (kn_cons lb_24 (kn_cons lb_26 (kn_cons lb_21 (kn_cons lb_34 (kn_cons lb_22 (kn_cons lb_41 (kn_cons lb_49 (kn_cons lb_46 (kn_cons lb_53 (kn_cons lb_57 (kn_cons lb_43 (kn_cons lb_48 (kn_cons lb_62 (kn_cons lb_51 (kn_cons lb_60 (kn_cons lb_42 (kn_cons lb_47 (kn_cons lb_52 (kn_cons lb_58 (kn_nil))))))))))))))))))))))))))))))))))))))))))) rc_68 nc_68 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [0, 14]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [13, 16]⟩, ⟨GateOp.and, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008372896 * 2 ^ 32 + 3936397440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008372896 * 2 ^ 32 + 3936397440)) (13 - 1) := by
  rw [show canon fullMask (4008372896 * 2 ^ 32 + 3936397440) = g_68 by decide]
  exact lb_68

end PEqualNP.Outside.L_meta_48188

theorem PEqualNP.Outside.L_meta_48188 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372896 * 2 ^ 32 + 3936397440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372896 * 2 ^ 32 + 3936397440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48188.table2_from_lowerBin (4008372896 * 2 ^ 32 + 3936397440) 13 PEqualNP.Outside.L_meta_48188.root_lb PEqualNP.Outside.L_meta_48188.wg 18 rfl PEqualNP.Outside.L_meta_48188.wfits PEqualNP.Outside.L_meta_48188.weval
