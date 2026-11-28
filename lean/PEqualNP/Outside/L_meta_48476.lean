import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48476

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

def m_0 : Nat := 0x5500550000000000
def s_0 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_0 : Nat := 0x100150000000000
def ep_0 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_1 : Nat := 0x4444444400000000
def s_1 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_1 : Nat := 0x4044400000000
def ep_1 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_3 : Nat := 0xcccc
def s_3 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_3 : Nat := 0x44c
def ep_3 : Nat := 0x48000000000000040800000000000000000000000000000440
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

def m_4 : Nat := 0xa0a00000a0a
def s_4 : List Nat := [0x20200000202, 0xa0000000a, 0xa0a]
def g_4 : Nat := 0x20000020a
def ep_4 : Nat := 0x20800000000000000000000000200000008000000000000000000000002000002000000000000000000
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

def m_6 : Nat := 0x3000300030003000
def s_6 : List Nat := [0x1000100010001000, 0x300000003000, 0x30003000]
def g_6 : Nat := 0x100010003000
def ep_6 : Nat := 0x1000200000001000000020000000000000000000000000000000000000000000000000000000100010000000
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

def m_8 : Nat := 0x202020202020202
def s_8 : List Nat := [0x2000200020002, 0x20200000202, 0x2020202]
def g_8 : Nat := 0x200020202
def ep_8 : Nat := 0x2020000000002000002000000000200020000000000000000000000000000000000000000000000000000
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

def m_9 : Nat := 0x22002200220022
def s_9 : List Nat := [0x2000200020002, 0x2200000022, 0x220022]
def g_9 : Nat := 0x200020022
def ep_9 : Nat := 0x2002000000002000000200000000000000000000000020002000000000000000000000000000000000000
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

def m_10 : Nat := 0xa000a000a000a
def s_10 : List Nat := [0x2000200020002, 0xa0000000a, 0xa000a]
def g_10 : Nat := 0x20002000a
def ep_10 : Nat := 0x2000800000002000000080000000000000000000000000000000000000002000200000000000000000000
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

def m_11 : Nat := 0xa0a0a0a
def s_11 : List Nat := [0x2020202, 0xa000a, 0xa0a]
def g_11 : Nat := 0x2020a
def ep_11 : Nat := 0x2080000000000020008000000000000000000000000000202000000000000000000
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

def m_12 : Nat := 0x5500000055000000
def s_12 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_12 : Nat := 0x100000015000000
def ep_12 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_13 : Nat := 0xaa00aa
def s_13 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_13 : Nat := 0x2002a
def ep_13 : Nat := 0x280000000000000000000000000002000800000000000200200000000000000000
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

def m_14 : Nat := 0x4444000044440000
def s_14 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_14 : Nat := 0x4000004440000
def ep_14 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_15 : Nat := 0x5050000050500000
def s_15 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_15 : Nat := 0x10000010500000
def ep_15 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
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

def m_16 : Nat := 0xf00ff00f
def s_16 : List Nat := [0x50055005, 0x30033003, 0xf000f, 0xf00f]
def g_16 : Nat := 0x1007300f
def ep_16 : Nat := 0x20080000000000000000000000000000000000000000100230000000000010040000
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xba5d37b3a7b2d4e80f 7 127 3 7 6 63 9 511
def nh_16 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_16 : Nat → Nat × Nat := unpackForestF 0x1f6e87a3b1d4e80f 3 6
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 7 (dagTraceF m_16 s_16 4 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 7 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) (nh_16 0) s_16 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 7 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 7 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xcc330000cc33
def s_17 : List Nat := [0x441100004411, 0x3300000033, 0xc0300000c03, 0xcc33]
def g_17 : Nat := 0x41300000433
def ep_17 : Nat := 0x2000000000000000000000000000000000000004020000040000000000000000000000041000000400
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850932244890e8701 0x2a47d0f42927a8d9aa5991e1480f 7 127 3 7 6 63 10 1023
def nh_17 : Nat → Nat := unpackHintV5 0xe81b12e45c0a8912201400800f082e002 0x0 11 2047 5 31
def f_17 : Nat → Nat × Nat := unpackForestF 0x2a41e8767d06a1985e2d0a41480f 4 6
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 11 (dagTraceF m_17 s_17 4 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 11 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) (nh_17 0) s_17 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 11 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 11 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0x8822882288228822
def s_18 : List Nat := [0x22002200220022, 0x802080208020802, 0x882200008822, 0x88228822]
def g_18 : Nat := 0x200020022
def ep_18 : Nat := 0x2002000000002000000200000000000000000000000020002000000000000000000000000000000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_18 : Nat → List (Nat × Nat) := fun _ => []
def nh_18 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 0 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 0 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xc030c030c030c03
def s_19 : List Nat := [0x401040104010401, 0x3000300030003, 0xc0300000c03, 0xc030c03]
def g_19 : Nat := 0x1040304030403
def ep_19 : Nat := 0x402000000000402000000000000000000000000000000000000000000000000000000000001040004000400
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb4b4dd9a7655340f 7 127 3 7 5 31 8 255
def nh_19 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_19 : Nat → Nat × Nat := unpackForestF 0x3db43a3635340f 3 5
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 7 (dagTraceF m_19 s_19 4 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 7 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) (nh_19 0) s_19 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 7 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 7 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xcc330000cc330000
def s_20 : List Nat := [0x4411000044110000, 0x33000000330000, 0xc0300000c030000, 0xcc330000]
def g_20 : Nat := 0x11000004130000
def ep_20 : Nat := 0x402000000000000000000000000000000000000000000000402000000000000000000000011000004100000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2ca1cc2e82962242122000f 7 127 3 7 9 511 12 4095
def nh_20 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_20 : Nat → Nat × Nat := unpackForestF 0x1bab86931184c00f 3 6
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 7 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 7 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 7 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 7 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xcc33cc33
def s_21 : List Nat := [0x44114411, 0x330033, 0xc030c03, 0xcc33]
def g_21 : Nat := 0x4130433
def ep_21 : Nat := 0x200000000000000000000000000402040000000000000000000000000004100400
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850932244890e8701 0x2a47d0f42927a8d9aa5991e1480f 7 127 3 7 6 63 10 1023
def nh_21 : Nat → Nat := unpackHintV5 0xe81b12e45c0a8912201400800f082e002 0x0 11 2047 5 31
def f_21 : Nat → Nat × Nat := unpackForestF 0x2a41e8767d06a1985e2d0a41480f 4 6
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 11 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 11 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 11 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 11 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xcc33cc3300000000
def s_22 : List Nat := [0x4411441100000000, 0x33003300000000, 0xc030c0300000000, 0xcc3300000000]
def g_22 : Nat := 0x11041300000000
def ep_22 : Nat := 0x402000000000000000000000000000004020000000000000000000000000011041000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2ca1cc2e82962242122000f 7 127 3 7 9 511 12 4095
def nh_22 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_22 : Nat → Nat × Nat := unpackForestF 0x1bab86931184c00f 3 6
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 7 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 7 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 7 ch_22 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 7 → ch_22 i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_nil) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0x4444111144441111
def s_23 : List Nat := [0x111100001111, 0x404010104040101, 0x44001100440011, 0x44441111]
def g_23 : Nat := 0x4111104441111
def ep_23 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0x3c003c003c003c00
def s_24 : List Nat := [0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00]
def g_24 : Nat := 0x140014003400
def ep_24 : Nat := 0x1400200000001400000020000000000000000000000000000000000000000000000000000000140014000400
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0x8282828282828282
def s_25 : List Nat := [0x202020202020202, 0x82008200820082, 0x828200008282, 0x82828282]
def g_25 : Nat := 0x200020202
def ep_25 : Nat := 0x2020000000002000002000000000200020000000000000000000000000000000000000000000000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xc300c300c300c3
def s_26 : List Nat := [0x41004100410041, 0x3000300030003, 0xc3000000c3, 0xc300c3]
def g_26 : Nat := 0x1004300430043
def ep_26 : Nat := 0x42000000000042000000000000000000000000000000000000000000000000000000000001004000400040
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
def cur_26 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb4b4dd9a7655340f 7 127 3 7 5 31 8 255
def nh_26 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_26 : Nat → Nat × Nat := unpackForestF 0x3db43a3635340f 3 5
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 7 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 7 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26 : treeBlockF 0 7 ch_26 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 7 → ch_26 i = true := fun _ h1 h2 => treeBlockF_at nb_26 h1 h2
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_nil) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xc3c30000c3c3
def s_27 : List Nat := [0x414100004141, 0x30300000303, 0xc3000000c3, 0xc3c3]
def g_27 : Nat := 0x14300000343
def ep_27 : Nat := 0x20000000000000000000000004200000040000000000000000000000000000000000000014000000040
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
def cur_27 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850a14214072e0701 0x2946d1543d27a8d9ee4889a1580f 7 127 3 7 6 63 10 1023
def nh_27 : Nat → Nat := unpackHintV5 0xe81b12e4582b01602a1540988f202e002 0x0 11 2047 5 31
def f_27 : Nat → Nat × Nat := unpackForestF 0x2941e8761b974550623d05a1580f 4 6
def ch_27 : Nat → Bool := dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 11 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 11 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27 : treeBlockF 0 11 ch_27 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 11 → ch_27 i = true := fun _ h1 h2 => treeBlockF_at nb_27 h1 h2
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_nil) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xc3c30000c3c30000
def s_28 : List Nat := [0x4141000041410000, 0x303000003030000, 0xc3000000c30000, 0xc3c30000]
def g_28 : Nat := 0x101000001430000
def ep_28 : Nat := 0x42000000000000000000000000000000420000000000000000000000000000000000000101000001400000
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xbcbcde997251300f 7 127 3 7 5 31 8 255
def nh_28 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_28 : Nat → Nat × Nat := unpackForestF 0x3ebc393231300f 3 5
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 7 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 7 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 7 ch_28 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 7 → ch_28 i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_nil) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xc3c3c3c3
def s_29 : List Nat := [0x41414141, 0x3030303, 0xc300c3, 0xc3c3]
def g_29 : Nat := 0x1430343
def ep_29 : Nat := 0x2000000000000420040000000000000000000000000000000000000000001400040
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850a14214072e0701 0x2946d1543d27a8d9ee4889a1580f 7 127 3 7 6 63 10 1023
def nh_29 : Nat → Nat := unpackHintV5 0xe81b12e4582b01602a1540988f202e002 0x0 11 2047 5 31
def f_29 : Nat → Nat × Nat := unpackForestF 0x2941e8761b974550623d05a1580f 4 6
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 11 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 11 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 11 ch_29 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 11 → ch_29 i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_nil) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xc3c3c3c300000000
def s_30 : List Nat := [0x4141414100000000, 0x303030300000000, 0xc300c300000000, 0xc3c300000000]
def g_30 : Nat := 0x101014300000000
def ep_30 : Nat := 0x42000000000000004200000000000000000000000000000000000000000101014000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xbcbcde997251300f 7 127 3 7 5 31 8 255
def nh_30 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_30 : Nat → Nat × Nat := unpackForestF 0x3ebc393231300f 3 5
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 7 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 7 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 7 ch_30 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 7 → ch_30 i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_nil) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xc0c0c0c03030303
def s_31 : List Nat := [0x404040401010101, 0x3030303, 0xc000c00030003, 0xc0c00000303]
def g_31 : Nat := 0x4040401030303
def ep_31 : Nat := 0x400000002000004000000020000000000000000000000000000000000000004040401000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := []
def cur_31 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def nh_31 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_31 : Nat → Nat × Nat := unpackForestF 0x32db2432a32632532400f 3 9
def ch_31 : Nat → Bool := dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 7 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 7 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31 : treeBlockF 0 7 ch_31 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 7 → ch_31 i = true := fun _ h1 h2 => treeBlockF_at nb_31 h1 h2
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_nil) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xc0c0c0c030303030
def s_32 : List Nat := [0x4040404010101010, 0x30303030, 0xc000c000300030, 0xc0c000003030]
def g_32 : Nat := 0x4010103030
def ep_32 : Nat := 0x40000020200000004000000000000000000000000000000000000000000000004010100000
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
def cur_32 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850932244890e8701 0x292874f0e30248263e88c9929548502d109400f 7 127 3 7 10 1023 14 16383
def nh_32 : Nat → Nat := unpackHintV5 0xe81b12e45c0a8912201400800f082e002 0x0 11 2047 5 31
def f_32 : Nat → Nat × Nat := unpackForestF 0x292818f863274f0529148442d28c0920109400f 4 10
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 11 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 11 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32 : treeBlockF 0 11 ch_32 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 11 → ch_32 i = true := fun _ h1 h2 => treeBlockF_at nb_32 h1 h2
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_nil) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xcc00cc00330033
def s_33 : List Nat := [0x44004400110011, 0x330033, 0xc000c00030003, 0xcc00000033]
def g_33 : Nat := 0x4004400130033
def ep_33 : Nat := 0x40000000200000000000000000000400000002000000000000000000000004004400100000
def bds_33 : List (Nat × List Nat × Nat × Nat) := []
def cur_33 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def nh_33 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_33 : Nat → Nat × Nat := unpackForestF 0x32db2432a32632532400f 3 9
def ch_33 : Nat → Bool := dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 7 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 7 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33 : treeBlockF 0 7 ch_33 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 7 → ch_33 i = true := fun _ h1 h2 => treeBlockF_at nb_33 h1 h2
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_nil) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xcc00cc0033003300
def s_34 : List Nat := [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300]
def g_34 : Nat := 0x40011003300
def ep_34 : Nat := 0x400000022000000000000000000000004000000000000000000000000000000040011000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := []
def cur_34 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850932244890e8701 0x292874f0e30248263e88c9929548502d109400f 7 127 3 7 10 1023 14 16383
def nh_34 : Nat → Nat := unpackHintV5 0xe81b12e45c0a8912201400800f082e002 0x0 11 2047 5 31
def f_34 : Nat → Nat × Nat := unpackForestF 0x292818f863274f0529148442d28c0920109400f 4 10
def ch_34 : Nat → Bool := dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 11 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 11 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34 : treeBlockF 0 11 ch_34 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 11 → ch_34 i = true := fun _ h1 h2 => treeBlockF_at nb_34 h1 h2
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_nil) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xcccc000033330000
def s_35 : List Nat := [0x4444000011110000, 0x33330000, 0xc0c000003030000, 0xcc000000330000]
def g_35 : Nat := 0x4000011130000
def ep_35 : Nat := 0x4000000020000000400000002000000000000000000000004000011100000
def bds_35 : List (Nat × List Nat × Nat × Nat) := []
def cur_35 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def nh_35 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_35 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_35 : Nat → Bool := dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 7 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 7 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35 : treeBlockF 0 7 ch_35 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 7 → ch_35 i = true := fun _ h1 h2 => treeBlockF_at nb_35 h1 h2
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_nil) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xc0c03030c0c0303
def s_36 : List Nat := [0x404010104040101, 0x30300000303, 0xc0003000c0003, 0xc0c0303]
def g_36 : Nat := 0x4010304040303
def ep_36 : Nat := 0x400020000000000000000000004000200000000000000000000000000000000000000000004010004040000
def bds_36 : List (Nat × List Nat × Nat × Nat) := []
def cur_36 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb25935b2a73294c80f 7 127 3 7 6 63 9 511
def nh_36 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_36 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
def ch_36 : Nat → Bool := dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 7 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 7 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36 : treeBlockF 0 7 ch_36 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 7 → ch_36 i = true := fun _ h1 h2 => treeBlockF_at nb_36 h1 h2
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_nil) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xc0c03030c0c03030
def s_37 : List Nat := [0x4040101040401010, 0x303000003030, 0xc0003000c00030, 0xc0c03030]
def g_37 : Nat := 0x101000403030
def ep_37 : Nat := 0x40202000000000000000000000000000400000000000000000000000000000000000000000101000400000
def bds_37 : List (Nat × List Nat × Nat × Nat) := []
def cur_37 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850a14214072e0701 0x282868c142030f263e88c9d2d4494829108400f 7 127 3 7 10 1023 14 16383
def nh_37 : Nat → Nat := unpackHintV5 0xe81b12e4582b01602a1540988f202e002 0x0 11 2047 5 31
def f_37 : Nat → Nat × Nat := unpackForestF 0x282818f863214b5630508052530f0429108400f 4 10
def ch_37 : Nat → Bool := dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 11 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 11 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37 : treeBlockF 0 11 ch_37 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 11 → ch_37 i = true := fun _ h1 h2 => treeBlockF_at nb_37 h1 h2
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_nil) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xcc003300cc0033
def s_38 : List Nat := [0x44001100440011, 0x3300000033, 0xc0003000c0003, 0xcc0033]
def g_38 : Nat := 0x4001300440033
def ep_38 : Nat := 0x40002000000000000000000000000000000000000400020000000000000000000000000004001000440000
def bds_38 : List (Nat × List Nat × Nat × Nat) := []
def cur_38 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb25935b2a73294c80f 7 127 3 7 6 63 9 511
def nh_38 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_38 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
def ch_38 : Nat → Bool := dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 7 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 7 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38 : treeBlockF 0 7 ch_38 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 7 → ch_38 i = true := fun _ h1 h2 => treeBlockF_at nb_38 h1 h2
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_nil) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xcc003300cc003300
def s_39 : List Nat := [0x4400110044001100, 0x330000003300, 0xc0003000c000300, 0xcc003300]
def g_39 : Nat := 0x110004003300
def ep_39 : Nat := 0x400220000000000000000000000000000000000000000000400000000000000000000000000110004000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := []
def cur_39 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850a14214072e0701 0x282868c142030f263e88c9d2d4494829108400f 7 127 3 7 10 1023 14 16383
def nh_39 : Nat → Nat := unpackHintV5 0xe81b12e4582b01602a1540988f202e002 0x0 11 2047 5 31
def f_39 : Nat → Nat × Nat := unpackForestF 0x282818f863214b5630508052530f0429108400f 4 10
def ch_39 : Nat → Bool := dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 11 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 11 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39 : treeBlockF 0 11 ch_39 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 11 → ch_39 i = true := fun _ h1 h2 => treeBlockF_at nb_39 h1 h2
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_nil) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xcccc333300000000
def s_40 : List Nat := [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000]
def g_40 : Nat := 0x4111300000000
def ep_40 : Nat := 0x4000200000000000400020000000000000000000000000004111000000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := []
def cur_40 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def nh_40 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_40 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_40 : Nat → Bool := dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 7 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 7 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40 : treeBlockF 0 7 ch_40 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 7 → ch_40 i = true := fun _ h1 h2 => treeBlockF_at nb_40 h1 h2
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_nil) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0x4444444411111111
def s_41 : List Nat := [0x11111111, 0x404040401010101, 0x44004400110011, 0x444400001111]
def g_41 : Nat := 0x4044411111111
def ep_41 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xf0f000000000f0f0
def s_42 : List Nat := [0x5050000000005050, 0x3030000000003030, 0xf00000000000f0, 0xf0f0]
def g_42 : Nat := 0x10000000003070
def ep_42 : Nat := 0x10000000000040000000000000000000100000000030200010000000000040
def bds_42 : List (Nat × List Nat × Nat × Nat) := []
def cur_42 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb1e54b327d13969924c4a6000f 7 127 3 7 10 1023 13 8191
def nh_42 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_42 : Nat → Nat × Nat := unpackForestF 0x33eb2c33933233133000f 3 9
def ch_42 : Nat → Bool := dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 7 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 7 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42 : treeBlockF 0 7 ch_42 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 7 → ch_42 i = true := fun _ h1 h2 => treeBlockF_at nb_42 h1 h2
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_nil) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xff00ff0000000000
def s_43 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_43 : Nat := 0x100150000000000
def ep_43 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xffff000000000000
def s_44 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_44 : Nat := 0x115000000000000
def ep_44 : Nat := 0x14000000000000010400000000000001100000000000000115000000000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xffff00000000
def s_45 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_45 : Nat := 0x155700000000
def ep_45 : Nat := 0x4200000000000004020000000000001002000000000000155400000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := []
def cc_45_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_45_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_45 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_45_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_45_0 p) (Nat.blt p 32)
def hc_45_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_45_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_45_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_45 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_45_2 (Nat.sub p 64)) (hc_45_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_45_0 p) (Nat.blt p 32)
def f_45 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
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

def m_46 : Nat := 0xf0f0f0f000000000
def s_46 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_46 : Nat := 0x10105000000000
def ep_46 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xcccccccc00000000
def s_47 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_47 : Nat := 0x4044400000000
def ep_47 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0x3333333300000000
def s_48 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_48 : Nat := 0x111111300000000
def ep_48 : Nat := 0x1002000000000010000200000000010000020000000000000000000000000111111000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
def cc_48_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_48_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_48 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_48_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_48_0 p) (Nat.blt p 32)
def hc_48_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_48_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_48_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_48 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_48_2 (Nat.sub p 64)) (hc_48_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_48_0 p) (Nat.blt p 32)
def f_48 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_48 : Nat → Bool := dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 64 (dagTraceF m_48 s_48 5 f_48) cur_48 nh_48
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 64 bds_48 (dagTraceF m_48 s_48 5 f_48) (cur_48 0) (nh_48 0) s_48 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 ch_48 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 64 ch_48 = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 64 → ch_48 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 64 → ch_48 i = true := nj_48_1
theorem lb_48 : LowerBin m_48 s_48 g_48 6 :=
  lowerDagV5 (kn_nil) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xaa00aa00aa00aa
def s_49 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_49 : Nat := 0x20002002a
def ep_49 : Nat := 0x2002800000002000000280000000000000000000000020002000800000002000200200000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_13, s_13, 4, g_13), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10)]
def cc_49_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_49_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_49 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_49_1 (Nat.sub p 32)) (cc_49_0 p) (Nat.blt p 32)
def hc_49_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_49_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_49 : Nat → Nat := fun p => Bool.rec (hc_49_1 (Nat.sub p 32)) (hc_49_0 p) (Nat.blt p 32)
def f_49 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_49 : Nat → Bool := dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 43 bds_49 (dagTraceF m_49 s_49 6 f_49) (cur_49 0) (nh_49 0) s_49 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 ch_49 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 43 ch_49 = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 43 → ch_49 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 43 → ch_49 i = true := nj_49_1
theorem lb_49 : LowerBin m_49 s_49 g_49 7 :=
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_13 (kn_cons lb_9 (kn_cons lb_10 (kn_nil))))) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0x33003300330033
def s_50 : List Nat := [0x11001100110011, 0x3000300030003, 0x3300000033, 0x330033]
def g_50 : Nat := 0x11001300130033
def ep_50 : Nat := 0x2002000000002000000200000000000000000000000020002000000000000000000000011001000100000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x5050505050505050
def s_51 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_51 : Nat := 0x10105010501050
def ep_51 : Nat := 0x1040000000001040000000000010004000400040000000000000000000101000100010000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x5555555500000000
def s_52 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_52 : Nat := 0x115155500000000
def ep_52 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_5, s_5, 4, g_5), (m_2, s_2, 4, g_2), (m_1, s_1, 4, g_1)]
def cc_52_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_52_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_52 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_52_1 (Nat.sub p 32)) (cc_52_0 p) (Nat.blt p 32)
def hc_52_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_52_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_52 : Nat → Nat := fun p => Bool.rec (hc_52_1 (Nat.sub p 32)) (hc_52_0 p) (Nat.blt p 32)
def f_52 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 43 (dagTraceF m_52 s_52 6 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 43 bds_52 (dagTraceF m_52 s_52 6 f_52) (cur_52 0) (nh_52 0) s_52 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_0 : treeBlockF 0 32 ch_52 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_1 : treeBlockF 32 43 ch_52 = true := by decide +kernel
theorem nj_52_1 : ∀ i, 0 ≤ i → i < 43 → ch_52 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_52_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_52_1 h1 h2)
theorem nc_52 : ∀ i, 0 ≤ i → i < 43 → ch_52 i = true := nj_52_1
theorem lb_52 : LowerBin m_52 s_52 g_52 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_5 (kn_cons lb_2 (kn_cons lb_1 (kn_nil))))) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x3030303030303030
def s_53 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_53 : Nat := 0x10101010103030
def ep_53 : Nat := 0x1000202000001000000020200010000000000000000000000000000000000000000000000010101010100000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xcccc0000cccc
def s_54 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_54 : Nat := 0x4440000044c
def ep_54 : Nat := 0x800000000000000000000004000000048000004000000040800000000000000000000044400000440
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x3333000033330000
def s_55 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_55 : Nat := 0x111000011130000
def ep_55 : Nat := 0x1002000000000000000000000010000000020000010000000002000000000000000000000111000011100000
def bds_55 : List (Nat × List Nat × Nat × Nat) := []
def cc_55_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_55_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_55 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_55_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_55_0 p) (Nat.blt p 32)
def hc_55_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_55_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_55_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_55 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_55_2 (Nat.sub p 64)) (hc_55_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_55_0 p) (Nat.blt p 32)
def f_55 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 64 (dagTraceF m_55 s_55 5 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 64 bds_55 (dagTraceF m_55 s_55 5 f_55) (cur_55 0) (nh_55 0) s_55 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 32 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_1 : treeBlockF 32 64 ch_55 = true := by decide +kernel
theorem nj_55_1 : ∀ i, 0 ≤ i → i < 64 → ch_55 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_55_1 h1 h2)
theorem nc_55 : ∀ i, 0 ≤ i → i < 64 → ch_55 i = true := nj_55_1
theorem lb_55 : LowerBin m_55 s_55 g_55 6 :=
  lowerDagV5 (kn_nil) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0x5555000055550000
def s_56 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_56 : Nat := 0x115000015550000
def ep_56 : Nat := 0x1440000000000000000000000014000000400000010400000400000001100000100000000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_12, s_12, 4, g_12), (m_15, s_15, 4, g_15), (m_14, s_14, 4, g_14)]
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_56_1 (Nat.sub p 32)) (cc_56_0 p) (Nat.blt p 32)
def hc_56_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_56_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_56 : Nat → Nat := fun p => Bool.rec (hc_56_1 (Nat.sub p 32)) (hc_56_0 p) (Nat.blt p 32)
def f_56 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 43 bds_56 (dagTraceF m_56 s_56 6 f_56) (cur_56 0) (nh_56 0) s_56 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 43 ch_56 = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 43 → ch_56 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 43 → ch_56 i = true := nj_56_1
theorem lb_56 : LowerBin m_56 s_56 g_56 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_12 (kn_cons lb_15 (kn_cons lb_14 (kn_nil))))) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0x5500550055005500
def s_57 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_57 : Nat := 0x100150015001500
def ep_57 : Nat := 0x1400000000001400000000000000000000000000010004000400040001001000100010000000000000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) (nh_57 0) s_57 4 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 4 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xff000000ff
def s_58 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_58 : Nat := 0x570000007f
def ep_58 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000005400000040
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def nh_58 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 0 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) (nh_58 0) s_58 4 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 0 (dagTraceF m_58 s_58 4 f_58) cur_58 nh_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xf0f00000f0f
def s_59 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]
def g_59 : Nat := 0x5070000070f
def ep_59 : Nat := 0x20800000000000000000000000200000008000000000000000000000002000002000000050400000400
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def nh_59 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 0 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) (nh_59 0) s_59 4 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 0 (dagTraceF m_59 s_59 4 f_59) cur_59 nh_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xcccc0000cccc0000
def s_60 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_60 : Nat := 0x4000004440000
def ep_60 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000004000004440000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 4 f_60) (cur_60 0) (nh_60 0) s_60 4 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 4 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xaaaa0000aaaa
def s_61 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_61 : Nat := 0x20000222a
def ep_61 : Nat := 0x222800000000000000000000000200000008000000020000000800000002000022200000000000000000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def nh_61 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 0 bds_61 (dagTraceF m_61 s_61 4 f_61) (cur_61 0) (nh_61 0) s_61 4 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 0 (dagTraceF m_61 s_61 4 f_61) cur_61 nh_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0x3300330033003300
def s_62 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_62 : Nat := 0x100110011003300
def ep_62 : Nat := 0x1000220000001000000022000000000000000000010000000000000000000000000000000100110011000000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def nh_62 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 1 1 0 bds_62 (dagTraceF m_62 s_62 4 f_62) (cur_62 0) (nh_62 0) s_62 4 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_62 g_62 ep_62 1 1 bds_62 0 (dagTraceF m_62 s_62 4 f_62) cur_62 nh_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xf000f000f000f000
def s_63 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_63 : Nat := 0x100010003000
def ep_63 : Nat := 0x1000200000001000000020000000000000000000000000000000000000001000100030000000100010000000
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_63 : Nat → List (Nat × Nat) := fun _ => []
def nh_63 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 1 1 0 bds_63 (dagTraceF m_63 s_63 4 f_63) (cur_63 0) (nh_63 0) s_63 4 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_63 g_63 ep_63 1 1 bds_63 0 (dagTraceF m_63 s_63 4 f_63) cur_63 nh_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xf000f000f000f00
def s_64 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_64 : Nat := 0x100050005000700
def ep_64 : Nat := 0x400020000000400000002000000000000000000000000000000000001000000000002000100050005000400
def bds_64 : List (Nat × List Nat × Nat × Nat) := []
def cc_64_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_64_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_64 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_64_0 p) (Nat.blt p 32)
def hc_64_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_64_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_64_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_64 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_64_2 (Nat.sub p 64)) (hc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_64_0 p) (Nat.blt p 32)
def f_64 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 1 1 bds_64 64 (dagTraceF m_64 s_64 5 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 1 1 64 bds_64 (dagTraceF m_64 s_64 5 f_64) (cur_64 0) (nh_64 0) s_64 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : treeBlockF 0 32 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_1 : treeBlockF 32 64 ch_64 = true := by decide +kernel
theorem nj_64_1 : ∀ i, 0 ≤ i → i < 64 → ch_64 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_64_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_64_1 h1 h2)
theorem nc_64 : ∀ i, 0 ≤ i → i < 64 → ch_64 i = true := nj_64_1
theorem lb_64 : LowerBin m_64 s_64 g_64 6 :=
  lowerDagV5 (kn_nil) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xcc00cc00cc00cc
def s_65 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_65 : Nat := 0x400440044004c
def ep_65 : Nat := 0x40000800000040000000080000000000000000000400000000000800000000000000000004004400440040
def bds_65 : List (Nat × List Nat × Nat × Nat) := []
def cc_65_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_65_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_65 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_65_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_65_0 p) (Nat.blt p 32)
def hc_65_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_65_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_65_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_65 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_65_2 (Nat.sub p 64)) (hc_65_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_65_0 p) (Nat.blt p 32)
def f_65 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_65 : Nat → Bool := dagCheckNodeV5 m_65 g_65 ep_65 1 1 bds_65 64 (dagTraceF m_65 s_65 5 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 1 1 64 bds_65 (dagTraceF m_65 s_65 5 f_65) (cur_65 0) (nh_65 0) s_65 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_0 : treeBlockF 0 32 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_1 : treeBlockF 32 64 ch_65 = true := by decide +kernel
theorem nj_65_1 : ∀ i, 0 ≤ i → i < 64 → ch_65 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_65_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_65_1 h1 h2)
theorem nc_65 : ∀ i, 0 ≤ i → i < 64 → ch_65 i = true := nj_65_1
theorem lb_65 : LowerBin m_65 s_65 g_65 6 :=
  lowerDagV5 (kn_nil) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xffff0000
def s_66 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_66 : Nat := 0x15570000
def ep_66 : Nat := 0x420000000000000402000000000000100200000000000015540000
def bds_66 : List (Nat × List Nat × Nat × Nat) := []
def cc_66_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_66_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_66 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_66_0 p) (Nat.blt p 32)
def hc_66_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_66_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_66_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_66 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_66_2 (Nat.sub p 64)) (hc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_66_0 p) (Nat.blt p 32)
def f_66 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_66 : Nat → Bool := dagCheckNodeV5 m_66 g_66 ep_66 1 1 bds_66 64 (dagTraceF m_66 s_66 5 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 1 1 64 bds_66 (dagTraceF m_66 s_66 5 f_66) (cur_66 0) (nh_66 0) s_66 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_0 : treeBlockF 0 32 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_1 : treeBlockF 32 64 ch_66 = true := by decide +kernel
theorem nj_66_1 : ∀ i, 0 ≤ i → i < 64 → ch_66 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_66_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_66_1 h1 h2)
theorem nc_66 : ∀ i, 0 ≤ i → i < 64 → ch_66 i = true := nj_66_1
theorem lb_66 : LowerBin m_66 s_66 g_66 6 :=
  lowerDagV5 (kn_nil) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0xffff
def s_67 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_67 : Nat := 0x377f
def ep_67 : Nat := 0x48000000000000040800000000000032200000000000000440
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_67 : Nat → List (Nat × Nat) := fun _ => []
def nh_67 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_67 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 1 1 0 bds_67 (dagTraceF m_67 s_67 4 f_67) (cur_67 0) (nh_67 0) s_67 4 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_67 g_67 ep_67 1 1 bds_67 0 (dagTraceF m_67 s_67 4 f_67) cur_67 nh_67 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_67 : LowerBin m_67 s_67 g_67 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_67 nc_67 (by decide +kernel)

def m_68 : Nat := 0xff00ff00
def s_68 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_68 : Nat := 0x15003700
def ep_68 : Nat := 0x22000000000000000000000000000400040000000000100032000000000015000400
def bds_68 : List (Nat × List Nat × Nat × Nat) := []
def cur_68 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_68 : Nat → Nat := fun _ => 0
def f_68 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_68 : Nat → Bool := dagCheckNodeV5 m_68 g_68 ep_68 1 1 bds_68 1 (dagTraceF m_68 s_68 3 f_68) cur_68 nh_68
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 m_68 g_68 ep_68 1 1 1 bds_68 (dagTraceF m_68 s_68 3 f_68) (cur_68 0) (nh_68 0) s_68 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68 : treeBlockF 0 1 ch_68 = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 1 → ch_68 i = true := fun _ h1 h2 => treeBlockF_at nb_68 h1 h2
theorem lb_68 : LowerBin m_68 s_68 g_68 4 :=
  lowerDagV5 (kn_nil) rc_68 nc_68 (by decide +kernel)

def m_69 : Nat := 0xff00ff
def s_69 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_69 : Nat := 0x57007f
def ep_69 : Nat := 0x280000000000000000000000000002000800000000000200200000000000540040
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_69 : Nat → List (Nat × Nat) := fun _ => []
def nh_69 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_69 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV5 m_69 g_69 ep_69 1 1 0 bds_69 (dagTraceF m_69 s_69 4 f_69) (cur_69 0) (nh_69 0) s_69 4 = true := by decide +kernel
theorem nc_69 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_69 g_69 ep_69 1 1 bds_69 0 (dagTraceF m_69 s_69 4 f_69) cur_69 nh_69 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_69 : LowerBin m_69 s_69 g_69 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_69 nc_69 (by decide +kernel)

def m_70 : Nat := 0xf0f0f0f
def s_70 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_70 : Nat := 0x507070f
def ep_70 : Nat := 0x2080000000000020008000000000000000000000000000202000000000005040400
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_70 : Nat → List (Nat × Nat) := fun _ => []
def nh_70 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_70 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV5 m_70 g_70 ep_70 1 1 0 bds_70 (dagTraceF m_70 s_70 4 f_70) (cur_70 0) (nh_70 0) s_70 4 = true := by decide +kernel
theorem nc_70 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_70 g_70 ep_70 1 1 bds_70 0 (dagTraceF m_70 s_70 4 f_70) cur_70 nh_70 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_70 : LowerBin m_70 s_70 g_70 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_70 nc_70 (by decide +kernel)

def m_71 : Nat := 0xcccccccc
def s_71 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_71 : Nat := 0x444044c
def ep_71 : Nat := 0x80000000000400048000000000400040800000000000000000000000004440440
def bds_71 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_71 : Nat → List (Nat × Nat) := fun _ => []
def nh_71 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_71 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_71 : dagCheckRootsV5 m_71 g_71 ep_71 1 1 0 bds_71 (dagTraceF m_71 s_71 4 f_71) (cur_71 0) (nh_71 0) s_71 4 = true := by decide +kernel
theorem nc_71 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_71 g_71 ep_71 1 1 bds_71 0 (dagTraceF m_71 s_71 4 f_71) cur_71 nh_71 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_71 : LowerBin m_71 s_71 g_71 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_71 nc_71 (by decide +kernel)

def m_72 : Nat := 0xaaaaaaaa
def s_72 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_72 : Nat := 0x2222a
def ep_72 : Nat := 0x22280000000000020008000000000002000800000000000222200000000000000000
def bds_72 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_72 : Nat → List (Nat × Nat) := fun _ => []
def nh_72 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_72 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_72 : dagCheckRootsV5 m_72 g_72 ep_72 1 1 0 bds_72 (dagTraceF m_72 s_72 4 f_72) (cur_72 0) (nh_72 0) s_72 4 = true := by decide +kernel
theorem nc_72 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_72 g_72 ep_72 1 1 bds_72 0 (dagTraceF m_72 s_72 4 f_72) cur_72 nh_72 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_72 : LowerBin m_72 s_72 g_72 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_72 nc_72 (by decide +kernel)

def m_73 : Nat := 0xf000f000f000f
def s_73 : List Nat := [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f]
def g_73 : Nat := 0x500070007000f
def ep_73 : Nat := 0x2000800000002000000080000000000000000000000000000000000000002000200000005000400040000
def bds_73 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_73 : Nat → List (Nat × Nat) := fun _ => []
def nh_73 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_73 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_73 : dagCheckRootsV5 m_73 g_73 ep_73 1 1 0 bds_73 (dagTraceF m_73 s_73 4 f_73) (cur_73 0) (nh_73 0) s_73 4 = true := by decide +kernel
theorem nc_73 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_73 g_73 ep_73 1 1 bds_73 0 (dagTraceF m_73 s_73 4 f_73) cur_73 nh_73 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_73 : LowerBin m_73 s_73 g_73 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_73 nc_73 (by decide +kernel)

def m_74 : Nat := 0xff000000ff000000
def s_74 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_74 : Nat := 0x100000015000000
def ep_74 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000100000015000000
def bds_74 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_74 : Nat → List (Nat × Nat) := fun _ => []
def nh_74 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_74 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_74 : dagCheckRootsV5 m_74 g_74 ep_74 1 1 0 bds_74 (dagTraceF m_74 s_74 4 f_74) (cur_74 0) (nh_74 0) s_74 4 = true := by decide +kernel
theorem nc_74 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_74 g_74 ep_74 1 1 bds_74 0 (dagTraceF m_74 s_74 4 f_74) cur_74 nh_74 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_74 : LowerBin m_74 s_74 g_74 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_74 nc_74 (by decide +kernel)

def m_75 : Nat := 0xff000000ff0000
def s_75 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_75 : Nat := 0x15000000570000
def ep_75 : Nat := 0x42000000000000000000000000000000000000000400000002000000100000000200000015000000540000
def bds_75 : List (Nat × List Nat × Nat × Nat) := []
def cc_75_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_75_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_75 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_75_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_75_0 p) (Nat.blt p 32)
def hc_75_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_75_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_75_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_75 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_75_2 (Nat.sub p 64)) (hc_75_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_75_0 p) (Nat.blt p 32)
def f_75 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_75 : Nat → Bool := dagCheckNodeV5 m_75 g_75 ep_75 1 1 bds_75 64 (dagTraceF m_75 s_75 5 f_75) cur_75 nh_75
set_option maxHeartbeats 0 in
theorem rc_75 : dagCheckRootsV5 m_75 g_75 ep_75 1 1 64 bds_75 (dagTraceF m_75 s_75 5 f_75) (cur_75 0) (nh_75 0) s_75 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_0 : treeBlockF 0 32 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_1 : treeBlockF 32 64 ch_75 = true := by decide +kernel
theorem nj_75_1 : ∀ i, 0 ≤ i → i < 64 → ch_75 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_75_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_75_1 h1 h2)
theorem nc_75 : ∀ i, 0 ≤ i → i < 64 → ch_75 i = true := nj_75_1
theorem lb_75 : LowerBin m_75 s_75 g_75 6 :=
  lowerDagV5 (kn_nil) rc_75 nc_75 (by decide +kernel)

def m_76 : Nat := 0xf000f000f000f0
def s_76 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_76 : Nat := 0x10005000500070
def ep_76 : Nat := 0x40002000000040000000200000000000000000000000000000000000100000000000200010005000500040
def bds_76 : List (Nat × List Nat × Nat × Nat) := []
def cc_76_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_76_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_76 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_76_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_76_0 p) (Nat.blt p 32)
def hc_76_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_76_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_76_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_76 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_76_2 (Nat.sub p 64)) (hc_76_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_76_0 p) (Nat.blt p 32)
def f_76 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_76 : Nat → Bool := dagCheckNodeV5 m_76 g_76 ep_76 1 1 bds_76 64 (dagTraceF m_76 s_76 5 f_76) cur_76 nh_76
set_option maxHeartbeats 0 in
theorem rc_76 : dagCheckRootsV5 m_76 g_76 ep_76 1 1 64 bds_76 (dagTraceF m_76 s_76 5 f_76) (cur_76 0) (nh_76 0) s_76 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_76_0 : treeBlockF 0 32 ch_76 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_76_1 : treeBlockF 32 64 ch_76 = true := by decide +kernel
theorem nj_76_1 : ∀ i, 0 ≤ i → i < 64 → ch_76 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_76_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_76_1 h1 h2)
theorem nc_76 : ∀ i, 0 ≤ i → i < 64 → ch_76 i = true := nj_76_1
theorem lb_76 : LowerBin m_76 s_76 g_76 6 :=
  lowerDagV5 (kn_nil) rc_76 nc_76 (by decide +kernel)

def m_77 : Nat := 0xf0f00000f0f00000
def s_77 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_77 : Nat := 0x10000010500000
def ep_77 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000010000010500000
def bds_77 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_77 : Nat → List (Nat × Nat) := fun _ => []
def nh_77 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_77 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_77 : dagCheckRootsV5 m_77 g_77 ep_77 1 1 0 bds_77 (dagTraceF m_77 s_77 4 f_77) (cur_77 0) (nh_77 0) s_77 4 = true := by decide +kernel
theorem nc_77 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_77 g_77 ep_77 1 1 bds_77 0 (dagTraceF m_77 s_77 4 f_77) cur_77 nh_77 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_77 : LowerBin m_77 s_77 g_77 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_77 nc_77 (by decide +kernel)

def m_78 : Nat := 0x4444444444444444
def s_78 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_78 : Nat := 0x4044404440444
def ep_78 : Nat := 0x440000000000440000000000004004000400040000404000400040000000000000000000000000000000000
def bds_78 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_78 : Nat → List (Nat × Nat) := fun _ => []
def nh_78 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_78 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_78 : dagCheckRootsV5 m_78 g_78 ep_78 1 1 0 bds_78 (dagTraceF m_78 s_78 4 f_78) (cur_78 0) (nh_78 0) s_78 4 = true := by decide +kernel
theorem nc_78 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_78 g_78 ep_78 1 1 bds_78 0 (dagTraceF m_78 s_78 4 f_78) cur_78 nh_78 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_78 : LowerBin m_78 s_78 g_78 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_78 nc_78 (by decide +kernel)

def m_79 : Nat := 0x2222222222222222
def s_79 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_79 : Nat := 0x200022222
def ep_79 : Nat := 0x2222000000002000022200000000200020000000000020002000000000000000000000000000000000000
def bds_79 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_79 : Nat → List (Nat × Nat) := fun _ => []
def nh_79 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_79 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_79 : dagCheckRootsV5 m_79 g_79 ep_79 1 1 0 bds_79 (dagTraceF m_79 s_79 4 f_79) (cur_79 0) (nh_79 0) s_79 4 = true := by decide +kernel
theorem nc_79 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_79 g_79 ep_79 1 1 bds_79 0 (dagTraceF m_79 s_79 4 f_79) cur_79 nh_79 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_79 : LowerBin m_79 s_79 g_79 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_79 nc_79 (by decide +kernel)

def m_80 : Nat := 0xa0a0a0a0a0a0a0a
def s_80 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_80 : Nat := 0x20002020a
def ep_80 : Nat := 0x2020800000002000002080000000200020008000000000000000000000002000202000000000000000000
def bds_80 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_11, s_11, 4, g_11), (m_8, s_8, 4, g_8), (m_10, s_10, 4, g_10)]
def cc_80_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_80_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_80 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_80_1 (Nat.sub p 32)) (cc_80_0 p) (Nat.blt p 32)
def hc_80_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_80_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_80 : Nat → Nat := fun p => Bool.rec (hc_80_1 (Nat.sub p 32)) (hc_80_0 p) (Nat.blt p 32)
def f_80 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_80 : Nat → Bool := dagCheckNodeV5 m_80 g_80 ep_80 1 1 bds_80 43 (dagTraceF m_80 s_80 6 f_80) cur_80 nh_80
set_option maxHeartbeats 0 in
theorem rc_80 : dagCheckRootsV5 m_80 g_80 ep_80 1 1 43 bds_80 (dagTraceF m_80 s_80 6 f_80) (cur_80 0) (nh_80 0) s_80 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_80_0 : treeBlockF 0 32 ch_80 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_80_1 : treeBlockF 32 43 ch_80 = true := by decide +kernel
theorem nj_80_1 : ∀ i, 0 ≤ i → i < 43 → ch_80 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_80_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_80_1 h1 h2)
theorem nc_80 : ∀ i, 0 ≤ i → i < 43 → ch_80 i = true := nj_80_1
theorem lb_80 : LowerBin m_80 s_80 g_80 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_11 (kn_cons lb_8 (kn_cons lb_10 (kn_nil))))) rc_80 nc_80 (by decide +kernel)

def m_81 : Nat := 0xc0c0c0c0c0c0c0c
def s_81 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_81 : Nat := 0x404040404040c
def ep_81 : Nat := 0x400000800000400000000080004000000000008000000000000000000000000000000000004040404040400
def bds_81 : List (Nat × List Nat × Nat × Nat) := []
def cc_81_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_81_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_81 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_81_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_81_0 p) (Nat.blt p 32)
def hc_81_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_81_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_81_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_81 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_81_2 (Nat.sub p 64)) (hc_81_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_81_0 p) (Nat.blt p 32)
def f_81 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_81 : Nat → Bool := dagCheckNodeV5 m_81 g_81 ep_81 1 1 bds_81 64 (dagTraceF m_81 s_81 5 f_81) cur_81 nh_81
set_option maxHeartbeats 0 in
theorem rc_81 : dagCheckRootsV5 m_81 g_81 ep_81 1 1 64 bds_81 (dagTraceF m_81 s_81 5 f_81) (cur_81 0) (nh_81 0) s_81 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_0 : treeBlockF 0 32 ch_81 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_1 : treeBlockF 32 64 ch_81 = true := by decide +kernel
theorem nj_81_1 : ∀ i, 0 ≤ i → i < 64 → ch_81 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_81_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_81_1 h1 h2)
theorem nc_81 : ∀ i, 0 ≤ i → i < 64 → ch_81 i = true := nj_81_1
theorem lb_81 : LowerBin m_81 s_81 g_81 6 :=
  lowerDagV5 (kn_nil) rc_81 nc_81 (by decide +kernel)

def m_82 : Nat := 0x303030303030303
def s_82 : List Nat := [0x101010101010101, 0x3000300030003, 0x30300000303, 0x3030303]
def g_82 : Nat := 0x101010301030303
def ep_82 : Nat := 0x2020000000002000002000000000200020000000000000000000000000000000000000101010001000000
def bds_82 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_82 : Nat → List (Nat × Nat) := fun _ => []
def nh_82 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_82 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_82 : dagCheckRootsV5 m_82 g_82 ep_82 1 1 0 bds_82 (dagTraceF m_82 s_82 4 f_82) (cur_82 0) (nh_82 0) s_82 4 = true := by decide +kernel
theorem nc_82 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_82 g_82 ep_82 1 1 bds_82 0 (dagTraceF m_82 s_82 4 f_82) cur_82 nh_82 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_82 : LowerBin m_82 s_82 g_82 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_82 nc_82 (by decide +kernel)

def m_83 : Nat := 0xc3c3c3c3c3c3c3c3
def s_83 : List Nat := [0x4141414141414141, 0x303030303030303, 0xc300c300c300c3, 0xc3c30000c3c3, 0xc3c3c3c3]
def g_83 : Nat := 0x101014301430343
def ep_83 : Nat := 0x42020000000042000002000000004200420040000000000000000000000000000000000101014001400040
def bds_83 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 5, g_26), (m_28, s_28, 5, g_28), (m_27, s_27, 5, g_27), (m_30, s_30, 5, g_30), (m_29, s_29, 5, g_29), (m_82, s_82, 5, g_82), (m_25, s_25, 5, g_25), (m_8, s_8, 4, g_8)]
def cur_83 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa4b63301f 4 15 2 3 10 1023 12 4095
def nh_83 : Nat → Nat := unpackHintV5 0x5bba0d19d017300005 0x2f79def77dc2e3eebbdcbdee13bdd77baef79dee3ef7bde66f7bdce338ef7bdc78bbdc2ef9cde17177bdef337bdee719c6bbceebbbee0f2ebb97bccd76f5dbc09c6719ee3b9ee3b9c06d37 18 262143 8 255
def f_83 : Nat → Nat × Nat := unpackForestF 0x192f1981f 1 10
def ch_83 : Nat → Bool := dagCheckNodeV5 m_83 g_83 ep_83 3 7 bds_83 3 (dagTraceF m_83 s_83 7 f_83) cur_83 nh_83
set_option maxHeartbeats 0 in
theorem rc_83 : dagCheckRootsV5 m_83 g_83 ep_83 3 7 3 bds_83 (dagTraceF m_83 s_83 7 f_83) (cur_83 0) (nh_83 0) s_83 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_83 : treeBlockF 0 3 ch_83 = true := by decide +kernel
theorem nc_83 : ∀ i, 0 ≤ i → i < 3 → ch_83 i = true := fun _ h1 h2 => treeBlockF_at nb_83 h1 h2
theorem lb_83 : LowerBin m_83 s_83 g_83 8 :=
  lowerDagV5 (kn_cons lb_26 (kn_cons lb_28 (kn_cons lb_27 (kn_cons lb_30 (kn_cons lb_29 (kn_cons lb_82 (kn_cons lb_25 (kn_cons lb_8 (kn_nil))))))))) rc_83 nc_83 (by decide +kernel)

def m_84 : Nat := 0xcc33cc33cc33cc33
def s_84 : List Nat := [0x4411441144114411, 0x33003300330033, 0xc030c030c030c03, 0xcc330000cc33, 0xcc33cc33]
def g_84 : Nat := 0x11041304130433
def ep_84 : Nat := 0x402002000000402000000200000000000000000000004020402040000000000000000000011041004100400
def bds_84 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 5, g_50), (m_19, s_19, 5, g_19), (m_20, s_20, 5, g_20), (m_17, s_17, 5, g_17), (m_22, s_22, 5, g_22), (m_21, s_21, 5, g_21), (m_18, s_18, 5, g_18), (m_9, s_9, 4, g_9)]
def cur_84 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb4b63301f 4 15 2 3 10 1023 12 4095
def nh_84 : Nat → Nat := unpackHintV5 0x5c794d49d0173c0005 0x16ebd57def3bdeefbdcbdee5ef72f79dee5ef3b8e1d7bdeeb3acf7bdeebef7bdee5d0bbe73780def7bdc70ebdef759d6757979dcbbee5db97b8e1c358772e5ebaceb3ad4ebb972e7bc31d7 18 262143 8 255
def f_84 : Nat → Nat × Nat := unpackForestF 0x1d2f1981f 1 10
def ch_84 : Nat → Bool := dagCheckNodeV5 m_84 g_84 ep_84 3 7 bds_84 3 (dagTraceF m_84 s_84 7 f_84) cur_84 nh_84
set_option maxHeartbeats 0 in
theorem rc_84 : dagCheckRootsV5 m_84 g_84 ep_84 3 7 3 bds_84 (dagTraceF m_84 s_84 7 f_84) (cur_84 0) (nh_84 0) s_84 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84 : treeBlockF 0 3 ch_84 = true := by decide +kernel
theorem nc_84 : ∀ i, 0 ≤ i → i < 3 → ch_84 i = true := fun _ h1 h2 => treeBlockF_at nb_84 h1 h2
theorem lb_84 : LowerBin m_84 s_84 g_84 8 :=
  lowerDagV5 (kn_cons lb_50 (kn_cons lb_19 (kn_cons lb_20 (kn_cons lb_17 (kn_cons lb_22 (kn_cons lb_21 (kn_cons lb_18 (kn_cons lb_9 (kn_nil))))))))) rc_84 nc_84 (by decide +kernel)

def m_85 : Nat := 0xcccc3333cccc3333
def s_85 : List Nat := [0x4444111144441111, 0x333300003333, 0xc0c03030c0c0303, 0xcc003300cc0033, 0xcccc3333]
def g_85 : Nat := 0x4111304443333
def ep_85 : Nat := 0x440222000000000000000000004000200400000000400020400000000000000000000000004111004440000
def bds_85 : List (Nat × List Nat × Nat × Nat) := [(m_60, s_60, 5, g_60), (m_40, s_40, 5, g_40), (m_23, s_23, 5, g_23), (m_39, s_39, 5, g_39), (m_38, s_38, 5, g_38), (m_37, s_37, 5, g_37), (m_36, s_36, 5, g_36), (m_14, s_14, 4, g_14)]
def cur_85 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x53d2e1f 4 15 2 3 7 127 9 511
def nh_85 : Nat → Nat := unpackHintV5 0x5bb88d49a0173c0005 0x57adeb38ce3bcef7bd7bde77b97bcef72f7bdef7bdeeb7992f7bdcbde7535bdeb19ce3bdef7bdef7bdef74bb017ba177d2cf4338ce39dcbd72ebb977dcb8ee5cf72ecad7a34e976f72f7 18 262143 8 255
def f_85 : Nat → Nat × Nat := unpackForestF 0xcf971f 1 7
def ch_85 : Nat → Bool := dagCheckNodeV5 m_85 g_85 ep_85 3 7 bds_85 3 (dagTraceF m_85 s_85 7 f_85) cur_85 nh_85
set_option maxHeartbeats 0 in
theorem rc_85 : dagCheckRootsV5 m_85 g_85 ep_85 3 7 3 bds_85 (dagTraceF m_85 s_85 7 f_85) (cur_85 0) (nh_85 0) s_85 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85 : treeBlockF 0 3 ch_85 = true := by decide +kernel
theorem nc_85 : ∀ i, 0 ≤ i → i < 3 → ch_85 i = true := fun _ h1 h2 => treeBlockF_at nb_85 h1 h2
theorem lb_85 : LowerBin m_85 s_85 g_85 8 :=
  lowerDagV5 (kn_cons lb_60 (kn_cons lb_40 (kn_cons lb_23 (kn_cons lb_39 (kn_cons lb_38 (kn_cons lb_37 (kn_cons lb_36 (kn_cons lb_14 (kn_nil))))))))) rc_85 nc_85 (by decide +kernel)

def m_86 : Nat := 0xcccccccc33333333
def s_86 : List Nat := [0x4444444411111111, 0x33333333, 0xc0c0c0c03030303, 0xcc00cc00330033, 0xcccc00003333]
def g_86 : Nat := 0x4044411133333
def ep_86 : Nat := 0x440000022200004004000020000000404000002000000000000000000000004044411100000
def bds_86 : List (Nat × List Nat × Nat × Nat) := [(m_47, s_47, 5, g_47), (m_35, s_35, 5, g_35), (m_41, s_41, 5, g_41), (m_34, s_34, 5, g_34), (m_33, s_33, 5, g_33), (m_32, s_32, 5, g_32), (m_31, s_31, 5, g_31), (m_1, s_1, 4, g_1)]
def cur_86 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x153d0b81f 4 15 2 3 9 511 11 2047
def nh_86 : Nat → Nat := unpackHintV5 0x5bb88d49a0173c0005 0x57adeb38ce35bccde77bdebdef3bdcbde77b97bdef7bdef7bdcbdee5e7535bdeb19ce360bdef7bdef7bdef74bb72e177d2cf4338ce3656bd1a76772f5cbaee5df72e3b973dcbb72f72f7 18 262143 8 255
def f_86 : Nat → Nat × Nat := unpackForestF 0x34f85c1f 1 9
def ch_86 : Nat → Bool := dagCheckNodeV5 m_86 g_86 ep_86 3 7 bds_86 3 (dagTraceF m_86 s_86 7 f_86) cur_86 nh_86
set_option maxHeartbeats 0 in
theorem rc_86 : dagCheckRootsV5 m_86 g_86 ep_86 3 7 3 bds_86 (dagTraceF m_86 s_86 7 f_86) (cur_86 0) (nh_86 0) s_86 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_86 : treeBlockF 0 3 ch_86 = true := by decide +kernel
theorem nc_86 : ∀ i, 0 ≤ i → i < 3 → ch_86 i = true := fun _ h1 h2 => treeBlockF_at nb_86 h1 h2
theorem lb_86 : LowerBin m_86 s_86 g_86 8 :=
  lowerDagV5 (kn_cons lb_47 (kn_cons lb_35 (kn_cons lb_41 (kn_cons lb_34 (kn_cons lb_33 (kn_cons lb_32 (kn_cons lb_31 (kn_cons lb_1 (kn_nil))))))))) rc_86 nc_86 (by decide +kernel)

def g_87 : Nat := 0x11515571557377f
def ep_87 : Nat := 0x1442222800001442000022280014004200420048010404020402040801101002100232200115155415540440
def bds_87 : List (Nat × List Nat × Nat × Nat) := [(m_56, s_56, 7, g_56), (m_52, s_52, 7, g_52), (m_49, s_49, 7, g_49), (m_76, s_76, 6, g_76), (m_80, s_80, 7, g_80), (m_65, s_65, 6, g_65), (m_55, s_55, 6, g_55), (m_66, s_66, 6, g_66), (m_64, s_64, 6, g_64), (m_54, s_54, 5, g_54), (m_45, s_45, 6, g_45), (m_53, s_53, 5, g_53), (m_75, s_75, 6, g_75), (m_82, s_82, 5, g_82), (m_81, s_81, 6, g_81), (m_48, s_48, 6, g_48), (m_46, s_46, 5, g_46), (m_70, s_70, 5, g_70), (m_44, s_44, 5, g_44), (m_60, s_60, 5, g_60), (m_73, s_73, 5, g_73), (m_72, s_72, 5, g_72), (m_57, s_57, 5, g_57), (m_58, s_58, 5, g_58), (m_43, s_43, 5, g_43), (m_71, s_71, 5, g_71), (m_77, s_77, 5, g_77), (m_62, s_62, 5, g_62), (m_74, s_74, 5, g_74), (m_59, s_59, 5, g_59), (m_61, s_61, 5, g_61), (m_51, s_51, 5, g_51), (m_63, s_63, 5, g_63), (m_69, s_69, 5, g_69), (m_42, s_42, 5, g_42), (m_83, s_83, 8, g_83), (m_85, s_85, 8, g_85), (m_86, s_86, 8, g_86), (m_84, s_84, 8, g_84), (m_79, s_79, 5, g_79), (m_16, s_16, 5, g_16), (m_78, s_78, 5, g_78), (m_67, s_67, 5, g_67), (m_68, s_68, 4, g_68)]
def cc_87_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8001fc15d897405b096c05909640570958156015025401500540150053054c052054415101440510144047291c047011c04700f4a01f0001 0x79b70cd5bc64ac63146f182318bb17c5b8b62c457156298a6dbc516c62735f131ad892d5c466a622b4f10da5882d1c396861c2630dd2f06a96c334b4192560b5298569482a49c1424b099218489082347c10a3b07d1983a8c8060200912406c2a022490190880812405c1a01e4900e2480a034030a981a4d00c6860934f045a182090c0f4760723302ca18144ec092660412301c0f03517c188a60b353055a5826d0c062480285e0102b0061380207d5145fa7a2dd3715e968a748b5fa41add12d5e846a74034f9eda5ceed1e6a68732a5f9892dcb695e564a72924f93125c9091e3a4871aa3f8bd1dc548de0c4670595f7f4adbdc55de72a6ef14f748a5b5851da3286cb13f6449db144dd82266bb92f5c895ad649d63246b005f5482da8615d3c0a69704f474259dc11ce10866783f3201d97a0dcb10664e82f2601591a09c810463b81f1a00d83805c010260003f 14 16383 6 63 11 2047 21 2097151
def cc_87_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xe1e0d9cac89790909089888180796a68684c4841404032302220191818111002 0x1ea607b151f454789c204547edbddb676c9ad8263748e070106d14da5621a04189441808184535e579714e16081656e5253850204f1ac48204b1b9115e415ac4020 8 255 3 7 11 2047 18 262143
def cc_87_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xe19f25eb972b54a92e44280f5e3c6cd172c58992243654a0e1818080 0xbed66f25824042e349408ced361b2982bb49ac9208810a89a0f230a48e284599e9626b5e4e94e5c6194982435e8e8e080108917a234e1e042034084941f357 7 127 2 3 11 2047 18 262143
def cc_87_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c23088620882208818a6018060180601805c5705495054150541411f470148500c8300481000400 0x88056022fbfc537e6a6fad2df1a1bd95e7a2acf2539e09f348156f680df151101322343768beeb14dd1afb9b537269ee2d2dc1a3b73436d0bcd8159ac273503e6904cce9a0b1281a268654b0c69a0952030a48 10 1023 4 15 11 2047 19 524287
def cc_87_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xa45af681a0681a059160545505415054141501314c0b82c0a1280912408120080200802000800000 0x27e2dd845bae8a75a97eb12f55a5aaa4af5295aa12953a4ea64854857e88abd014f2325b3c496702f4d8569a09d3209a5db049360906a12d15e55ad4a352936852255e3ca3c713d8307b181122812440248b8a71294e1d21c305e850ad0813a0c1f41026 10 1023 4 15 11 2047 19 524287
def cc_87_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8c622101803c5e0e170381c0e0701a0a250209008040201008031180c04220088400200 0x2fda863c5ac68a58895f0d20e0957c029b7c49ed026de034ba04970092eda9dca53b74676c17ad42b5a04eb307d6409a7c92d7a44a52bf4a93a8d3650a44 9 511 4 15 11 2047 19 524287
def cc_87_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xe8743a1d0e0f0363a1d06472181c05c6e08f401c4e070381c04a20100802210080040000 0x69145d9489ac57f591cea36cd24b7c0d7f7daf6f35add6afb8d5b6da96d25bd84a7ae8e69918ea95fd32ae544f7449ae812fce0499a8ef302f65856ca07d9209b163061460 9 511 4 15 11 2047 19 524287
def cc_87_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xdc0d42d40d40c83c80c80c41c40c01c00bc1bc0bc0b81b803613402c22c0281280241240240240240240201008000000 0x7f4607e2307e3447da6c7c16d7c2337b36c7a46078b608e5638dc638cb6f8b3638ab5f6f3598a353893518834f873438626f84a638425f55a5983a5382a5181a4f80a438023f7fa3b7ea377d2337c96f7b95d191557a93f799377912f781277785e7305d7784e738427683471826758247482471b43763437524374233739567305e7284e7203e71026 12 4095 6 63 11 2047 20 1048575
def cc_87_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0bb1c0e07030980c05128140a048a410280389c0a450280c86030180844011080040000 0x8fb4396c5f9645395b5f9535394b4f9434b9334791b43910569084e9003e8f0268d56889b508c36c8bb5c89c6e88c6c87b6c86d688325085a6c8525c8336e8246c8126c 9 511 4 15 11 2047 20 1048575
def cc_87_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c221755d0741d0741d06c9b06c1a1681916418127c811c46114450140500c8300c0030000000000 0x9f143a105ea0856a002c9f8269e8249a1559b9279a233992399824e9db639d3496db419ca639c249542419b2339a96f1b94d999459893f9792f7785677846910458785488844810548203492b409385c92c54920348f826 10 1023 4 15 11 2047 20 1048575
def cc_87_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xe86cb61b0c96432172b85c2e17083b89c0e070381c0c26030180c0512812209000000000 0xaf944af044ae134ad834ac934ac034aec53ad353abb43ab05eaa856aa04ea983ea6b41a4241a6d7ca637ca457ca3a7ca2a7ca8c6da8461a7b61a734ba5b43a5261a4a4ba3243a2233 9 511 4 15 11 2047 20 1048575
def cc_87_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0280a02719c2709859d6419064190515404c5304c1304c0b82c0a1280a0280a0280280802000800 0x9805fbcc5bc0c5bc0453bfa5ebf25abea56be252bda4ebd2429785f790576804f1182dbc025bb15eba956ba14e6684bb9815b8b60b8457b7b5ab7352b6b42b293d780575f047b603db5144b4c53b415eb3956b314eb293e740535b843b2015b114fb0947 10 1023 4 15 11 2047 20 1048575
def cc_87_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xa82a0a4690a06719c2615fd705c1705c1344c1304c121481202a0a02449024090240900600100000 0xcc045cda449905fcc25bd135fd0b5ed035acfb57cf356ceb52ce25bcd253cca39bd2319885f7a8571503dcb8355002fca95eca156c993ec9015c7460c845ac7c52c6a57c6241c294d79857c584d47827c4934c4353c395ec3156c294ec213e7505343833c1815bc825 10 1023 4 15 11 2047 20 1048575
def cc_87_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xd02d00d00d00cc1cc0c81c80c80c80c80c02c00c00b43b40b40b012e12c0242240240240240240201008000000000000 0xe026cdfa5cddb6edcc6cda460d9230d9344d8a6cd706dd7233e8d63e8463e736fe5b63e535fd0359e4b53e3b51e2b4fe1b43e0a6fdf263dea5fbf259de253dd251dc24fdba43db23fdaa3bd9a37d8233d795ed415dd794ed4942b086fd685d190556983f608375102f48827d5934d2815d2b43d5343d4a56d415ed394ed313e5c84344833d2015 12 4095 6 63 11 2047 20 1048575
def cc_87_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x63d7158551541504c9304c1304c12126490240901c8701c0521405014041100310c0210800200000 0xf3363f2b49ceb41f2263f1a49be241f0a33d7956d7946eb945b106f1b84def8456a83f5202fe2154e3144dc934ec934ea015ea343eec5fee453edb53ed34bec343eb956eb14eea93ee9815e7d68e4350e6b6ce635ce446ee346ce236ce1568dda50 10 1023 4 15 11 2047 20 1048575
def cc_87_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x801975c9705c1705c1705495054150541324c121264902409024090204350c0300c0300c01204001 0x82229c0ad4e026870095e800ab3fe539fe27cfc3417cd20bf15f1f76f8f9d7c7c93e3e09f1fc8dafdc617e9b0bf2d2df6686faa617d125be290def466f48437b4af3d8559eb030f50157a00a3c0155e204ef0233 10 1023 4 15 11 2047 21 2097151
def cc_87_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xe01e00e00d04d00cc1cc0cc0c81c80c02bc1bc0bc0b42b40ac2a81222182180180102100100082080080002000000000 0x1f017879a243a5b61c0da1d81786a3542e056158a89b86f810b54251521104d07c54788b7ab21aa28ad713567891a244699e224bf1025e87d2d43695e194ad0c252808b5bde59de12beec15b6c0abb5454d7a25b0b12b85093c26495570d6a20674d82fa4616cfa0ae7605329816c200ae0e04f068251f00f8dc06c3902e098134d4279f211e0a4890494481d1a40c4d20446901934 12 4095 6 63 11 2047 21 2097151
def cc_87_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xa80d402a014c1650b201900c806402829400a004e0a70138068d3401a00d0068020510007043801810c001140800208100002000 0x10396a5703548f59e468d720b5a915ab48899e4349d0c2429091f4828f6052d6f896776cadb6e55d9a29ec41435f096c804ae3f24f1f12556835a8c19d2a0b6808573602797610ca805b1e82b8f013c760947e03e3981b1180b82c04e396bd1c3568c9a736c55e3726a9485b4002bc6c0d472036228171100bc6897a334ad1923e768adb6a55e3124a9405b3fc2bc600947d03e3881b10c0b82a04e2e8b516c528911836655e2c29a9305b3f42bc56134700362081786932452952274f910a5c87923c4a8f5b228f0a927494259f811e12057078271bc0d88005c3f02f10d66 13 8191 6 63 11 2047 21 2097151
def cc_87_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xd4350d06f5b4ad0b42d0926318c2306a5a064590641902bc91240900601004010040010000000000 0x12eb4798636cc11865f6d92f361971b037e5550a0ab2d25e9652b3c857dbe2af2c1254e42fa1215e5704a288171400bc9f17a55692dc157950a2a5616d030af298451d00d89c05c4d02f28c6b905a94a093a1f48527a3e9051ebe859d9c29ebf12d93892a9219cda09e5582d9341289805c4b02f2145d92da8c8a90a4a2bac69379242e9880dc4902e24017 10 1023 4 15 11 2047 21 2097151
def cc_87_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x8a0c502280d8f6a0b501a80b485a02d01680b405a02c05600b00560ab01580a811308900480240120021c1000800010000000000 0x5c02f394529fda74e4d36644d73f23987d18bf259da027b3e93560497a9c19cde07b3e0352c0178b605c5a02f39c5d9d5a14f4946792bab81279e02e92c09c5802e2b817828b52be1aa76acf3945a9d62b4e8d9e7369d3934d98d35ce28e6184630416b7d8b3bb856dc32aece93d9c09dcde4de6e26ac012f5a491aba1ad4b0ce9605b4382b9b60f66d077360379ac1a95c0bc8b0463f81f1d40d8aa05c1802734c599a22acce555c128f33055430238a605e648b731c53 13 8191 6 63 11 2047 21 2097151
def cc_87_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xd1340d02e6b82d1b42d09da709c2709c207789e0781e0781e0745855896058160364c1300c003000 0xa86b6d40d269f49314233a6628d3ad86766874e26191d21c4c8ce9a8d94cd65740abd305151b0af4b8451900bd2b166948ab49955738a3d241551908e310179452dc8c94e8b48f47c6da3a30d1a9b28c4c345260730aaa2e156886bd43b56798afb9655e8626a9d85f4582bd0a0d46002e2f8179fe2f506925dd2b6e2957a08a2a5a16d100af408452000f8ec06c5d02e0d013 10 1023 4 15 11 2047 21 2097151
def cc_87_21 : Nat → List (Nat × Nat) := unpackCursorV5 0xa28301000 0x150c69a90aad461546602f4d464 6 63 3 7 11 2047 21 2097151
def cur_87 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_87_21 (Nat.sub p 672)) (cc_87_20 (Nat.sub p 640)) (Nat.blt p 672)) (cc_87_19 (Nat.sub p 608)) (Nat.blt p 640)) (Bool.rec (Bool.rec (cc_87_18 (Nat.sub p 576)) (cc_87_17 (Nat.sub p 544)) (Nat.blt p 576)) (cc_87_16 (Nat.sub p 512)) (Nat.blt p 544)) (Nat.blt p 608)) (Bool.rec (Bool.rec (Bool.rec (cc_87_15 (Nat.sub p 480)) (cc_87_14 (Nat.sub p 448)) (Nat.blt p 480)) (cc_87_13 (Nat.sub p 416)) (Nat.blt p 448)) (Bool.rec (cc_87_12 (Nat.sub p 384)) (cc_87_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 416)) (Nat.blt p 512)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_87_10 (Nat.sub p 320)) (cc_87_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_87_8 (Nat.sub p 256)) (Nat.blt p 288)) (Bool.rec (Bool.rec (cc_87_7 (Nat.sub p 224)) (cc_87_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_87_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 256)) (Bool.rec (Bool.rec (Bool.rec (cc_87_4 (Nat.sub p 128)) (cc_87_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_87_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_87_1 (Nat.sub p 32)) (cc_87_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 352)
def hc_87_0 : Nat → Nat := unpackHintV5 0xb5310ead99e6a9610ea3c9669b7a1495e1668d921488594e80b1ea78d9f673e13e6c19f26429fc5c39fc5521c64df9ca46e1c646981244f06a3cf20034e2042cc2082579d21e31d21b10c81549720f817209798203a1760000e8000000000000 0x200aa00aa07030703000000000000a170b17170b030307070303000051555550010828217171717821785e1785e17001f07c1705c171721f280285c2c5c3c5c3c5c2c5c0c5c1c5c1c5c0c4c4c4c145d0411344d1344d1313613444c0513140004e0084c4c4c1c4c1c4e1381107c1f07c1f07c1f154011344d1344d1344d001410000000b030000001c3c1c1c1c001c1c0002c2c2c2c2e17170b85c5c1c1c1c1c000000000000015555555554000000001c3c1c001c3c1e9c1c1c1c1c1c1c1c002c2c2c2c1e07570781c1c1c1c1c1c000000000000015555555554001000002c00f001c070001c0000c007005c08001000001c0c3c1c3c00000707000030300000030b030b03030303038ac5c0e2b170000000000000055555555550000000707030f070f07a70000070707030f0f00030b030b030303030380d5c0e0337000000000000005555555555000400000b003c003001c00300c002b0001702000400000b0f0f0b0082c3e0f21785c000280010c0c5c1c5c1d0c0c3c3c0000000000000000155555555540000002c3c3c2c0282c3e0fa9e1785c0002a17370b0717070b370b0f0f000000000000005555555555000400000b003c003001c01702002c0b0010c0000400000070307030083e1781ea7a0307000003430707030f0707a80c9c1c000000000000015555555554001000002c02b000c007005c0800701c000300c0001000001c0c1c0c020f85e0380000370b0f0f0f0f370ba000070700000000000000000555555555500000000703070300083e17a030781e2700003743030f0f0f0337a80c1c1c000000000000015555555554001000002c023000c007005c0800300c00370000100000001c3c1c001c3c1e9c1c1c1c1c1c1c1c002c2c2c2c1e07570781c1c1c1c1c1c002c3c3c2c1c1c1c6c1c4c1c1c1c1c1c1c4c2c2c5c00000000000001b29c00001c1c0c3c1c3c1e9c00001c1c1c0c3c3c000c2c0c2c0c0c0c0c0e03570380c6c002c3c3c2c0c1c1c0c0c4c6c6c4c4c0c6c4c0c0c6c00000000000001b29c00002c3c3c2c0282c3e0fa9e1785c0002a17370b0717070b1b0b0f0f000b0f0f0b1317131b13a170b131b1b13130b1b000000000000006ca700000070307030083e1781ea7a03070000031b0707030f0707a80c9c1c004c3c3cbc0c1c1c0c4e85c1c1c0cec0c4c1c1c00000000000003b29c000001c0c1c0c0020f85e80c1e0789c0000dc6c0c3c3c3c0c6ea03070700130f0f0307070313a170313373f1313033700000000000001fca77f29c2c2c3c3cfc4c0c1c5e030b03a7000000b0f0f0b000b0b0b0b0b2f0b0000b130f0f0f0f0f0f13131313130b0b1300000b0f131b370b071b070b1b0b570b82e0b1b0f0f0f000000000004ca700000000007070707001b0f0f170707070700130f0f13070713a707070707131313130000071b0707070f070707070707570781e0707071307000000000004ca70000000000703070300030f031b03030303000130f0f1303130707070713131303031300001b1b030f0f0f031b031313033b0380e0337070707000000000004ca700000000170f0f1b00083e1785e17000130f0f13131313131313aa131300001b1b0f0f0f0f171b1737170717071737131313a800000000001329c000000006c3c3c6c006c3c3c6c9cec9dfca729ca729c4e9c3e9c3e9c4e9c4e9c4e9c4e9c4e9c4e9c4e9c4e9c4e9c0004c3c3c4c4c4c4c4c4c4c4c4c000000f0f00270f0f272700130f0f13131327130000000000a700000000002c2c2c2c2c1c2c0c2c1c2c0c002c2c2c2c2e0b0b0b82c2c2c2c2c2c00000000000000155555555554000000000000f070f030f070f030f0f0f0f000f83c3c3e0f170f0f0f0f232b272300000000000000055555555555000000030303030f030000030b0303030f030300000c0c0c0c0c0c0c0c0e03030380c0c000000000000001555555555540000005c3c3c5c020f0f83c5e1785c00005c2c3c3c3c3c5c2c5c0c5c1c5c1c5c0c0000000000000000555555555550000000f0f00270f0f2727000000000055555500040000000001c0020004 24 16777215 10 1023
def hc_87_1 : Nat → Nat := unpackHintV5 0xcad064ca8812c9a03ac7b07cc051d8b4a2ecad19e2a4f20aa31078958b629250ce899a2e81720a80a0347e988277e9ac71e18264bb4a6180ce58ca2e50a20a4a59923cf35a3b50682deb5a2aa0d221ea2e1ae1c21541680cb2240b28620002ca 0x3a7130f0f0f0b47031f04d0fa77780c1c5e030b0b030b0303130f0f0f0b034747031f04d0f82a0a0703070381c20785e1780e030441f07c0301c17228028fc2cfc3cfc3cfc2c0e07070707a1707aa0707051f410044d1340d0744d91130144c582a0a0703070381c20785e17a030781ea00a1b030f0f031ba80c1c1e80284c2c8c4c8c2c0c0c1c1c1c1c0c0c4c5ea85c5c0c0c4c0e8d1cfc4d1c4c4c0c0cfc0c1107c1f00c0705c8031b01f1b0550044d1340d0744d903135131350014100000707070700aaaa0a0001313133f1313133f0707070707070707aaaa0001000000040a1ba83ea07a81eaaaa80000014040005555550004000000002c02c2e000b82c2c2cbc0bc2c2c2c2c2c1c2c0c2c1c2c0c2c02c2c2c2c2c2e0b0b0b82c2c2c2c2c2c002c0b02c2c4c4c1302c0b1042d0b42c2c3c4d1342d0b444c3b1b0f130f133f1323030f1b030b0f0f0f00f1b3b04b0f0f0f0f4b04b0f0f0f0f533b3b131300133f0f0f13130f0f0f0f0f0f1313132b131313231313133f1313133f0440f0f03c3c0f03c0f03c543e000f83c3c3c3c6c3c1c3c1c3c3c3c6c3e0f83c3c3c4c3c2c143d04010f1343c3d1344d1344d001410f050f14200aa00aaaa000000000000a0f07070707aa0000515555500100f0f00f2b0230f0f0f0f930630f0f0f0f232b2b23000f0f03c3c0f03c0f03c0f8003e0f0f0f0f030f070f070f030f170f83e0f0f050f41043c4d0f0f44d1344d13443c050f143e000f83c03c3c3c3cac08c3c1c3c0c3c1c3c0c3c3c3c3d2c12c3e0f0f0f83c5c3c3c3c3c8cacac8c003c3c3c3c0f03c0f03c0f1043c3c4c3d0f44d1344d13443c030f130f1b04d0b0b0f0b13133f133f03071780c2c0c3c02c0e082c0c1c0c0c0c0c0e0380c1c01c2c3c3c2c0c0c4cbc0c0c0c0c0c0c0c0c3c3c0c1c1c0c0c0c0c0c0c0d40c131400d134044dc02c2c2c5e082e82c0c1c1c0c2c2e082c2c2c2c4c5c4c5c2e0b0b82c4c5c2c4c4c2c2c2ea0b0f0f51302c501342d011570f4b00b1b2f04b0b0f0f0b0b04b0b0b0b0b0b2f0b131300133f0b0b130b0f0f0f0f13131313132f1313133f13130b0b0b0b133f0440b1303c4c1304c1302c546e000b82c4c4c6c2c1c6c1c2c6c2c2e0b82c6c3c3c3c3c144d04010b1343c4d1344d1342d00141051314200aa00aaaa000000000000a0b07070707aa0000515555500100b00b0b2f02f0b0b0b0b0b00b0b0b0b0b0b0b0b0b000b0b02c7c1b06c0b02c0b8002e0b0b0b0b030b070b070b030b0b0b82e0b0b050b41042c2d0b1344d1342d0b444c050b141c01c0c00c0c0c0c0c0e000380c2c0c0c0c3c0c0c0c0c0c0c00c0c0c0c0c0c0c0c0c0e03030380c0c004c1300c0300c0c4c0c031044d1340d0340c0c4c0d03444ca070717530707820b0f0f0b81c1e070782132b132f030707031384cfe17131713131317133fa80c0c0d44c131404d1340455c1c01c1c1c01c1c1c1c1c1c1c01c6c5d4c5c1c1c1c1c1c1c001c1c4c4c4cac4c4c4cbc1c1c4c4c1c1c1c1c1c1c4c4c4cfc4c4c4c5c1104c1301c4c070704c1315078001e071b0707070f0707070707070781e0707071307030507410044d1341c4d070744d13400504141c5a703130f3f130f0f030b03070f07007073b0034b070307030300703031b030303030707000707131313231313133f03031303070707071313131303030303133f0441304c031301c4c1300c541e000386c6c0c3cec3c0c6c0c4c4c0cec0e0380cfc1c1c1c1c144d04011344d031341c4d1340d00141051314200aa00aaaa000000000000a0303030303aaa00005155555001007007030030303030303030030303030303030303001f07c030300c7c0300c038000e030b0303030f030303030303030380e0303050341044d1340c0d031340d03444c0503160a085c5c5c5e0a1785e1785e80284c2c4c3c4c3c4c2c4c0c4c1c4c1c4c0c4c5c4c004c1304c1304c8131313411344d1344d13644c4c4c44ca033b820b030f03aaaaa820b23130b0303133f0303030303030303133f030707030303aa50304c500344d0112782820b033b03a0aaaaaa00a0b0b133f13130b0b0303133f13130303a1313aaa0440b04c0304c84ca15a00a86ea0faaa07aaa1385c16410042d1340d136136900141270585a7033f1303130303172f0383e0a085c5c6e4b092e1785e1785e80284c4c4cfc4c4c4cfc4c4c4c5c4c4c4cfc4c4c4c4ea84c4c1104c1304c1304c4c84c5680286c6c5c3cfc3c5c6c5d4c5c1c5c1c5cfc4c4c4ea8144d04011344d1344d1313613400504144c5 24 16777215 10 1023
def hc_87_2 : Nat → Nat := unpackHintV5 0x7e01173b8add9d132c8daa37e6a34c732ec8b979d764b6e18257051b280cdd935e2a09272204698a821248a0fd030878818037f1141a94590bca60058c1642960c0126c9108723103c81c418517c09f48d045728c16ab040854c002028a003c314000078 0x1c01c1c01c1c1c1c1c1c01c2c2c2c2c1c1c1c1c002c0f01c0705c0b01e000782c0c3c3c3c3c2c0c1c0c1c1c1c1c1c0c5c5c2e0b85c5c141d0410b43d0741d1342d1070141c507007078001e071b0707007070f07a707070707070707070070b0b0b0b0781c1e070707070707078001e0b0b0f0f0f0f0b0b0707070707071b0707131307070707070307070707070313170b82e17170440b03c07070071b00701c1702c550042d0f41c1d41c4d41d0744d0b4005043c0c0c0e0a070380e80c0c0e082c3c3c2c0c0c0c0c0e80c0c4c4c0c0c0c0c0c0c0c5c5d43c031404d0340443c1c01c1c00c1c3c1e9c1c1c0c3c1e000381c1c1c0c6c3c0c01c0c3c0c3c0c0c0c0c0e030380c3c1e000783c2c3c3c3c3c3c2c0c0c1c1c1c1c0c0c0c0c3c0c3c3cfcbc3c3c4c4c0c0c3c0c4c5c0e0385c1103c0f00c0700c3c03c3c03c03154010f43d0341d030f50f1351340d001410f07070f0f07078280c3e81c1e0707820b0f0f0b03070703178ee85c5c5c5c4c4c5cecfc5c4c4c5c5c5d43c0f1404d1340443c1c01c1c01c1c1c1c1c1c01c3c3c3c3c1c1c1c1c003c0f01c0703c0f01e000783c2c3c0c3c0c3c2c1c0c1c1c1c1c1c0c5c5cee3b85c5c141d0410f43d0741d1344d1070141c5078001e0700707070f0700707070707070707070f07a7070070781c1c1e070f0f0f0f07070707078001e07071313070707070707070707073b0f0b0f0f0f0f0f0b070307070707070313173b84e171704407070f1f0070701c03c0f01c0703c0f15401070713135070741d43d0f41d0744d134005043c00c2c0c0e080e81c0e80c0c0e082c2c2c2c0c0c0c0c0e03a03171703131303030303030303171751700c501340d0115707007070030703070303007030b030b030303030440b03c0301c1b00c078001e0b070f0f0f0f070703030707070703031b170380e1b17051b410042d0f40d0744d03444c0513141c01c1c00c1c1c0c3c1c3c1e9c1e000381c1c1c0c3c3c0c01c0c2c0c2c0c0c0c0c0e030380c6c1e000782c2c3c3c3c3c2c2c0c0c1c1c1c1c0c0c0c0c4c0c6c6c6c4c6c4c4c0c0c6c0c4c5c0e0386c5c1102c0f00c0700c6c06c6c06c03154010b43d0341d03135131351340d0014100000703070300aaaa0000000000000b0b3f0f3f0f0b0b0303070707070303a0000000005555540005000802a1b83e802a0781e81c0c1c0c0a70202aaaa070000aaa3fa1313aa0b0b4b93134b0b0b0303070707070303aaaaa4b000000207c00000004000555644d55555540010000000707070700aaaa0000000000003f0b3f0f3f0f3f0b070307070707070300a000000055554500050000000707070720029eaaaa070a1ba83ea07a81e800000130b4b63134b4b0b0703070707070703aaaaa4b17aaa3fa1313aa000000000000207c04000555555555644d400100a0b03820b030703aaaa820b0f0f0b0303030303130703030303031b2f031313030303aa5031b0306c5003130344d0112782820b030f0382aaaa000b03c0306c88a00a0b0b0f0f0f0f0b0b03031b071b070303aaaa0590410b43d0344d9918058582a00a86e820b030f03aa07a8283ea7aaaaaa80282c2c3c3c3c3c2c2eaa86e84c4ea80c0c6c1c4c1c0c0eaaa81102c0f2821b00306c88550042d0f6961350344d990014127030b8207a030303030380e03820b0b0b0b0303030303030303171703131303030303a0350303c500344d0110f82820b0f0f0b8283ea7a0b0f85e17a00aa82c3c1c2c1c3c3c2c6c3e80282c2c3c3c3c3c2c2c4c0c5c1c4c1c0c4c5ea85c5c3c3c3c3c2c2cfc2c2c2c4c2c3c3c3c3c1102c0f03c0f03c80f0f00b0f0550042d0f44d1344d90f0f50b135001410fa030f8207030f03aaaa820b0f0f0b0303530703030303030303033f2b031313030303aa50303c500344d0110f82820b030f0382aaaa000b03c0303c88a00a0b0b0f0f0f0f0b0b03033f073f070303aaaa0590410b43d0344d99180585a00a82a0f8281eaa0b030f0382aaaa0fa9eaa802a84c4eaaaa8fc2c2c3c3c3c3c2c2c0c0d4c1c4c1c0c0eaaa811283c7c28802c0f00c0f2215401a13135a650b43d0344d99001410f00b038280c1e0303030380e03820b0f0f0b030317070303030303030303171703131303030303a0350305c500344d0113782820b0f0f0b8282e0b85e170440b03c1b05c172280282e0f0f0f0fa1b03170717071b03170faa0f0f051b410042d0f44d1344d91130144c582820b0f0f0b82a0b0f83ea785e17a00aa85c2c1c5c1c2c6c2c3c3e80282c2c3c3c3c3c2c2c4c0c5c1c4c1c6c0c4c5ea85c5c2c2c4c2c6c6c6c4c6c4c4c2c2c6c2c1102c0f06c1705c80b1b01b1b0550042d0f44d1344d90b1351313500141828207030703a00a86ea0faaa0aaa81ea7aaaa80282c2d4c8c4c8c2c2c0c0c1c1c1c1c0c0eaa8fc5e84c4eaaaaa81102c1f00c072821b088550042d1340d07696135990014127aa80ea820b030f03a80e082c8c8c2c0c0c0c0ea80c0c0c0cecfc0c4c4c0c0c0d40c1b1400d1340449e0a8281c0c1c0e0a1785e07a9e80c1e80280c6c1c1c0c3c1c1ea0307a00a130b3b2b132b2f0b03030707070703031317aa17170707070703033b0303031303070707070441f07c0301c17201c1c00c6c154011344d0341d13641c1d40c4d4005060a081c0c1c0e0aaaa8002c1f00c0722280282c2cec3cec3c2c2c0c0c1c1c1c1c0c0eaaa81641042d1340d076646016160a802aa0fa86e081c0c1c0e81e0aaaaaa81ea00a0b0b3b2b132b0b0ba1313aaaaa3b0303070707070303aaaa0440b07c86c2800c0722154010b44d84d6940d07664005049e0a82aaa082c0c0ea5e9e80282c2cec8c4c8c2c2eaaa80c0ced1c4cec0c0c1102c1f2200c1f154010b44d990344d00141270b03030f230b0b23130b03471b0337 25 33554431 10 1023
def hc_87_3 : Nat → Nat := unpackHintV5 0xda2a3ad1323ec84a3ac161baba79bab391baacf1a8a899169ef26a954a6a8e41c2855a3a7e41c6754a3e6e61ba69913460ca3259e1ba52f9ba4c11ba4571a83f11983b18fe36692c2e121629612c210a161c592c13f21a0f412c06ba220001ae 0xb0f0f0b00a0b0f83ea785e170000a85d7c2c1c5c1c2d0c2c3c3c000000000000000000b003c003001c01702002c0b0010c1f0000002d0f44d1344d90b13513135069c0006c000001c0c1c0c020f85e07a9e80c1c00000d0c1c1c0c3c1c1ea0327070000000000000000002c02b000c007005c0800701c000300c000001343d0341d13641c1d40c4d41a70003b000000703070300083e17a030781e2700005f43030f0f0f0343a80c1c1c000000000000000000b008c003001c01702000c030011c1f0000004d0f40d0744d90313513135069c0000000000000b0b0b0b0b070b030b070b03000b0b0b0b0b82c2c2e0b0b0b0b0b0b0000000000000000b0b42c3d0b0b50b0f51344d0b42d0000000000003c1c3c0c3c1c3c0c3c3c3c3c003e0f0f0f83c5c3c3c3c3c8cac9c8c0000000000000003c4d43c3d43c4d0f0f44d1344d1340000000c0c0c0c00000c2c0c0c0c3c0c0c00003030303030303030380c0c0e03030000000000000001343d030340c4d03035031350340d000000170f0f170083e1785e170000170b0f0f0f0f170b1703170717071703000000000000000004d0f44d1344c4d84d13135131350000000f0f00270f0f272700000000000000000007000800001343d1344d1344d069c0010540141c6c1d041c3c1e9c1c1c1c1c1c1c1d042c2c2c2c1e07570781c1c1c1c1c1c002c0f01c1c01c6c01c0705c0b100555555555541a750500542d50f541d075541d135540d507545d5951b4041410707030f070f07a75005070707030f0f41030b030b030303030380d5c0e031b000b03c0301c031b01b1b01b00c4015555555555069d4140150b543d503541d50340d551b44d551756546d010540161b9042c0c3c0ea3781e9060fa9eaaaaa000b03ca086c00c1b22100555555555541a750500542d50f56655644d5503541d595951b4041410b0f0f0b41a0b0f83ea785e175005a85cdc2c1c5c1c2c6c2c3c3c002c0f06c1705c80b1b01b1b04015555555555069d4140150b543d503541d51756542d0b5546d135546d0105041c0c1c0d40161ba83ea379416aa07a9eaaa000b07c0301ca086c22100555555555541a750500542d523540d50756655644d559595274041505070307034185e1781ea7a03075005031b0707030f0707a80cdc1c007c1f00c0705c807070031b04015555555555069d4140150b54ad503541d51756541d075540d03554ed01054016a0fa86d041c0c1c0e81d06aaaaa81e000b07c86c2800c0722100555555555541a750500542d52b5644d55995503541d59595274041505aa410b033303a37a7000b07c880307c401555555069d4140150b548d595950354dd52740415050703070350585e17a030781e5005371b030f330f031ba80c1c1c007c1f00c0705c8031b01f1b04015555555555069d4140150b548d503541d51756540d03554dd13555010540155410b0b0b0b0b070b030b070b03410b0b0b0b0b82c2c2e0b0b0b0b0b0b000b0b02c4c0b0b00b1301304c0b02c41555545055551450054155043c1c3c0c3c1c3c0c3c3c3c3d043e0f0f0f83c5c3c3c3c3c8cacac8c003c3c03c3c03c3c0f0f03c0f03c0f105415155555545105040c0c0c0d40140c2c0c0c0c3c0c0d54103030303030303030380c0c0e0303001304c030300c4c03030031300300c4155555545055144141171717174185e1785e175005130b130f130f130b130313071307130354004c1304c1304c4c84c131301313041555555554501400001b0f0f1b001b0f0f1b273b270000130b0f0f0f0f130b130313071307130313131384e1317000000000100015555540010041413333413333001f07c1f07c1f07c401555555069d414015555541d556550000001c1c1c1c02aaa80000000000003c2c0001c0c1c1c1c1c1c0eaaa80000015155540014002029c08000a81e07a0707070700aaaaaaaa0000aaa3fa1313aa0f0b0f0f0f0f0f0f0f0b4b0707070707070707aaaa000000207c00000004000555644d55555540010000000707070700aaaa000000000000000f0f00703070707070703aaaa00000045555500050020029c200001c1c1c1ea0781e802aaaaaaa800002c2c3c3c6c3c3c2c2c6c2eaa86e84c4ea81c1c1c1c1c1c1c1eaaa80000000081f0000010001555559135555500040000001c1c1c1c02aaa8000000000000bc2cec3cec3cbc2c1c0c002aaa8000001555154001400200a86e0fa029c0800707070700aaaaaaaaa0000aaa3ba1313aa132f3b2b132b2f2f070307070707070707033baaaa000000207c00000004000555644d55555540010000000703070300aaaa0000000000003f0b3f0f3f0f3f0b0007070aaaa0000005545550005000020029c1c0c1c0c286ea0fa0002aaaaaaaa800004cbd2c8c4c8d2cbc0c0c1c1c1c1c1c1c0c0d2c0eaa8fe84c4eaaaaa8000000000081f0001000155555559135550004001c1c2c2c1c1e082e80e070781c1e082c2c2c2c0c1c1c0c2c4c5e82e0b0b13130b0b0b0b0b0b0b17175170b1702c50130b1342d01157 24 16777215 10 1023
def hc_87_4 : Nat → Nat := unpackHintV5 0xd091d6cad96ec51172bf4972b93186b3497aaee918a891969f1a5e9821be9129be8a31be8461747baa2e75d9746d222e6671ac61e9225ba192522a5e4cd9544601b640c15039e9b632f1be2bf9be2501be1e899e17d9ac13512209aa6a00026a 0x20a085c5c6e80284c2c4c3c4c3c4c2c4c0c4c1c4c1c4c0e0a1785e1785c1604d001304c1304c1313131317204d044d1344d1344e4a013641344c4c969617179685e1785e17a44a131317130717071356584c4c4c5c4c5e84c4c4c13131544d1344d1359a7a5a84d1355551155550b030b030b0703030b07030355aaaaaaaaa550b0b0b0b0b0b0b02c7c2c03271b03aa55555555555555554455555542c1c0c0c2c1c0c0c2c0c2c0d56aaaaaaaa9542c2c2c0b0f0b02c2c2c2c0c3c3c0ea9555555555555555555540c0c0c0ccc0d51140c2c0c0c0c3c0c0d555aaaaaaaaa550b231f0b0303030303030300c7c0caa55555555555555541410b03330341aaaa50050b0b1b0f1b0f0b0b03031f071b0703038aa00440b0b06c0b0306c8a85505555554151454555542c0ccc0d56aaa9542c9c7c2c0c9c7c0ea95555559a7555554455555507565154565a580c0e0396aaaaa44aa0303aaa0303aaa59a960b0b0b0b03030303aa3b1b0f0ec6c3c550b42d0340da6613135070750f44da44a960303039603070303070303030303a7a44aaa81e07aa81ea82ea0ba80ea0396aaaaaaaa56581c7c1c07070702c2c2c2c0c0c0c0e6b8a8aa5507135070750b42d0340da17a5669c3d13696a582c0c2c0e5aaaaaa912aa03030b070b070303a59a960b0b0b0b030f0f03aa0b0f0b02c2c2c550b0b42c3d0344d990b0f50b0b50f43da5a960b030b0396aaaaaa44aa80c0c2c1c2c1c0c0e966a582c2c2c2c0c4c6c0ea82c2c2c0b1f0b1542c2d0b1340d136642c2d42c4d44d1365a9680c0c0c0e5aaaaaa91280c2c0c0c0c3c0c0eaa59a960b13230b03030303aa03030300c7c0c550b44d030340c4d9903035031351344d82820b030b0382aaaaa00aa08a0303430743070303a59a000b200c132202c2c281042d0b40d136644c4d44c4d444ca00a8202087c1c0c0c3c1c0c0c2c0c2c0e802aaa0f83eaa1faa0ba82ea07a88e0aaaaaaaa95000b0b0b0b0b002ca70304c84c28221044c4d43c4d42d0b40d13684e959a711320a080c0c0c0e0aaaaa80282c2cec3cec3c2c2e822a9668002c1300c88803030a0410b44d0340d99131350707511320a80281c1c1ccc1c1c1c2e080c0c0c0c0a00aa83ea1baa81e07aa81ea80ea0382aaaaaaaa54002c1300c0c0c0c0c00329e130a088410b44d07135070750340da13a5669c44c82820b036b0382aaaaa00a0b0b130f130f0b0b030313071307030305982020b04c0304c8a8a9042d1340d136644c4c04c4d01344c4c96960b0303a44aaaaa81ea96aaaa56582c4c2c0c4c0e8a8aa550b44d0344daa5669c4d13555540c0c0d5445070755503035555580e0380e03a0303a0303550b0b0b0b030303031f1b2b07c6cac03a0355555555555555555503030303030b03a754450307030303035580e0380e03a0303a0303550b0b0b0b0303030303030300c7c0c03a03555555555555669d5551150b542d503540d50340d5503555035151b45400002c2c2c2c020b82e0b82c0000000000002c2d554fc0c5c1c5c1cfc0c2c2c000000001555555000140000002c2c2c2c020b82e0b82c00000b29c000000000b003001c00b02000015555559a7000110000042d50b557d507542d00000005040150000030303030080e0380e03000000000000370b0f0f0f0f370b030355503030000000005555540005000000030303030080e0380e0300000000ca700000002c033000c00c080000555555669c00044000012f543d503540d5034000000141005555551155550b0b0b0b0b070b030b070b035582c2e0b0ba0b0ba0b0b82e0b550b0b0b0b0b0b0b02c7c2c1b17172f0ba0b555555555555555544555555543c1c3c0c3c1c3c0c2c3c3c2d5683c3e83c5e0b0f82c5e1785d543c3c3c0f0f0f02c3c3c2c3c3c3c3c3e83d555555555555555555540c0c0c0d51140c2c0c0c0c3c0c0d55580e0380c0e0303a0303a0303551f231f5f0303030303030300c5c0c03a0355555555555555555550b03170355aaaa54450b0b130f130f0b0b030313071307030355542c4c4c2c0c4c4c0ea84c4c4c13131315555555a765655505045ccc5c6d061785e1785d40146c2c6c3c6c3c6c2c6c0c5c1c5c1c7c0c4c4c205c5c1106c1b06c1705c5c8175505555554151454555545ccc5d561785e1785d547ccc7c7c5c5c5e85d555555559a755544555555075545515000000070f0700070f07a707070707070707000b0b0b0b0781d9c1e0707070707070000000000000000002c00f001c070001c1f0000c007005c0800000b43d07075071350741d1342d069c0006c00001c1c0c3c1c3c1e9c00001c1c1c0c3c3c000c2c0c2c0c0c0c0c0e03670380d0c000000000000000000b003c003001c00300c002b07c001702000002d0f40d0740c4d44c4d44d0341a70001b 24 16777215 10 1023
def hc_87_5 : Nat → Nat := unpackHintV5 0x80b1173e3a879e4e33ce9125871c8b03716739ae32a0d041b66444f730347b97273ccb229c4558ce2298051931f6849101fe41fda11df4c28dff3ec6891da2e358515247d89a53b44571ee1f04ed0e065f05836002529bc0c9580048e6f00c760000018e 0x20a80281c1c1c3c1c1c1c2e080c0c0c0d5a00aa8aea2faa81e07aa81ea80ea0382aaaaaaaa00002c1301c4c01c1c00c03284e808a7410b44d0303030303540da784d6966444c07507079101e0707070707070750707070707541d41cbc5c5c1e07070781c1c1c1c1c1d41cbc4c4c1c1c07070701c1c1c1c5c4c4d544d1341c1c1c1d50769c4d1344d13555540c0c0c0d5603980e035445a55503030303030303030303555550b231f0b0303030303a031f1b3b07c6cec5555555555555555550303030355a031780ea780e035445a80c0c0c0c0c0c0c0c0c0c5d542c8c7c2c0c0c0c0c0e80c2c5c5c171f0b15555550369d5555555551150b543d50350356542d0b5545d554546d1500000703070300030b030b030303030000000000000b0b55503030003b170380e3b17000000555545500050000000703070300030b030b03030303000007ca70000000007c00c007005c080000555541da755000110000042d50f544d59d594000000141005400000c0c0c0c020380e0380c000000000000ec2c3c3c3c3cec2c0c0c0000c0d55400000155515400140000000c0c0c0c020380e0380c000000008a700000bc023000c003000c000155550369d5400044000010b543d5035035650000000504015555544555541c0c0c1c0c0c1c1c0c0c1c1c0c0d540c2c0c2c0e0b0b0382c2c0c0c0c0d542c2c2c2c2c2c2c0b1f0b00c1c1c0c2c0c0c2d55555555555555551155555550707030307070303070303070303550383c3c0e0f17030f030f03030303550f0f0f03c3c3c0f0f0f0f030707030f03030f5555555555555555555030303035445030b0303030f030355540c0c0c0c0c0c0c0c0e03030380c0d544c4c4c4c0c0c0c0c0c0c0c03130300c0c0c0d55555a740d5035555555540c0c0c0d5560380e030380c0d51140c0c0c3c0c0c0c2c0c0c0ea030355547ccc7d9c0c0c0c0c0e80c0c5c0c030303155555555555555505041c0c1c0d040ccc0c6c0c0c0c0d40146c2c6c3c6c3c6c2c0c0c01c03031b170380e1f170441b06c030301c031b00c5505555554151454555541c0c1c0d540ccc0c0c0c0c0d547ccc7c0c1c1c0c7c0c0d5555550769d555551155555565455159696030b03a703030303a44a0307030303039680e0380e03a0303a0303a44a0b0b0f0f0f0f0b0b030303030303030303030303030313130303172f0303030356582c3c3c2c0c0c0c0c0c0c0c031f0300e80c4c5c3c130f1542d0f40d0340c0d40c4d59a7a5a83d1365a580c0c0c0e91281c1c2c2c2c2c2c1c0c0c0c0c0c0c0c0e5a0380e0380e9680d960b0b0b0b030303032b1b130ac6c4c03a03550b42d0340d0396940d91344d969603030303030b03a7a44a0307030303039680e0380e03a0303a0303a44a0b0b0b0b0b0b0b0b030303030303030303030303030313130303170303030356582c2c2c2c0c0c0c0c0c0c0c031f0300e80c4c5c4c131b131542d0b40d0340c0d40c4d59a7a5a84d1365a91282c2c2e582c2c2c2c2c1c2c0c2c1c2c0e5a0b0b82c2e82da582e0ba55a0b0b13130b0b0b0b0b0b0b0b130f131713131317131356582c2c2c2c2c2c2c0b130b04c4c4c4c2e82c4c4c4c4c4c4c4c4d542c2d0b136942e51344d669e96a1344d96a44a0b0b0b960b0b0b0b0b070b030b070b039682c2e0b0ba0b6960b82e582c2c2c2c2c2c2c0b1f0b06c4c5c4c2e82d542c2d0b136942e51344d0b644d1365a582c3c3c2e5a0b82e1785e91283c3c3c3c0c3c1c3c1c3c0c3c5c3e582c3c3c2c3c3c3c3c3e83c3c3c3c0f0f0f1542d0f44d1344d90b0b0b0f43da44a960f13139617070f030f0717030b0f0f0b96a5a1760b1782c5e1785e95682c2c2c2c2c2c3c3c4c3c2c2c4c4c4c5c4c4c4c5c4c4d5960f130f03c4c3c0b0f0f0b130f130f13a0f13130f0f13130f0f551396942c4d0f1344d1359a7a5a83d136912a583c3c3e583c1c3c0c3c1c3c0c2c3c3c2e5a9683d82c3e0b1785e17960f0f0f03c3c3c0b0f0f0b0f0f0f0f0fa0f550f96942c4d0f0f44d1344d90f43d96960b0b0b0b9682e0b82e0ba44a0b0b0b0b030b070b070b030b0b0b960b0b0b0b131313130ba0b0b0b0b02c4c2c550b42d1344d0b642c2c4c4d1365a580c0c0c0e91280c2c0c0c0c3c0c0c0c0c0e5a0380e030380c0e80da5961323130303030303030300c5c0c03a03551344d030340c4da503940d91344d9696030303039680e0380e03a44a030b0303030f030303030303030396131313130303030303a0303030300c4c0c551344d0340d03640c0c4c4d1360800c0c0c0c2c0c1c0e082c0c2c0c2c0c2c0c0c0c2c0c3c0c0c0c0c0e0380c0c0e642ca70b02c4c0c1302d1340c4e660a80280820b0b0b0b0b070b030b070b038282e0ba0b0ba0b0b82e0ba00a0b0b0b0b0b0b0b0b0b0b0b0b0b0b130f0b0b130f0b0b0b0b1313071307131354000b29c2c2c02c2c4c4c1302c81313013130410b42d0b0b50b1351344d669e96a11320a80282c2c03c0b0b820b0f0f0b17074303170743038282e0ba176961785c002c0f02c2c04c2c04c1304c8410b43da513944d1344d91132802a0808217070f030f071f030b0f0f0b82a0f17a171782e0b85e17a00a131f130f0f130f0f0f130f131313130b0b0f0f0f0f0b0b132313071307131354002c2c2c2c2c00b29c4c1304c8131301313041131350f1350b43d1344d669e96a11320a8029dc2ddc3ddc3ddc2e080c0c0c0c0c0c00c0c0c8280e03a5a0360380c004c1304c1c01c1c00c0300c8411344d0396940d0340d911320a080c0c0c0e80280c2c0c0c0ccc0c0c08280e0380e03a0303a0303a00a131b130f130f1313030303030303030303030303030313130303130303030354004c1300329c0c0c00c0c1c0c81313013130411344d0340d0303503135669e96a11302c0e9c0c0e081c0c0c0e082c3c3c2c0c0c0c0c0c0c0c0c4c4c0c4c6c0c0c0e0380c440c0c00c3c6c130f03030344d880f13 25 33554431 10 1023
def hc_87_6 : Nat → Nat := unpackHintV5 0x8d151a42c6f120264f4f8623475ada138d87f9acb684ce4206641cc12e90df963145ca3937e4ec4c1252c8d911261080f9e63e24961d80648dcb3d466b1ea2fb0ea1604750a532bc48728a1f25450de46b85c64b025ba1e0e811703c2df80ba49c000174 0x1d41c0d40c0c0c0c0c0e440380c3c0c0c0c0c0d40c0c0c0c0c0c0c0c0c0e03030380c0c1d41c3c3c3c3c0c0c0c0c0c0c0c030f0300c0c0c0d543d0f40d0340c0c4c0d0343d0f41e440781d41c0c0c0c0d40c0c0d40c0c0d03030303030303075503030323030b03230303030303030303540d40c0e03030380c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1d41c3c4c3c0f130f03c3c3c3c0c0c0c0c0c0c0c3c0c4c0c0c0c0c0c0d544c1d41c1d44c4d0f1350369c0c0d40c0c1c0d0343d1341e440781d41c0c0c0c1d40c1c1d41c1c0d070303070303035070383c3c0e0f17030f030f03030303075070f0f0f03c3c3c0f0f0f0f030707030f03030f550f075070750f1343c3d0341d1340d0f43d075070350303030303039100e030b030303030350303030303030303030380c0c0e0303075070b0b0b0b0303030303030300c4c0c03030303550b42d0340d0303130340d1344d969603030303a44a030b0303030f0303565a03a9e80c5e0380e80c0e80c0e912aa03030303030303030303030303030f0f03030b0b03030303030317960b0f0f0b0303030303030300c0c03a030f170b02c7c3c550b43d40da70303503030703643c4d42c4d43d1365a912a80c0c0c0c0e96030303030303503030365a0380e80c0e80c0e0380e582c4c8c2d6c6c4c5b1b1300c0c0c0c0e80d542d1344c1d41c1d40d0340d91344d969603030303a44a030b0303030f0303565a80c5e03a9e0380e80c0e80c0e912aa03030303030303030303030303030b0b03031703030303030317960b13230b0303030303030300c6c0c03a030b171305c7c2c550b44d40da70303503030703642c4d44c4d44d1365a580c0c0c0e5a0380e030380c0e91280c0c0c3c0c0c0c2c0d03a940c0c0e584d8c4c0c0c0c0c0e80c0c5c0c0303031544d1340d0340c4d80d03075030351344d8200303030382c0c5c0e80c0c0e080c2c0c2c0c0c0c2c0c3c0c0c0c2c0c2da40c0c2ca70b02c4c4c0302d1344c0c1d0341c01c1e00078007003070307030707030307070303078000e0b0b030f0f0f030b0b0b130b030f03030f0f130f030b0303540c01c0c2c0c2c0e0b170382c5c0c0c0c0c0e030380c4c001329c3c7c03c7c4c0c0700c4c04c4c04c031042d0f42c4d43c4d50769c1c1d41c1c1c4d03444c07007078001e030300f04c0c1c00c1c0c1c0c1c1c0d0707503007030f03230388c5c0e231703030303000f03c130b0130b00301c1300c411343d07075130750341d1340d11301e000781c01c007003070703030707030307030703078000e131f13030f03030f0f130f03130303130b030f0f0f030b540c01c0e0f170387c5c0c3c0c8c0c0c0c0c0e03630380c4c003c7c4c3c7c01329c0c0700c4c04c4c04c031044c4d43c4d44d0f50769c1c1d41c1c1c4d03444c820b0f0f0b1103a9e0f80e0382a130b0b0f0f0f130b0b0f0f0f03030303030f030303030f0b00b0f1b01c0703d1343c4c1c01c1e000784c2c4c3c4c3c4c2c1c00c1c0c1c0c141c0340c01c0c0c6c0e13170384c4c0c0c0c0c004c1300c0c0c0c0c0700c4c031044d1344c1d01c1c00d0744d0341344c4c828203030303a00a030b0303030f0303560a0380e0380e80c0e80c0e80285cbc5c5c5c8c5c5c0c0c0c0c0c0c0c0c0c0c0c0c0c0c5c5c0c0c5c9c0c0c0c0c0001304c0300c0303003130229e82a411344d40da70303503030703644c4d44c4d444c075070750307030703079100e0303540d41c0c0c0c0c0c0c0e030380c1d41c4c4c0c1c1c0c0c4c130300c0c4d544d1350769c1c1d41c1c1c4d0344d13400000c0c0c0c02aaa80000000000002c2c3c3c3c3c2c2c000c0c1569400000155155400140000000c0c0c0c02aaa80000008a70000000bc02b000c0030200005540da75555000110000042d50f540d6565000000050401555544555541c1c1c1c1c1c1c1c1c0c1c1c1c0d542c2c2c2c2e0b0b0b82c2c1c1c1c1d542c2c2c2c2c2c2c0b1f0b01c1c1c1c2c2c2c2d5555555555555555115555550707070307070703070707070707550f83c3c3e0f170f0f0f0f07070707550f0f0f03c3c3c0f0f0f0f070707070f0f0f0f55555555555555555550703070355585c5e331780c1e07035445170b170f170f170ba070707070395551f331f2f0307070317a1717171705c7c5c555555555555555414107070707411b1733170707070750051b0b1b0f1b0f1b0b0701c1c1c1c05c5c7e1b85c5c1106c7c1b0bc1c07070705c1b15415555550545151555507070707552f17331707070707551f331f2f07070707171f17555541da7555555544555541d5595154541c1d41c1c1d41c1c1c1c1c1c1c1e440781c1c1c1c0d41d0703075070f0f0f0f070707070f83c5c3e0f0f075070f0f0f0f070707070f0f0f03c3c3c0f0f0f0f550f1343c3d0741d0f0350f1351344d0f43d07075070707507070707070707079101e070707070350741c0c1d41c2c2c2c2c1c1c1c1c2e0b0b0b82c2c1d41c2c2c2c2c1c1c1c1c2c2c2c0b1f0b02c2c2c2d542c2d0b1341d0742c0d42c4d42d0b44d1365a580c0c0c0e91281c1c3c3c1c1c1c1e966a5aaaaaaaaa582c3c3c2c0c0c0c0cac6c3c2b1b0f2a9542d0f40c0d90303035a5990f44da44a96a17a44aa0707aaaaa070707070f0707070b9680eaa0303030303565aaaa85ea7aaaaaa9687e2a02c3c3c2c1d4c1c07070700c0c0c0ea956135a50b43d0303030303540da7990f44d96960703070381d60785e1780c1e0703a44a170b170f170f170ba50740e070707962f1363130307070317a1317171305c7c4c551344d0341d131361340c0d44c4d44d1341c01c1c01c1c1c1c1c1e000781c1c01c0707070350741c0c1c01cac3c3c5c1c1c1c1cae17172b85c5c003c0701c0704c2c01c1c04c131044d0f41d0744c0d44c0d44d13444c078001e07007001e000781c1c1c1c1c3c1c3c1c1c1c1c1c7c1c1c1c1c3c1c1c1c2c1c01c1c1c1c0c1c1c1c0c1c1c1c1d5070071f83c5c3e17172b0f0f170781c1c1e076307070707000f1f130f1f004ca707130070700701c1304c41131350f1351343d0707130707541da71344d11301c01c1c01c1c1c1c1c1e000784c2c4c3c4c3c4c2c141d0701c01c6c5d4c5c1c1c1c1c4e13131384c5c07001c4c1301c07070701c1c1c4c131044d1341d0744c0c04c4d04d1341344c4c82820303030382aaaaa00a0b0b370f370f0b0ba59aa08a000b04c0300c881313007070410b44d0366640c0d69444c 25 33554431 10 1023
def hc_87_7 : Nat → Nat := unpackHintV5 0x827cd73eee941e9a374ec8a126fb9a336286d1a47334c922466035172c9cdf953745c9bc37e47d18422745d102345c78aa1c39a8ab1b36678c5e4f45d71602b1ce7143a55094236c420a021d38f30c8e8385553c825016a0f08de063e51813d78800027a 0x969607030703a44aa59a030307070707030396aaaaaaaa960b0b0b0b030707032b1b0f0ac6c3caa550b0b642c0d0742c2d696643d136912a595a44aaa83e0faa8aea82ea0b96070703030707030307030703a0796aaaaaaaaaa07a583d4c3c0f2b0f02c2c2c2e1f8a803070703aa550b0b0b0b0b542da784d6940d076643d136912a595a5aaaaaaa96232303030f2303030b030b03a23a7960f530f03c8c3c0b0b0b0baa030f2303550b0b0b0b0b542da7990344d0f44d96a44a030350f42c0e9681c0c1c0c1c1c0e0707a81d60782e0ba1707a070780e03960b0f0f0b231b0f08c6c3c0307070317a0f550b43d0b0b5130b50341d13643d136912a595a5a07070303070703030703070381d607a0f17a171782e0ba030781ea44a232323030f03030f0f230f032303030b0b030f0f0f030ba80c1c1e583c3c0f230f02c3c3c2c0c1c1c0c5e83c0c7c3c231f031542c2c2c2c2d50b69c0d0744d903135131350f44d000000280000280080095002002070707070707070707070707002002aaaaaaaa029c00003c1f000000000000100143d43d55a75555008214a07030703070783e1781c1e53820b0f0f0b0f1f1b0f03030f0f0f0f0303a0707a0f0f0f0f0f0f01f0f1b02c0b04d1343c4c3c03c3e000f8143d0f1ac1bc3c3c3c3c3c1c3c0c3c1c3c0d4c1bc3c3c3c3c3e0f0f0f83c5d4dad4c1f003c3c0f0f0f03c3c3c3c0f03c0f1043d0f43c2c03c3d04d1344d1340f43c4c07007078001e030350f43c0c1c00c1c0c1c0c1c1c0c0707003007030f030f0388c5c0e231703030303000f03c070700f0700301c0f00c410f43d130b5130b50341d1340d10f01e000781c01d507003070703030707030307030703078000e0f0f1f030f03030f0f0f0f030f03030f0b030f0f0f030b000c01c0e0f0f0383c5c0c3c0c3c0c0c0c0c0e03630380c7c003c3c03c3c03c0f00729c1c1c01c1c1c3c031043c3c4c3c3d50f69c0d0740c4d44c4d44d03443c070070700707070707078001e070750741c1c1c0c01c0703070070f0f0f0f070707072b85c5cae1717000f03c0701c0f0300f0300f03c410f41d0741d130b5070751344d10f01e000781c01d5078001e07070707070f070f07070707070f070707070f0707070b07007070707030707070307070707001c01c3e0f0f0f83c5c3c3c3c3c1e07070781d8c1c1c1c1c003c3c03c3c03c0f01c1c3c1c1c00729c3c0f1043c3c4c3c3d50f69c1c4d41c1d41d0744d13443ca00a8256083c1c3c0c3c1c3c0c2c3c3c2e0a83c3e83c5e0b82e1785e80283c3c7c9c3c3c3c3c3c3c3c3c3c3c5c5c2c2c3c3c3c3c2c2c5c8c5c1c5c1c5c7c0000f0f00f0f00b03c0f03c229e82a410b0b0b0b0b542da71344d13644c4d44c4d443c82820b030b0382aaaaa00aa59a0303670767070303a08a000b02c0303c880f0f00f0f0410b640d136642c2d69443ca00a8256083c1c0c0c3c1c0c0c2c0c2c0e802aaa0f83eaa0faa0ba82ea07a88e0aaaaaaaa80000f0f00f0f00b02c0303ca0fa0229d042c2c2c2c2d50b69c0d136135a59910f03d43c2d42d5a70b50b54569cad48c3c3c3c3c2c2c2c2c2c2c2c2c2d42c2c2c2c2c2c2c2c2c2c2c2c2c2c2c2c2c3d43c3c3c3c3c2c2c2c2c2c2c2c2c3c3c3c3c2c2c2c2c3e4483d555070f0f070f0f583c3e0f0f50f0f0f03c3c0f0f0f0f0f0f0f0f55131355a71344d1344d0f44d5555070307035582e0b80e551142c2c0c0c2c0c2c2e95541c1d555542c2c2c2c0c1c1c0c2e82c7c6cdc1f1b37155555555555555555541c0c1c0d5560b82e80c1e0782d51142c2c0c2c2c2c0c2ea030707550b0b0b0b030707030ba0b031b3707c6c0c555542da75555555555544542d40d03541d07542d17566540d03554dd554551500000703070300030b030b0303030300000000000000b0b000030355537170380e371700000054555500050000000703070300030b030b0303030300000001ca700000002c00f006c15c0800005543da75555000110000043d40d507545d594000000141005400002c2c2c2c020b82e0b82c00000000000002c2c000fc0c5c1c5c1cfc0c2c2d55400000151555400140000002c2c2c2c020b82e0b82c000000008a7000002c00b00dc007002c0001550b69d555400044000010b503541d50b565000000050401555569da7555543c3c3c3c2c2c2e9c2c3c2e9d542c2c2c2c2c2c2e9c2c2c2e9c2c2c2c2d543c3c3c3c2e9c2c3c2e9c2c2c3c3c3c3c2c2c2c2d550f62d0b55555555551155550b0b0b0b0b070b030b070b03550b0b0b0b0b82c2c2e0b0b0b0b0b0b550b0b0b0b0b0b0b02c4c2c130f130f0b0b0b0b55569d0b542d55555555555030b030303035445030b03030307030355540c0c0c0c0c0c0c0c0c0c0e03030380c0d542c8c7c2c0c0c0c0c7c0c0c0c0c031f0300c0c0c0d55555555555555555542c2c2c2d5560b0b82c2e0b0b82c5d51142c2c2ea0b0b0b030b070b070b0355542c2c2c2c5c5c5c5c2c5e82c2c2c5c2c0b0b0b155555555555555556070782d042c2c2c2e81c1d042c02c0c1c1c0c2e82c0c6c0cdc7cfc7c6c6c0c7c0d42c2c6cdc07c6c6c55511541410b0f0f0b410b0b0b0b0b2f0b50050b0b00f02c2c6c0c7c1c6c1c7c0c6c5c2e0b87c5c1102c2c0f02c6c1b06c0b1541555555054515155550b2f2f0b550b0b0b0b0b2f0b550b331f0b1f2f1f1f0b0b55555a755555554455550755595154541d41c1e440780c0c0c0d40c0c0c0c0c0c0c0c0c0d030350307550303030303030323030303030323030f540d40c0c0c0c0c0e03030380c0c0c0c0c0c0c0c0c0c0c0c0c0c1d41c2c4c4c2c2c4c4c13130b00c0c0c0c0c0c0c4c0c4c0c0c0c0c0c0d542c4d131341c1d44c1d50369c0c0d40c0c1c0d0344d1341d41c1e440780c0c0c1d40c1c0c0c1c0c0c1c1c0d0707503507030b030b0382c2c0e0b0b03030303075070b0b0b0b0b0b0b02c7c2c030707030b03030b550b0b42c4d070750b0750341d0b40d1344d 25 33554431 10 1023
def hc_87_8 : Nat → Nat := unpackHintV5 0x8608ee41de49a0063a4f921c47a44933b14839cf724ce2e1366d111832b4f517707a8b808de57014128f0a412bd6ec8baa903ef1b91e28540e0a4286b115032eca717408d8a6d4cc46d3262128900e7e8586633702a3a381128fd05b2b881a74c800034e 0x41410f0f0f0f410f0f0f0f536b5350050f03c3c3c3c03c0c3c1c3c1c3c0c3c5c3e0f83c3c1103c0f0f0f03c7c0f03c3c7c0f03d541555555054515155550f0f550f0f550f0f0f0f1f0f1f0f1f0f1f0f5562da755555555544555507555951545568015815558001555041c1c1c1c1c1c1c1c1c1c1c1ea0781e906aaaaaaaaaaa8003c3c03c3c03c0f2820f00701c8850543d43d55a75055555514500560069d55954041070707070707070707070707a81e07a41aaaaaaaaaaaa000f0f00f0f00b02ca083c01c07221050b50b5555555555514415005a55541070707401c0d1506aaaaaaa8003c0f0ac6c0ac6c01c072210555555555545165005aaa2ba0f0faa41a82e0fa541a706001c1c1c1c1c0c1c1c1cac0c1c1c1c1d06aaaaaaaaaaaa802821f00f6b00f2b00f03c0701c884155554ad4ad55a7555514415005a5554140c1c0d501c1c106aaaaaaa8003c0f08c6c08c6c00c0722105555555555451415042c8c2d050303070303507106aaaaaa8003c6c0f1b02c0b00c07221050b50b555a755551450054155801a7070707070303070703230303070307035a23aaa0f83eaa0baa0f83e8041aaaaaaaaaaaaa000f6f00f2300f03c0301ca087c22105235235569d5555591355514070755070707507541e440781c3c1c0c1c2d41d0707070750707070f070f07070707070707070f070707070707075070f470f0f0f0f0f170f0f0f0f0781c8c1e070707070707075070f0f0f0f0f0f0f0f0f0f0f0f07070701c3c1c070707070f0f0f0f550f0f130f0f543da70707507135071341c1d1344d0f43d070755070707507541cad40c8c1c1c0c3c0c0c1c3c1c3c1c0c3c1c3c0c1e440381c1c1c1c1c1d43d030b030f0f0350703030f0f03030f77030f030f030303030380cac0e0323075070f0f0f0f0f0f0f0f0f0f0f0f03070703030f0f03c3c0c0f03030f550f0f130f0f543da7031341c4d030b5131351340d0f43d5906983e401a03035506aaaaaa802203c0f00c0322105555555554501d41c0d40c0c0c0c0c0c3c0c0e440380c1d40d03030303030350303030303030303030380c0c0e0303075070f0f0f0f0303030303030300c7c0c03030303551343d030340c4d03035031350340d0f44d075070750707070b070707079101e070350741c0c1c0d41d0703075070b0b0b0b070707070b82c2c2e0b0b075070b0b0b0b070707070f0f0f03c3c3c0b0b0b0b550b0b41d0b0741d0b035070350b42d0f43d079101e075507541e440781c3c1c1c2c1c1d41c1c1c1c0c1c1c1c0c1c2c1e9c1c1c1c1c1c1c1c1d41c2e0b0b0b82c2c2c2c2c2c1e070b0781c1c1c1c1c1c1d41c3c3c3c0f0f0f02c2c2c2c1c1c1c070f0701c1c1c1c2c2c2c2d542c2c2c2c2d50b42c1c1d41c4d41d0742d0b43d0f41d41c1e440780c0d42d07030750307030b070b0307070341c1d40d41c0c2c0c2c0e0b0b0382c2c0c0c0c0c1d41c2c2c2c2c3c3c3c0f0f0f00c1c1c0c2c0c0c2d542c2d0b42c1c1d42c1d40d0742d0343d0f41e440781d41d50750307070303070703030707030b070b07a7079100e0b0f0b070707030f0b035070382c2c0e0b0b030b030b030303030380c2c0e030b075070f0f0f03c3c3c0b0b0b0b03070703030b0b02c3c0c0b03030b550b0b0b0b0b542da70341d030b50b1350b40d0f43d415005a5554107030703070703030707030341a90a45aa000b02c4b1b04b1b00301c8841555555555514594016aa92e83c3ea906a0b82e9541a81e07a070703030707030307030703069c180aaaa92eaaaa81c02821f00f5300f4b00b02c0301c8841555542d42d55a7555514415005a55541070707070707070307070703416a54a0aa000b03c4b1b04b1b00701c8841555555555514505410b4b0b4107070707070707070707416aa58aa000f1b03c6c0b02c0701c884142d42d5569d55545140150554107070703070707030707070760069eaaaa4b85eaaaa075a4baaa0f83eaa0baa0f83ea07a81e80000f6f00f4b00b03c0701c88a087c1050b50b5569d5555555913514a55a9656912a0f85e0b59a960f4703030f0f03030b030b03a88e07aa5a83e0faaaa0baaaaa960f0f0f0f0f0f0f0f0b0b0b0ba883e00c3c3c0ea9542c2c2c2c2d50b69e961350344d84da43d0f6956a595960f170f0f0f0f0f770b0f0f0b92d64ba0f0f0f0f83e0f82c3e0f0b85e17a44aaaa50f42c2c5c8c5c1c5c1c5c8c3c3c3e583c3c3c3c3c3c3c3c2c3c3c2c3c3c3c3c3e83c3c3c3c0f0f0f1542c2c2c2c2d50b69c4d1344c4d84d0b0b5131350f43d5906982e41aa07030703401a179503030707030300880b02c0301c1705c415555555551496960b0f0f0b961782c3e0f0b85e17a44aa50f42e17031707170717030f0f0f960b0f0f0b170f170f17a0f17170f05c7c3c550b43d1344d131361342c2d44c4d43d1365a582c0c2c0e5a82eaaaa44aa59a03032b072b070303a59a960b0b0b0b030f0f03aa0f0f0f03c3c3c550b0b642c0d136642c2d6943d0f6912a5595a44a83e82e960f0703030f0703030b030b03a88e07a96aaaa82ea7aaaaaa583c3c3c0f0f0f02c2c2c2ea20f8030f0f03aa550b0b0b0b0b542d0ba584d40d136643d0f65a91282e50b6a582c2c2c2c5c1c8c0c5c1c8c0e5a0b0b82c2e82da582e0b960b0b0b0b0f0f0f03c3c3c0f0f0f0f0ba0b550b0b42d0ba50b944d1342d90f43da44a9656583c1c3c0c3c1c3c0c2c2c2c2e5a82c2e82c2e82c2e0ba9e0b82e91282c3c2ea0b230b070b070b0b0b0b0b960f0f0f03c3c3c0b0b0b0b0f0f0f0f0ba0b0b0b0b02c3c2c550b0b0b0b0b542da71344d0b642c2d42c4d43d0f6912a59596070703030707030307030703a44a88e17aa83e0faa82ea0ba88ea5aaaaaaa81ea7aaaa583d4c3c0f230f02c2c2c2c0c1c1c0ea21f8aa550b0b0b0b0b542da70341da584d6643d136912a595a5a07070303070703030703070396a0f17a171782e0b81ea7a0307a44a032b030307070707030f030307070707030b0707030f0707a80c8c1e583dac3c0f2b0f02c3c3c2c0c1c1c0c5e83c1c1c0c031f071542c2c2c2c2d50b69c0d0744d907075031350f44d 25 33554431 10 1023
def hc_87_9 : Nat → Nat := unpackHintV5 0xeda984eab8bce6890cde4212d45a7acbca24c3920ec20862b4d34eae51a0a8617c9f8a369981828b8b7e85997c799b007201e6685a6a5ea26e57c9b64eea384781da3df2643859663141c62c214825a99e1c6a5014d1e60d29ea0629c000018a 0x105041c1c1c1d06aaa9042c6c6c6c6c6c6c7c1c1c1c1ea940142c6c6c1c1c1c1c1c1c1c1eaaa86c6c6d00555555414151505041c1c1c1d06aaa9047ccc7c1c1c1c1ea90055555541505041c1c1c1d06aaa8007c1f01c07221401a7555555145555507541d59594155001054015560069c1c0c1c0c1c1c0c0c1c1c0c0d682e0ba83e33a82e0baa8be33aa0106aaaaaaaaaaaa8002c2302cbc04dbc00c072821b08841569d23548d55555555140750703503030b03030303039100e0340c0c0c1d40c0c0c0d40c0c0c0c0c0c0c0c0c0e03030380c0c1d41c2c4c8c2c0c0c0c0c0c0c0c031f0300c0c0c0d542d1340c0d031340c0d40c4d40d0344d13505401554107070707070707030707070360069eaaaaaaaa075a0b82ea0b8cea0b82eaa0b8ceaa07a81e80000b02c0b0b00b6f00701c88a086c1055a742d50b555555554525a582c2c2c2e5a0b0b82c2e0b82e91282d0ba942c0c2c1c2c1c2c0c2c2c2e582c2c2c2c5c4c5c4c2e82c2c5c2c0b0b0b1542d0b44d1342c4d82d0b0f50b0b51344d0b0b331f0b0b03470300c0e9e5a91295a5a07030703070703030707030381d60782e0ba0b0ba0b0ba030781e0ba44a0b0b030b0b0b030b0b0b0b0b030b03030b0b4733030b0303a80c1c1e582c2c2c2c2c2c2c0b0b00c1c1c0c2e82c0c6c4c1b031550b69c2c2d42c2c8c0d0742d903135131351344d000080080000280000295002002070707070707070707070707002002aaaaaaaa029c0000000000000001001569d0f543d5555008211a07030703070782e0b81c1e0b82131313130303131f1b1303030b0b0b0ba07070b0b0b0b1304c1303c1344d1313138004e0f00b050f02d2f06f13071303130713030b0f0f0b0b06f0b84c5c2e13130b0b0b0b0b2f0b000b0b0b0b0b03c0b1304c1302c41131340f0f00b43d1344d1342d04d131320940c0c0c0e0b031703a03030382030b030b0303030b03170303030b030b2803030b04c13030700c0b69c2d0b0f1340d07007078001e541c00c1c0c1c0c1c1c0c0c1c1c0c0c1e000382c2c0c3c3c3c0c2c2c2c4c2c0c4c0c0c4c4c6ccc0c2c0c0c003007030b030b0382c5c0e0b13030303030380c0e031b000b03c0b1301313001ca7070700707071300c4143da70f0f50f0f0f0341d03135131351340d11320940c0c0c0c2c0c1c0e082c0c2c0c2c0c2c0c0c0c2c0c5c0c0c0c0c0e0380c0c0e202c1300c4e202da70b42c3c0d1360a80295820b0b0b0b0b070b030b070b038282e0ba0b0ba0b0b82e0ba00a0b0b0b0b0b0b0b0b0b0b0b0b0b0b17170b0b1b270b0b0b0b1717071707171b00002c0b02c2c02c4c04c1308a7a0a9050b69c2c2d42c2c3c4d1342d913135131351130cd42cce440b952f50b2f2f0b0b072f2f070b0b50b0b0b0b0b82c2e0b0b2f0b5130b13330b0b1304c2c132f130b0b135562da7135131344d1342d1344d555445070b0755070b07a707070707070707550b0b0b0b0781c2c1e070707070707550b0b0b0b07070701c3c1c070707070b0b0b0b5542da7555555555555544542d41d40d507542d595150f455555541c1c0c2c1c2c1c3d51141c1c1c0c3c2d540c2c0c2c0c0c0c0c0e030b0380c2d542c2c2c2c0c1c1c0c0c2c2c0b0f0302c0c0c2d550b69d55555555555551150b503541d50b50b5654543d1555544582e550b030b03a88e07a5582ea7aaaaa9542c2c2c2ea20f8030f0f03aa5542da7555555555555544542d6503541d59595150f455555542c2c2c2d5682c2e0b83e0b82d5116a0b230b070b070b0b0b0b0b550b0b0b0b0f0f0f0f0ba0b0b0b0b02c3c2c5542da7555555555555544542d40d507542d5950b5150f45555541c0c1c0d51160ba82ea239556aa07a9eaaa550b0b0b0b03070703a887e2a9550b69d55555555555551150b503541d599559175565654554d1555555070307035582e0b81ea7a03075445030b0707030f0707a80c8c1d542c3c3c2c0c1c1c0c5e83c1c1c0c031f071550b69d55555555555551152b503541d51756541d075540d0355455ad15555445a0b0baa5507030703070755555aaa555a6550b0b0b0b1f1b0f07c6c3c03070703aa5542d555555555555555116a0ba82d541c0c1c0e81d56aaaaa81e550b0b0b0b87e2a00c1c1c0ea9550b69d55555555555551150b5955665540d507565654554d1555555aa550b030b03a23a7550b0b0b0baa030f1f035542da755555555544542d656540d52354554d155555070307035582e0b80e551142c0c3c3c3c3c0c0e95541c1d555542c3c3c2c0c1c1c0c5e83c7c6c3c1f1b0f155555555555555555541c0c1c0d5560b82e80c1e07951142c2c0c3c3c3c0c2ea030707550b0f0f0b0307070317a0f031f0f07c7c0c5542da7555555555555544548d40d507545d5950340d5523555154555115555550f070f030f070f030b0f0f0b550b83c3c2e0f170b0b0b0b0b2b0b23550f0f0f03c3c3c0b0f0f0b0f0f0f0f0f0b0b0f5542d42d55a75555555555030303030f03544503070303030f030355540c0c0c0c0c0c0c0c0e03030380c0d543c3c3c3c0c0c0c0c0c0c0c031f0300c0c0c0d55555555555555555542c3c3c2d560b0f83c2e1785d511683c3c3c3c2e170317071707170355542c3c3c2c5c3c5c3c5e83c5c5c3c171f0f155555555555555556070794d042c3c3c2e81c1d040f0f00c1c1c0c5e83c0c3c0c3c3c3c7c3c6c0c3c0d43c3c0c0c5c3c0c3c6c0f030555115 24 16777215 10 1023
def hc_87_10 : Nat → Nat := unpackHintV5 0xae8132a66208a2a0f09e212096c1d89300f08e81208691fc81594e7c214e76a95e7149586d98ec6811626249725c81725422184f19424a51324192303bf9663459e82fe11e2b61202379fa1ef92016ea041378dc0df16208696206289000018a 0x1c0c1c0000070700003030000082e0b80e03a2b17a2b1700000000000000555555555500000007070333070707a700000707070307330082e0b80e03a034fa0337000000000000069c015555555375554000002c00f000c007000c03000ac0005c080000040000072f070b00a8aa00095130707139500000000000000b000020004c000000072f070b00a8aa0000a0004b03070707074b03a000000000000000005555555555000000072f070b00a8ceaa7aa0000a85cdc1c1c1c1c2cde8cc0000000000001a70055555555553d5000000b003c003001c080800b02c004f0000000400000703070300aaa8000131313139595000000000000000030020004c0000000703070300aaa80000370b330f330f370ba000a000000000000000005555555555000000007030703000aaa81ea80000de6c0ccccccc0cdeaa07000000000000069c015555555553754000002c023000c03001c070205c08800300c003700000004000000000001c2c1c2c1c1c2c0c1c1c2c0c020b82e82c2e82c2e0782c000000000000015555555555400000000000007070f0307070f03070f070f00a0f0fa0f1783e0f81e2300000000000000555555555550000000030303030000030b0303030f030300020380e030380c0e80c0e80c0c00000000000001555555555540000001c5c1c5c002aaaa170000170b170f170f170b17030707070717030000000000000001555555555540000001ccc1c0233a078000000001a70055555500000000001c0020000010000000000007070f0307070f03070f0f070f00a0f17a0f0f83c3e0f81e230000000000000005555555555500000000000001c2cbc1c2c2c1c1c2c0c1c1c2c0c020b0b82c2e82c2e82c2e0782c0000000000000015555555555400000000c1c0c0c0c0c00000c2c0c0c0c3c0c0c00080e0380c0e0303a0303a030300000000000000055555555555000003c3c0002cbc00070000c001c1c1e9c1c1c0ccc0bcbc000000c0c00001c1c1c0c1ccc800170083e2f80e03a034fa0333000000000000000004001a755555555550000000070707a701c1c0c3c0003c3c8c0c1c3c020f83e0380e032b80c8c0000000000001555555554000000000001c1c000000c0c1c0c1c00a2b17a2b1782e0b80e03000000000000005555555555000003c0002c2c0001c1c0000c0c001c1c0ccc1c1c1e9c0ac000000c0c00001c1c1c0c1ccc800170082e0b80e03a034fa034f000000000000000004001a7555555556d13555000000007170717000aa85eaa170000170b170f170f170b1703070707071703000000000000000015555555555400000f0f0000b0b0001c000300070f070b200200aa9ea33aa00b0b000000f0f0000a82dcc1c1c1c1c3cce8cc0000000000000000100069d555555555400000001c3c1c3c02aa72a0faa0000f0f4f172307070b23a0f000000000000055555555500000000000a0007074f0307074f03072f070b00000aa8aa000000000000005555555555000003c0002c2c00070000c001cbc1c2c280021700a8ceaa7aa04f000000b0b0000a85dcc1c1c1c1c2d3e8cc0000000000000000100069d5555555554f44d40000000011c3d1c2d1c3d1c2c0000281c0c1c0c00002aaaa000000000000001555555555400008c000b00007070000303000070307030a00085c002aaa07aa04700000030300004f5b03334f33034faa81c0000000000000000100069d5555555554f44d400000000001c00000707200002a078000000000000100069d5555540014154015541070707070707070707030707070341aaaaaaaaa000b02c0b0b00b1f00701c88415555450555514500550555041c1c1c0c1c1c1c0c1c1c1c1c1c1d06aaaaaaaa8003c3c03c3c03c0f01c0722105415155555545000001c1c1c1c02aaa800000000015555540000001c1c1c1c02aaa800006c2c6c3c6c3c6c2c1c0c1c1c1c1c1c0eaaa800001f007c007001c08080400055555500000110 24 16777215 10 1023
def hc_87_11 : Nat → Nat := unpackHintV5 0xc939dac161f6b9f9dab241eeaad9daa4a18e9d49d697517e9189728bc17285a9867fc17a7b81107529966bb25e64b9be5dc1be56c9be5019ac4b91224549923bd25e34d9be2de1be26e9be20719e19c1ac1539220eb9a007e9b40420f2000108 0x82820b0f0f0b8282e0b85e17a00a0f0f0f0f030f070f070f030f170f000b03c0f03c0f202c2c2e082c3c3c2c5c5c5c5c5e85c3c3c3d0f130f40f0f2802a083c3c3e083c1c3c0c3c1c3c0c2c3c3c2e0a8283c82c3e0b1785e17000f82802c3c0f0f03c0f03c8820f130f43c3c3d0b0f0f0b2317171f17a1703c3c82820b0b0b0b8282e0b82e0ba00a0b0b0b0b030b070b070b030b0b0b000b02c1705c0b202c2c7e082c2c2c2c5c5c5c5c2e82c2c2c2d0b130b41b1b20a080c0c0c0e80280c2c0c0c0c3c0c0c0c0c0e0a0380e030380c0e80ca0001f07c030300c5ca003800c8821f231f0303030303030340c4c0d03a0307c7c8282030303038280e0380e03a00a030b0303030f0303030303030303001b06c0300c03200c0c7e086c7c7c6c0c0c0c0c0e80c0c0c0d03130341b1b02c0e9c0c0e081c0c0c0e0380e082c3c3c2c0c0c0c0c0c0c0c0c4c7c0c4c4c0c0c0c500c0f2200c0d40c4c4d030313130f0f828217175b8285e1785e17a00a130b130f130f130b1303130713071303059130004c1304c1304c8138281044d1344d1344c4d917131313113131320a085c5e0a1785e1785e80289c5c9c5c5c5c1c5c1c5c0001f07c1f05c229e82a821f1f17171f17a17171f47c5d07c7c00000000002c0c2c0c2c1c0c0c2c1c0c0c02aaaaaaaa80000000000000002c2c2c2c2c2c2d0b0f0b40cbc4c0ea8000000000000b0703030b0703030b030b0300aaaaaaaaa0000000000000000b0b0b42c3c2d0b0b0b0b032b1303aa0000000030303030f030000030b0303030f03030002aaaaaaaa80000000000000002c3c3c2c0c0c0c0c0c0c0d0313036a80000002c0c3c0c02aaa80000000000002c2c3c3c3c3c2c2c0c0c4c1c4c1c0c0e6a9400000002c2d0f42c0d1366a4000000000b030f0300aaaa000000229c000000000001c0800002c3c3c2c0c4c0ea8000408282030380e0aaaaa802a80c0eaa80c0eaa8228002c0b00c0328883c3c01c1c2082c2c2c2c0c0c0c0ea91c4c7d47131f40f0f2802a080c0c0e080c1c0c0c1c0c0c0c0c0e9e802aaa0781eaa07aa0ba82ea03a80e0aaaaaaaa8000070f0070700b02c0300ca0fa0229e081c4c1d07070742c2c2c2c0c0c0c0e3b9a9aa03c3ca0a820b030b0382aaaaaa00aa80c0c2c1c2c1c0c0e8228002c2c0b0f00c0f2202c3c02c2c2082c2c2c2c0c7cac0ea82c3c2d0b0b0b40f0f282a082c0c2c0e0aaaaaa802aa03030b070b070303a08a000b0b02c7c0306c880b0b00b1f0820b0b0b0b031f2f03aa0b0b0b42c4c2d06c6c82a0a0303030382aaaaaa00a030b0303030f0303aa8228002c1f00c0c031f2200c0c00c7c2082c7c8c2c0c0c0c0ea80c0c0d03130341f1f20a082c0cec0e80282c2c4c3c4c3c2c2c0c0c4c1c4c1c0c0e0aaaa81624002c1300c1304c4c04c4c2218182d1340d136a9a9113131320a082c0c0e802aaaaa07aa0aaaa80000b07c0307caa0229e082c7c2c0c7c0e9a9aa07c7c0000030303000001c1c0000c0c000020380e0380e80c0e80c0c000000000000002c2c2c2c0c0c0c0c4c4cad13132b40e80c0000000c0c0c0c0c2c0e9c00000c1c0c0c0c0c020380e0380e80c0e80c0c0000000000008a7000002c00b000c003000c030000c0000c00002c2c2c2c0c0c0c0c0c0c0d03130340e80c00045b0000000000002c2c2c2c2c1c2c0c2c1c2c0c020b0b82c2e82c2e82c2e0b82c0000000000000002c2c2c2c2c2c2d0b0f0b44c5c4cbc2e82c0000000000000f070f030f070f030b0f0f0b00a0f0fa0f1782c3e0b1785e170000000000000000f130f43c3c3d0b0f0f0b1317132313a170000000030303030000030b0303030f030300020380e030380c0e80c0e80c0c0000000000000004c3c3cdc0c0c0c0c0c0c0d03130340e80c0000002c0c3c0c02aaa800002c2c3c3c3c3c2c2c0c0c5c1c5c1c0c0c0000000029c808000b0f0f0b03171303aa13131744c4c5d000000170f0f5b0083e1785e17000000000000130b0f0f0f0f130b1303130713071303131359131700000001343d1344d1313645c00000000170f0f0083e1785e1700000000229c0000000001c00000130f0f13171313a17000100100655600005a55555a000195581c1c1c1c1c1c1c1c1c1c1c1c01955aaaaaaaa80000000a707c01f000000a70101555555555400100005a55555a006556000195581c1c1c1c1c1c1c1c1c1c1c1c01955aaaaaaaa80000001f01f0029c00000a701011344d555555555401541655641655607070707416556aaaa00605000701c88069c14055555514000007030700001d50354020b82e0380e1384c00000000000002c00030004c0000 24 16777215 10 1023
def hc_87_12 : Nat → Nat := unpackHintV5 0x83d13d3fb48d1e39684e9d1fe6e65a1352c8199d5304c5d2365f1cf32da47a95dd3d4a799d45024ea26ac59921151486628a3fd4d71d92960dba43c649a4e2e110f156a6789894b04491ee1e6cf70d507985c63882721c41104a30540d080fb6940001f6 0x1e000781c01c0c0c0c1c00c1c1c01c1c0c070303070303030070383c3c0e0f17030f030f03030303000f070070700f0f03c3c0301c0f00c070070f130f43c3c3d0f0f0f0f030707033303031f03c3c070070300303030303038000e030b030303030300303030303030303030380c0c0e0303000b02c0300c03031f0300c070070b0b0b0b0303030303030340c4c0d0303030306c6c828203030303a00a030b0303030f0303020a03a9e80c3e0380e80c0e80c0e802aa03030303030303030303030303030f0f03030b0b0303030303030f000b03c00ca70303003030703203c3c02c3c2082c3c3c2c0c0c0c0c0c0c0d030340e80c3c3c2d0b130f40f0f20a802a80c0c0c0c0e82030303030303003030320a0380e80c0e80c0e0380c002c0f05c1c01c1c00c0300c8820b0f0f0b1b131b46c4c6d0303030303a0306c6c828203030303a00a030b0303030f0303020a80c3e03a9e0380e80c0e80c0e802aa03030303030303030303030303030b0b0303170303030303030f000b03c00ca70303003030703202c5c05c6c2082c3c3c2c0c0c0c0c0c0c0d035b0340e80c2c4c5d17130b41b1b20a080c0c0c0e0a0380e030380c0e80280c0c0c3c0c0c0c2c0c03a800c0c0c007c1f00c0300c5c80c0307003030821f631f0303030303a0303130340c0c0d07c7c820b0f0f0b1403a9e0f80e0382a03030303130b0b0f0f0f130b0b0f0f0f030f0701c0f03c030303030f0b50b131343c3c1c01c1c00c1c0c1c0c1e000784c2c4c3c4c3c4c2c141d0300c01c0c0d6c0c0c0c0c0e13130384c5c004c1300c0704c1c01c1c04c031044d1340c0d0740c0c0c0c4d03444c4c4c070070700307030703078000e0303000c01c0c0c0c0c0c0c0e030380c007c1f00729c1c1c01c1c1c7c0301c01c7c7c0c1c1c0c0c7d1f0340c0c7c1f1f00000000000707070707070707070307070703000b0b0b0b0b82c2c2e0b0b070707070000000000000000b0b0b0b0b0b0b42c3c2d070707070b0b0b0b0000000000001c1c1c0c1c1c1c0c1c1c1c1c1c1c003e0f0f0f83c5c3c3c3c3c1c1c1c1c0000000000000003c4c3d0f0f0f43c3c3c3c1c1c1c1c4c9c4c5c0000001c0c1c0c0020f0f83c5e030781c0c00005c2c3c3c3c3c5c2e81c1c1c1c0e000000000000000004c3c3cbc0c1c1c0c4e85c4c4c5d13131740000001c1c1c1c009c3c3c5c1c1c1c1c0000000000004c2c3c3c3c3c4c2c1d07070707513131384e13170000000131343d2f0741c1c1d1344d0000000001c1c1c1c009c3c3c5c1c1c1c1c00000729c0000000000007002000004c3c3cbc1c1c1c1c4c9c4c5c0004007070070707007070707070707078001e070707070300701c0c1c01c3c3c3c3c1c1c1c1c3e0f170f83c3c003c3c0f0f01c0703c0c03c3c03c0f01c01c3c3c3c3c1c1c1c1c3c3c3d0f130f45c7ccc5c0f0f01c1c01c1c1c01c1c1c1c1c1c1c1e000781c1c1c1c0c01c0703070070b0b0b0b070707070b82c2c2e0b0b000b0b02c7c0701c0b0300b1f00b02c070070b0b0b0b070707070b0b0b42c4c2d0b0b0b0b06c6c828203030303a00a07070f0f07070707a08a82aaaaaaaa000b03c0303200c0c0c28222082c3c3c2c0c0c0c0cac4c7d2b131f6a80f0f2802a0a83e802a81c1eaaaa81c1c1c1c3c1c1c1c2e0a03aa80c0c0c0c0c082aaaa0fa9eaaaaa8020f0a00b03c0303030303000ca7888284e6a42c3c3c2c1dec1d07070740c0c0c0ea80f0f20a081c0c1c0e07081e1785e030781c0e80285c2c5c3c5c3c5c2e801c0381c1c1c007c1f00c0705c5c87c03030171f0822f1f631f0307070317a1717131745c4c5d07c7c07007078001e130b130f130f130b0700707070707050701d070072f177b171384c5c4e131307070707001304c13030131300701c1304c41c1071344d0707070741c1c1d1344d113131301c01c1e000781c1c1c1c1c1c1c01c1c1c1c1c0070072f17170781c1c1e0707070707001f07c07070707001ca71707c070072f1f1f070741c1c1d07070707171f1707c7c0000030303030080e20380c000280000c0c0c0c0c0c0c0c0c0c000000000000000002c3c3c2c0c0c0c0c0e80c4c4d0d13134340000000c0c0c0c0280c3e03a9e0380c0002a030303030303030303030f00000000ca7000000000002c00f000c00c0800b02c00170000000b0f0f0b0303030303a030b131744c4c2d000116c00000000000070303070303070703030707030300030b030b0382c2c0e0b0b030303030000000000000000b0b0b0b0b0b0b42c3c2d030707030b03030b00000000000001c1c0c0c1c1c0c0c1c0c0c1c0c0c000e0f0f0383c5c0c3c0c3c0c0c0c0c0000000000000003c4c3d0f0f0f43c3c3c3c0c1c1c0c4c0c0ccc0000000c0c0c0c00000c2c0c0c0c3c0c0c00003030303030303030380c0c0e03030000029c03000c0000130f0f1b0303030303030340c4c0d030303030000000303030300080e0380c0e030300000303030f0303030b030303a80c0c0000000000000000130f0f570303030303a0303130340c0c0d0000000703070300030f035b03030303000000000000130b0f0f0f0f130b030350740c0c4c4c0e0384c5c00000004d0f40c0d0740c4d034000000000703070300030f030303030300000001ca700000000000080000130f0f030707031303030001020a080c2c0e9c0c0c0c0e80280c1c0c0c0c0e0a0380e0380e80c0e80c0e80282c2c3c3c3c3c2c2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c5c5c0c0c5c9c0c0c0c0c0000b03c0300c03030030f0229e82a820b0f0f0b0303030303030340c4c0d03a0317171745c5d03c3c828203030303030b03a7a00a0307030303038280e0380e03a0303a0303a00a0b0b0b0b0b0b0b0b03030303030303030303030303031717030317270303030300002c0b00c0300c0c00c6c08a7a0aa082c2c2c2c0c0c0c0c0c0c0d03130340e80c5c5c5d175b1741b1b20a80282c2c2e082c2c2c2c2c1c2c0c2c1c2c0e0a0b0b82c2e82ca082e0b000b0b02c7ca00b806c1702c8820b0b0b0b0b0b0b42c4c2d2f17171f0ba0b06c6c 25 33554431 10 1023
def hc_87_13 : Nat → Nat := unpackHintV5 0x88891b41de999f5c64cf6612077050b39ca6e1bc9470d2a2ea6489322ef6d396a435cabe250527cdd272c8491f368c872a1c4060cd1dea918e4a2ac6bd99e30f93d167a808a4a3cc4a1a0e2144f20f385a86be37830d94610e5e205f89e81e24680003c4 0x7070703070707030707070720029eaaaa6385eaaaa070a43aaa0f83eaa0baa0f83ea07a81e800002c02c00a70000000207c0007d2d43d2d42d0f41d076669613500a00a8202802a0f85e0b08a820f4303030f0f03030b030b03a88e07aa0a83e0faaaa0baaaaa000b0b0b0b0b002ca7a083c00c0f20f28820f1f0f0f0f0f0f1f0b0b0b0ba984e40c7c7c0ea80f0f2802a080820f170f0f0f0f0f430b0f0f0b94c263a0f0f0f0f83e0f82c3e0f0b85e17a00aaaa00f02c2c5c8c5c1c5c1c5c8c3c3c3c002c2c2c2c2c00b29c3c0f03c3c83c0b0b00f0f0820f1f0f0f0f0f0f1f0b0f0f0b1f17171f17a1717131f47c4c5d03c3c0802882e00aa07030703000a17800303070703030000000000000990b42d0341d1745d0082820b0f0f0b821782c3e0f0b85e17a00aa00f02e17031707170717030f0f0f000b03c1705c171721f02c2c05c7c2082c3c3c2c5c5c5c5c5e85c5c4c5d17131741f1f20a082c0c2c0e0a82eaaaa00aa08a03031b071b070303a08a000b0b202c0c0f2202c2c282082c2c2c2c0c7cac0ea86c4c6d1b131b40f0f2802a0080a00a83e82e820f0703030f0703030b030b03a88e07a82aaaa82ea7aaaaa8002c2c2c2c2c00b02e820f00303c88820f330f43c3c3d0b0b0b0ba984e40c7cac0ea80f0f2802a080820f070f030f070f030b0b0b0b82a0b0ba0b0ba0b0b82ea782e0ba00a0b0f0b27a82c8c2c1c2c1c2c2c2c2c2c002c2c2c2c2c00b29c3c0f02c80b0b00b0f0820f330f43c3c3d0b0b0b0b2317171f0ba0b0b0b0b42c4c2d03c3ca00a8202081c1c0c0c1c1c0c0c1c0c1c0e802a2385eaa0f83eaa0ba82ea23a82aaaaaaa07a9eaaa000b0b0b0b0b002ca70301ca086c222087dec3d0f231f42c2c2c2c0c1c1c0ea6139aa07c7ca00a82028281c1c0c0c1c1c0c0c1c0c1c0e0a83c5e85c5e0b82e07a9e80c1e80280cac0c0c1c1c1c1c0c3c0c0c1c1c1c1c0c2c1c1c0c3c1c1ea032307000b0b0b0b0b002ca70301c17201c1c00c6c2087cec3d0f2b1f42c3c3c2c0c1c1c0c5e85c1c1c0d03130741f1f20a081c0c1c0e802a82280c0c1c1c1c1c0c0e0aaaaaaaa8002c2c80b0301c0b0b0a088820b0b0b0b030707032b131f4ac4c7daa07c7ca00a8202802aaa0f83eaa2baa0ba82e081c1c0c0c1c1c0c0c1c0c1c0e81e0aaaaaaaaaa81e000b0b0b0b0b002ca786c2800c07222087cec3d0f2b1f42c2c2c2e139a903070703aa07c7ca00a820282aaaaaaa088c8c0c0c3c8c0c0c2c0c2c0e88e9c002c2c2c2c2c00b29e200c1f2087cec3d0f231f42c2c2c2ea80c7c8c0c1f1f20a80280c0c03c0b03a0a0703070307070381c1ea07081e0b82e85c1e81c1e0380c002c0f02c2c07c2c00c0705c8820b0f0f0b23131f48c4c7d0307070317a1707c7ca00a82028281c1c0c0c1c1c0c0c1c0c1c0e07081e83c5e85c5e0b82e80c1e07a80288c8c8c0c3c0c0c3c3c8c3c0c8c0c0c2c2c0c3c3c3c0c2ea030707000b0b0b0b0b002ca70301c17200c6c07c6c2087c3d0f231f42c3c3c2c0c1c1c0c5e85c0c4c7d23130341f1f03c03c2c02c0a70b00b00029cac08c3c3c3c3c2c2c2c2c2c2c2c2c2c02c2c2c2c2c2c2c2c2c2c2c2c2c2c2c2c2c7c07c3c3c3c3c2c2c2c2c2c2c2c2c7c7c7c7c2c2c2c2e084681c0c1c0c1c1e1784e07078ee084c4c4c4c0c0c4c7c7c4c0c0c2c3c3c2e81c1c2c0b04c13283c3c3c3c4c7d44c4c4d1313138004e0f033050f04d3b04b1307130313071303330f0f334b04b1384c5c4e1313330f0f337b3b3b00130b0131300f03c1304c1304c44c11f0f0f0f1343c3c3d1344d1344d113131303e0083c000070f0f070f0f083c3e0f0f000f0f00a71f07c1f07c01f1f0f43c7d330f0f1f1f1f1f1f07c7c0000070307030082e0b80e000002c2c0c0c2c0c2c2e80001c1c000000000000000002c2c2c2c0c1c1c0c2e82c4c4d1d131347400000001c0c1c0c0020b82e80c1e0782c00002c2c0c2c2c2c0c2ea030707000002ca700000000000002c00c03001c07002c17022000c030011c0000002c2c2c2c0c1c1c0c2e82c0c4d7d13130340004000029ca7000003c3c3c3c2c2c2e9c2c3c2e9c002c2c2c2c2c2c2e9c2c2c2e9c2c2c2c2c000f21c0b00000003c3c3c3c2e9c2c3c2e9c2c2c4c7c4c7c2c2c2c2c000000000000b0b0b0b0b070b030b070b03000b0b0b0b0b82c2c2e0b0b0b0b0b0b00029c0b002c0000000b0b0b0b0b0b0b42c3c2d131f131f0b0b0b0b0000000030b030303030000030b03030307030300000c0c0c0c0c0c0c0c0c0c0e03030380c0c0000000000000002c3c3c2c0c0c0c0c4c0c0c0c0d03130340c0c0c0c0000002c2c2c2c0020b0b82c2e0b0b82c5c00002c2c2ea0b0b0b030b070b070b03000000000000000002c2c2c2c4c5c4c5c2c4e82c2c2c4c2d0b0b0b40002070782c002c2c2c2e81c1c00002d42c0c1c1c0c2e82c0c4c0d1c4cfc4c4c4c0c4c0c0002c2c4d7d44c4c4d0000000b0f0f0b000b0b0b0b0b2f0b0000000000000b0b50f42c2c4c0c4c1c4c1c4c0c4c4c2e0b84c5c00000002c2d0f42c4d1344d0b4000000000b0f0f0b000b0b0b0b0b2f0b00000a70000000000007000800000b0f0f0b132f13130b0b0001001c01c1e000780c0c0c0c00c0c0c0c0c0c0c0c0c0c03030030700030303030303030f03030303030f030f000c00c0c0c0c0c0e03030380c0c0c0c0c0c0c0c0c0c0c0c0c0c002c6c0f1b01c1c06c1c00329c0c0c00c0c1c0c0301c01c2c3c3c2c2c4c6d1b130b40c0c0c0c0c0c0c7c0c7c0c0c0c0c0c0c1b1b01c01c1e000780c0c0c1c00c1c0c0c1c0c0c1c1c0c0707003007030b030b0382c2c0e0b0b03030303000b0b02c7c070700b0700301c0b00c070070b0b0b0b0b0b0b42c4c2d030707030b03030b06c6c070070300303030303038000e030f030303030300303030303030303030380c0c0e0303000f03c0300c03030f0300c070070f0f0f0f0303030303030340c4c0d0303030303c3c078001e07007030303030030303003030300c0c0c0c0c0c0c1c000c0c0c3c0c2c0c3c0c0c0c0c0c0c0c0c0030030380c0c0e030303030303030303030303030303030303000f070070700f0f03c3c00ca7030300303070300c070070f130f43c3c3d0f0f0f0f030303030303031f031f03030303030303c3c 25 33554431 10 1023
def hc_87_14 : Nat → Nat := unpackHintV5 0x800cf33d9c9a9d974dce3da386d253234f467994e4b0c2d9e65d98f52d0c7015c1314a699dc50d09f26967492693888eb126433d072078498fa126c744a30327dea156af50a461bc482a821ef5480c04dd84ba520180b720964a8029e8500a72a000014e 0xf00b0f8002e00bc02c3c3c2c2c1c3c3c1c2c2c02c2c2c2c2e0b0b82c2cbc2c008729c3c03c7c1f07c0b007c2c3c3c2c2c3d0f0b47cbc7c2c2c7c1f1f00000001c2c1c001c2c1e9c1c1c1c1c1c1c1c002c2c2c2c1e070b0781c1c1c1c1c1c000b29c000000000000000b007003001c00b02000002c2c2c2c1c1c1d07130741c1c1c1c2c2c2c2c00041b0000000707030b070b070f0000070707030f0b00030b030b030303030380c2c0e030b0002ca70000000000000002c00c007002c02c0800000b0b0b0b03070703030b0b42c4c0d0b03030b000106c0000002c2c2c2c0282c2e0b83e0b82c0002a0b230b070b070b0b0b0b0b0002ca70000000000000002c00c007002c0800b00000b0b0b0b131713230ba0b0b0b0b42c4c2d000106c0000001c0c1c0c020b82e07a9e80c1c00000c2c1c1c0c3c1c1ea0323070002ca7000000000000000ac00c007005c0800701c000300c000000b0f0f0b0307070313a1707070340c4c1d00010ec000001c0c1c0c020b82e03800000b030f0f0f0f0303a0000707000000000000000000b0f0f0b0307070313a1713131b44c4c6d00000000703070300082e0ba030781e2700000b0b030f0f0f030ba80c1c1c000b29c0000000000000023003001c01702000c030008c0000002c3c3c2c0c1c1c0c4e85c0c4c8d13130340004000000000003c1c3c0c3c1c3c0c2c3c3c2c002e0f0f0b83c5c2c2c2c2c2cac2c8c000b00b0029c0000003c4c3d0f0f0f42c3c3c2c4c7c4c7c4c2c2c7c0000000c0c0c0c3c0c00000c1c0c0c0c3c0c0c00003030303030303030380c0c0e0303000000000000000130f0f1b0303030303030340c4c0d030303030000000b0f0f0b0082c3e0f0b85e170000a0f0f0f0f0b85c0c5c1c5c1c5c0c00000000000000000b0f0f0b1317131713a1713131744c4c5d000081c1e27000b0f0f0ba0707000043c3d0307070313a170313032313331313130313030000f0f0303131703131344c0d40000006c3c3c6c006c3c3c6c9cec9c0000000000004d0f0f0f0f5130313071307130313131384e131700000001343c3c3d131344d33131344d330000000003c3c009c3c3c9c9c008729c00000000000001c002000004c3c3ccc4ccc4ccc4c9c4ccc000400a00020000200000000070707070707070707070707a81e07a00aaaaaaaaaaaa00003c03c00a700000000000f1f50f0f50f43da584d41d07664000000800a70020000001c1c1c1c1c1c1c1c1c1c1c1ea0781e802aaaaaaaaaaa8000b00b00000000000000f3350f0f50b42da584d41d07664000000028000001c1c1c007030000aaaaaaaa000000000000002b43d2b1352b1350741d9900080002aa8ae83c3ea802a0b83e80029c0800707070707030707072b030707070700aaaaaaaaaaaaa0000000ac0ac00a7000000a584d47ced43cad4ad0f41d0766400000002800000030703000707000aaaaaaaa000000000000002343d23135231350341d9900000000b1b0b0000c0c1c0c0c01c00aaaaaaa0002c02c0029c0000006d0d0f1b42d0b40d0766400000000020029c1c1c1c1c0c0c1c1c0c8c0c0c1c0c1c0c288eaa83e0faa82ea83e0fa0002aaaaaaaaaaaa800230230029c0000081f000001f4b50f2352343d0341da584d664001c1c001c1c1c01c0078001e070f0703070b00701c1c1c1c01c1c1c3c1c3c1c1c1c1c1c1c1c1c3c1c1c1c1c1c1c1c01c3d0c3c3c3c3c3c5c3c3c3c3c1e07230781c1c1c1c1c1c003c3c3c3c3c00f29c1c1c01c3c01c3c070703c0f01c01c3c7c3c3c3c3c3c7c3c3c3c3c1c1c1d07130741c1c1c1c5c7c7c5c0f0f01c1c001c1c1c01c0072b003230707030f0303070f070f07030f070f03078000e07070707070700f00c2c0c3c3c0c01c0c0c3c3c0c0c3d0c0c3c0c3c0c0c0c0c0e032b0380c8c003c3c3c3c3c00f29c0c3c070f00c2c03c3c03c0301c01c3c7c3c3c3c3c3c7c3c3c3c3c0c1c1c0c0c4c7d1f130347c0c0c7c0f0f0200a20f800280c0c000aaaaaaa0000000000000992b43d0340d9900070070300303030303030f03038000e030700300c0c0c0c0c0c00c0c0c0c0c0c0c0c0c0e03030380c0c003c0f00c0c031f00c0c00c7c00c0301c01cbc3c3c7c0c0c0c0c0c0c0d03130340c0c0c0c1f1f01c01c1c01c1c1c2c1c1c1c1e000781c0c01c0703070300701c0c1c01c2c2c2c2c1c1c1c1c2e0b0b0b82c2c002c2c0702c1c0702c0c01c0c02c0b01c01c2c2c2c2c1c1c1c1c6c4c6d1b131b42c2c2c2c0f0f01e000781c001c0078001e070f07070b07070070707070307070703070b07a707070707070707070070b82c2c2e0b0b0b0b0b0b0781c2c1e070707070707000b0b0b0b0b002c0b07070070f00701c0b02c070070f330f43c3c3d0b0b0b0b07070741c4c1d070707070b0b0b0b03c3c07007078001e030300b01c0c1c00c1c0c2c1c2c0c1c1c0c0707003007030b030b0382c2c0e0b0b03030303000b0b02c0b070700b0700301c0b00c070070b0b0b0b1b131b46c4c6d030707030b03030b03c3c078001e07007001c00c1c1c0c0c1c1c0c0c1c1c0c2c1c2c1e9c1e000382c3c2c1c1c1c0c3c2c0c01c0e0b0b0382c2c0c2c0c2c0c0c0c0c0e030b0380c2c002c2c2c2c2c00b29c0c0700c2c02c3c02c0301c01c3ccc3d0f0f0f42c2c2c2c0c1c1c0c0c2c2d0b130342c0c0c2c0f0f00000028000001c0c1c0c1c1c0c0c1c1c0c0c02a02802a8000000000000002d0b50c4d50c4d40d076640020000aaa43a0f0faa00a82e0ba0002a0781e81c1c0c0c1c1c0c0c1c0c1c0c0a70202aaaa53aaaaa0700000002c02c00a7000000a584d47d2d43d2d42d0b40d07664000000028000001c1c1c1c1c1c1c0c1c1c1c0c00a80282a8000000000000002d0f50c4d50c4d41d0766400000002c6c2c001c1c1c1c1c1c1c1c1c1c00aa822a8000b00b000a70000001b4343c6d0b42d0741d9900 25 33554431 10 1023
def hc_87_15 : Nat → Nat := unpackHintV5 0xbef958bb48ecb5c162aff972aa3172a1d2189cc9429801328f423089a9668209e87d911e7911207129fa6ca920649a046128dc5ba16256196253d8904db18a47a18444b0bc40810c383a122e527a25c2241d8a0e1c00620ecb4e08d97c000236 0x1c3c1c5c002aaaa170000170b0f0f0f0f170b17030707070717030000000000000000155555555540000001c3c1c020fa0780a70000000000000001c002000015555540100440000000000007070f0307070f03070f0f070f00a0f17a0f0f83c3e0f81e230000000000000005555555555500000000000001c2cbc1c2c2c1c1c2c0c1c1c2c0c020b0b82c2e82c2e82c2e0782c0000000000000015555555555400000000c1c0c0c0c0c00000c2c0c0c0c3c0c0c00080e0380c0e0303a0303a030300000000000000055555555555000003c3c0002cbc00070000c001c1c1e9c1c1c0c3c03cbc000000c0c00001c1c1c0c1c3c800170083e0f80e03a034fa030f00000a7000000000010010055555555550040000070707a701c1c0c3c0003c3c6c0c1c3c020f83e0380e032b80c6c0000000000001555555554000000000001c1c000000c0c1c0c1c00a1b17a1b1782e0b80e03000000000000005555555555000003c0002c2c0001c1c0000c0c001c1c0c3c1c1c1e9c06c000000c0c00001c1c1c0c1c3c800170082e0b80e03a034fa031b00000a7000000006c1f0001001005555555555004000007170717000aa85eaa170000170b170f170f170b1703070707071703000000000000000015555555555400000f0f0000b0b0001c000300070f070b200200aa9ea0faa00b0b000000f0f0000a82dcc1c1c1c1c3c3e83c000029c0000000000400401555555555401000001c3c1c3c02aa72a0faa0000f0f1b172307070b1ba0f000000000000055555555500000000000a0007071b0307071b03070f070b00000aa8aa000000000000005555555555000003c0002c2c00070000c001c3c1c2c280021700a83eaa7aa01b000000b0b0000a85dcc1c1c1c1c2c6e83c000029c0000000001b07c040040155555555540100000011c3d1c2d1c3d1c2c0000281c0c1c0c00002aaaa000000000000001555555555400008c000b00007070000303000070307030a00085c002aaa07aa04700000030300004f1b030f4f0f031baa81c000029c0000000004f07c0400401555555555401000000001c00000707200002a078000029c0000004004015555540100000000000070707070707070707030707070300aaaaaaaaa0000000000000000b42d0b0b50b0f50741d9900000000000001c1c1c0c1c1c1c0c1c1c1c1c1c1c02aaaaaaaa80000000000000003c4d43c3d43d0f41d076640000001c1c1c1c02aaa800000000015555540000001c1c1c1c02aaa800000000000004c2c3c3c3c3c4c2c1c0c1c1c1c1c1c0eaaa80000000113543d507541d595940000000000707070700aaaa000000000000b130f0f0f0f0f0f07070707aa0000000b0f130707070707070707aaaa00000f0f0f00000707070700aaaa00000000000130f0f07070707aa0000000707070700aaaa00029c000000000001c0070202000004d0f41d0766400010000000000800a70703070307070303070703030a0b82ea0f83ea0b82eaa0f83ea8000aaaaaaaaaaaaa00029c23008c00000000000b43d0b2f50f4b50341da584d664001c01c0c00c0c2c0c0c0c0c0e000380c0303030700303030300303030303030303030380c0c0e0303000b03c030300c3c03030030f00300c070070b0f0f0b0303030303030340c4c0d0303030303c3c00000000001c1c1c1c1c1c1c0c1c1c1c0c800a7aaaaaaaa81c282e0ba82e0fa82e0baa82e0faa81ea07a00000a702c00b000000000002d0b42c2d42d2d41d07666961350082820b0b0b0b8282c2e0b0b82e0ba00a0b02ea00b030b070b070b030b0b0b000b02c0f03c0b0f20b02c3c02c2c2082c2c2c2c5c5c5c5c2e82c2c3c2d0b0b0b40f0f02c2c3c3c2c2c0d1c0da7030382a00a028281c0c1c0c1c1c0c0c1c1c0c0e07081e0b82e82c2e82c2e80c1e0782e80282c2c0c2c2c2c0c2c2c2c2c2c0c2c0c0c2c2d1c3c0c2c0c0ea0307070002ca70b0b00b0b230301c0b200c6c07c6c2082c2c2c2c2c2c2d0b0b40c1c1c0c2e82c0c4c7d130341f1f2085281c0c1c0c1c1e0b82e070782e082c2c2c2c3c7c7c3c0c0c3c3c3c3c0c0e81c1c3c0f03c0f02c2c2c2c4d1343c3c3c02c3e000f8143d0b0bc12c2c3c3c2c3c1c3c0c3c1c3c0c2c12c2c2c2c2c2e0f0f0b83c5c2cbc2c002c0f03c3c03c3c03c0f03c0b1042c2d0f42c2c2c2c4d1344d0b443c3c3c 24 16777215 10 1023
def hc_87_16 : Nat → Nat := unpackHintV5 0xd831f4d199a6cb01a6bbe3c8b8d8c2aed282a60234a0496e96b2668f99c682f32a7a9a167559506fa16e662a5e5f11c6526b2a4a121644896240c0f23ca10837d9322fba082bf8f02779202019d81c58f017d9200fe9fc0ab14e05794e00015e 0xa88aaaa030303aaaaaaaaaaaaa030b03030b030303030303a03a7aa0f530f03c8c3c0b0b0b0baa03030303aa233b0f43c8c8d0b0b0b0baa030303030f330f820300ca03030303030780e0380c0e53820b030b003c0c2c0c0c0c2c0c3c0e80c0e83c3c3c3c0c0c0f030f1b04d0f40c7c7c0c3c7e080d03680c0c0c0c0c1e0380e03038ee582c0c2d513030b0303030b030f03a03031304c030f1303a0f0f0f0f03034cc0c4c4d1313a2303ca82d3c3c8e030303a0303a0303a03030380c0c0c0c0c0e03a81e80c0e80c0e030380c0e80c0e03a80c0c0d1e80c2c0c2c0c2c0c0c0c0c0c0c0c0ea03030383d3e0f0f03c8c3c0b0f0f0b0303030303a030303030f034703038cd3e230f43c8c8d0b0f0f0b0303030303a0303030333034703030f330f000000f0001ea0030002a8202a0000000000001540155540283c0f2a0b0f0f80c0c0e030781c1e81c1c0e070303070303aaa0707a0f0782c3e0b1780e0383c3e0f0f0f03c3c3c0b0f0f0b030707030fa0f8ccce0f130f43c3c3d0b0f0f0b0307070317a170f0f0f0f82c2e80c0e03030303aa80e0380e03a0300ca030b0303030303030390c6e0b0b0b0b0303030303a0303030300c7c0c8dd3e0b0b0b0b0303030303a0303030340c4c0d431b1b370080c0e270043030f03a0303000000b0f0f0b0303030303a0303030303133f031313540004cdc0c0d3f031313400000000c0c0c0c0020380e80c0e0389c00000d0c0c0c0c3c0c0ea0303030000000c00030000c03000000002c02302000c00302000c1f00004c3c3cdc0c0c0c0c0e80c0c0c0cfc0c4c0c0c0004082a0aaaa00a0b0b23231f230b0ba0aa80203030303a03a7002202c1f28880c0c0c0c0c00300e082c7c8c2ea87cec7d1f3b1f40c0c0c0c1f1f20a8280c0c0c0e03081e0380e80c0e03a80287c2c8c8c7c8d1c2e800c0c0e03030a0303a00a031b030303470303a80c0c0c0013c4f07c1f00c0c0300c0c0c80303030303030303000c03821f231f0303030303a031f5f1f47d1c7d0303031f0347030307c7c8282070307038285e1780e03a00a1b0b1b0f1b0f1b0ba00700e0707081707007c1b06c030301c031717205c0c0c0e086c7c7c6c0c1c1c0c5e85c7c4c6d1b131f41b1b155556a9540c0c0c0e80e9d542c8c7c2ea80c0c0c0d555559550369d555551150b548d59595035155345556030394d046c0ccc0e80c0d042c3c3c2c0c0c0c0c0e80c0c0c0c0c7cfc0c4c4c051f5f03030fc0c6c6c5055115555550303030355580e03a030380e55550347030303330303a80c0c0d547c8c7d7c0c0c0c0c0e80c0c0c0cfc0c7c0c0d55555035540d550340d5555551150b548d59503540d5950344d154565a96aaa91282c2c8c8c4c8c2c2e96aa5580c0c0c0e80e9d5960b13230baa13371304cec4c030303035990b44da660303030303540d031344d96a5a0303030380d60780e03a030380ea44a130b23231323370ba503030380c0d680c0e95680d1c0c0c0d1c0c0ea03030355961323130303030303a0313371304d1c4c030303130347030353753d1344d030340d030303640c0c0c0c0c0c0c0d50340c4d1365a581c0c1c0e5a1785e0380e91284c2c4c3c4c3c4c2e941d0381c1d644c1e584c4c4c4c0c1c1c0c4e84c4c4c4c131313151344d1340c0d0740c4c4d9170303031344daa0307a0703070381ea0785e17a030781ea030a0303a80c1c1e80c1c1c0c5e85c0c03280c1c1c0c5e85c0d034000200200200207070707002002aaaa029c00000000000200150741d9900000007030700001c00300020b82e0380e1b87c002c00030007c0000555555555000000070307000001c1c0000c0c000020b82e0380e8ac5e8ac5c0000000000000155555555540000001c1c0c3c1c1c1e9c00001c1c1c0c1c3c020b82e0380e80d3e80d0c0a700000000010c000000b003c003001c00300c002b0001702000015555555554010044000001c3c1c2c02a2a8002006c1c1c7e00002c00008001f0015555555540000001c3c1c2c02a2a8000280010c0c1c1c1c1d0c0e80000000000000000155555555540000001c3c1c2c02a0faa9ea80002a175f070707070b43a0f029c000000000004300002c00f000c0070202002c0b0010c0000015555555554010044000001c0c1c0c02aaa00006c3c3c6e020000000c008001f0015555555540000001c0c1c0c02aaa000011c2c3c3c3c3d1c2e8002800000000000000001555555555400000001c0c1c0c002aaa07aa00004f43030f0f0f0343aa81c0a70000000000013c0000b008c00300c00701c0817022000c030011c000001555555555401004400000000000070b070b07070b0307070b030082e0ba0b0ba0b0b81e0b000000000000000555555555500000000000001c1c3c0c1c1c3c0c1c3c1c3c0283c3e83c5e0f83e0788c000000000000001555555555400000000c0c0c0c00000c2c0c0c0c3c0c0c00080e0380c0e0303a0303a0303000000000000000555555555500 24 16777215 10 1023
def hc_87_17 : Nat → Nat := unpackHintV5 0xea9a16e10266d46b26cc1216c6b956bf11eab769eab069c0a969c0a4813a9a9a7a90b27a8931e080fa0e78c20e70d9fa6931ea6189ea5a49d05309d04e31364a58f64279f83ea0f636c1f82f79d22c58c82561be15e3e012d8c208d282000234 0x82820b0f0f0b8282e0b85e17a00aa00f02e1b03170717071f030f0f081717007c0b0b03c0b1b05c1717205c2c2c2e082c3c3c2c7c5c5c7c5e85c7c4c6d1b131f41b1b155542c2c2c2d5682c2e0ba9e0b82d5556a0b170b0b0b170b0b0b0b0b550b0b0b0b171717170ba0b0b0b0b3f0b1f0b0b55542d55550b5542d0b5555554456542d503541d50b56542d134546d1596960b0b0b0b96a0b0b82ea782e0ba44aa50b0b0b84c0c5c1c4c1c5c0c2c2d682c2e956aa0b170b0b0b170b0b0b0b0b55960b0b0b0b171317130ba0b131b1304c6c4c0b0b0b130b9f0b0b54f53d0b0b42d0b1344d0b0b642c2c2c2c2c2c2c2d50b42c4d1365a582cbc5c2e5a0b82e1785e912a944d0b84c0c4c1c4c1c4c0c4c3d644c5e582c4c4c2c4c4c4c4c4e84c4c4c4c131313151342c2d1342c4d1344c4d9170b0b0b1344d82e85e0b2f170baaa0baa785e17a0b0aa85c2c1c5c1c2c2e82c2c5c5c5e85c2c0b282c2c5c5c5e85c2d0b6aaa22aaaa0703030703030707030307070303aaaaaaaaaaaaa0b0b0b0b0b0b0b02c7c2c03070703aaaa0b0b0b0b0b0b0b42c4c2d03070703aa271b1b27a88aaaaaa81c1c0c0c1c1c0c0c1c0c0c1c0c0eaaaaaaaaaaaa82c2c2c0b0f0b02c2c2c2c0c1c1c0eaaa82c2c2d0b0f0b42c2c2c2c0c1c1c0ea83c3c3c3e0a081c0c1c0e80282c2c5c3c5c3c2c2c0c0c01c030382aaaaa8a0000b06c030301c03aa2a2082c7c7c2c0c1c1c0c5c4c5d1713176a81b1b25a581c0c1c0e91282c2c4c3c4c3c2c2c0c0d41d030396aaaaa9a5960b13130b0307070313131304c4c4caa550b44d030341d03aa6a44d136aaa81c0c1c0ea22aaaaaaaaaa07a9eaaaaa0b270b03070703a8a2aaa82c2c0c1c1c0ea69aa272781c1ea0300ca03070380c0e030303030303a03030380c0eaa030380c0e80c0e80c0e0380e070782c2c2c2c0c0c0c031f0300c0c0c0c0e80e070782c2c2c2c0c0c0d03130340c0c0c0c0e80d0c6c6d0e80c032a070780c0c1e030380e0303a0303030303030303aaa0303a030380c0e030380e0381c1e030f0300c0c0c0b0f0f0b0303030303a0381c1e03130340c0c0d0b0f0f0b0303030303a030f0f0f0faaaaa03030303aaaaaa80eaaa2280c2c0c0c0c3c0c0eaa03aa0b23230b03030303aa03030300c7c0caa0b23230b03030303aa03030340c4c0d2737278282030303038280e0380e03a00a0303030f0303030b0300ea00303080303001b06c0300c0c0c0303200c0c0c1e086c7c7c6c0c0c0c0c0e80c0c4c0d03030341b1b25a580c0c0c0e5a0380e0380e91280c0c0c3c0c0c0c2c0d03a940c0d640c0e584c4c4c4c0c0c0c0c0e80c0c4c0c0303031544d1340d03030340c0d9030303071344d81c1ea0307a07030703aa85e1781ea7a0307a0700ca030707030707a80c1e07078bcbc0c1c1c0c5e85c1c1c0c0307207078bcbc0c1c1c0c5e85c1c1c0d03076aaa81c1c0c1c1c0ea22aa0303070707070303aaaaaaaaaaaaa0b0b0b0b030707030b0f0b02c2c2caaaa0b0b0b0b030707030b0f0b42c2c2daa0f0f0f0faaaa070703070703a88aa80c0c1c1c1c1c0c0eaaaaaaaaaaaa82c2c2c2c0c1c1c0c2c2c2c0b1f0b2aaa82c2c2c2c0c1c1c0c2c2c2d0b130b6a89c6c6c9e0a80282c2c6c3c6c3c2c2e081c0c1c0c1c1c01c1c0c82aaa0a8aa000b0b06c0ba80c07070722a2082c7c7c2c6c4c7d1f131b40c1c1c0ea81b1b25a91282c2c4c3c4c3c2c2e581c0c1c0c1c1d41c1c0d96aaa5a9aa960b13130b13131304c4c4c03070703aa550b0b44d0ba80d07070766a44d136aaa22aaaaa81c0c1c0e81eaaaaaaa81eaa0b270ba2a00c1c1c0eaaa82c2e9a903070703aa2727000000a0303aa00070380c280002a82802a0000000000000015555555554002a70000800007030703000303007070000aa0085c282a07aa00000b0b0b0b030b0b0b4f030b000030304700aa81c0000000000000000015404415555555400000280c0ea800002802030703000a00aaa800000000000055550055555500002000a9c01c1c0000c0c0001c0c1c0c2800217000aaa81ea808c000000c0c00002c2c8c0c3c3c3c8c3c0c2eaa070000000000000000100100555555555500aaaaa03030303a9ea7a9ea703a703a703a703a7aaa82c8c8c2c0c0c0c0c0e9c0e9c0e9c0e9ea82c8c8c2c0c0c0c0c0e9c0e9c0e9c0e9c9cde5c9eaaaaaaaa82c0c0ea9ea82c9c2ea80c9c0ea82c2ea80c0c9c9c008c000b000a000a000280c0c0c0c2800207000207aaa80ea828000280d1c0c0c0d1c0c0eaa03000000000000000010010055555555550082c2c2c8ea0b02ca030303a0303a03030303030303030380c0ea03a81e030380c0e80c0e80c0e80c0e0382e80c0c0d1e80c0c0c0c0c2c0c0c0c0c0c2c0c3ea03030393d3e0b0b0b0b0b0b0b02c8c2c0303030303a0303030343031b03038dd3e0b0b0b0b0b0b0b42c8c2d0303030303a0303030347034703035f37370002c000000300a07800802aaa000000000000001555554020b0b0ba82c0b280c0c0e030781c0c0c1c0c0c1c1c0e0707aaa82c2e0b0ba0b07a070780e0390c6e0b0b0b0b0b0b0b02c7c2c030707030ba0ba6d6e0b0b0b0b0b0b0b42c4c2d030707030ba0b431b1b4382c3e80c0e03030303aa80e0380e03a0300ca030f0303030303030383c3e0b0f0f0b0303030303a0303030300c3c0c8ccce0b0f0f0b0303030303a0303030340c4c0d0f0f0f0f 24 16777215 10 1023
def hc_87_18 : Nat → Nat := unpackHintV5 0xdca95ad81924d5e88cd230eecba1a4c4d1b4be619cb7f19cb3d906abc206a4c1c09dc1c098c93e91b9c487f2728059e678220e6fea0e6851e660b9e65929e45199e44c814646498e3eb9e436b20230419c263a821ea1e616321c0c9a66000326 0x3070303030703030000030b0303030f030300002aaaaaaaaa80000000000000001555555555554000000000c0c0c000c2c0c0c2c0c0c0c0c0c0c002aaaaaaa80000000000000155555555540000002c0c0c002aaa8000000000155555400000000007000000703070308002a7aaaa00000000000010010055555500a0aa00aaa081c1c1c1c1c1c1c1c1c0c1c1c1c0e0aaaaa282a8002c2c0b02c2c02c7c01c07221042c2d0b42c2d42c4d41d0766446ca00aa0aaa081c1c1c0c1c1c1c0c1c1c1c1c1c1e0a82a2aaaa8003c3c03c3c02c3c0f0f01c07221043c4d43c3d42ccd0f0f41d0766443c00000707070700aaaa00001b0b1b0f1b0f1b0b07030707070707030000000001f0001c20020006d1f41d076647c4d46c4d4007c41410707070741aaaa5005130b130f130f130b07030707070707030554001304c0701c88131301313050555135541d65564544c828207070707a00a9eaaaa07aaaaa07a81e800000701c88a0810541d0766696512aaaa80c2c0c0c0c0ea2280c2c0c0c0c1c0c0eaaaaaaaaaaaaaa0b23230b030303032f0303030300c7c0caaaa0b23230b030303032f0303030340c4c0daa27372782a00a0b0b00f02c2e082c0c3c0c7c1c0c0c6c1c0c0e0aaaa282a8002c2c0f02ea0306c8a8820b0f0f0b1f131b46c4c7d031f1f03aa06c6c96a44a0b0b51342c2e582c0cbc0c4c1c0c0c4c1c0c0e5aaaa696aa582c4c4c2c4c4c4c13131300c4c4c0ea9542c2d1342ea0344d9a91344daaa88aaaa0b032f03aa07aaaa3ea7aaaaaaa82c9c2ea2803272f03aaaa0b0ba9a40cbcbc0ea89c9c002a700030303030007001c0800aa9ea17aa02200000a80c0c0c0c0c0c0c0c0001c1c01c1c0285c00000000000000000155540441555554020b0ba030380c0c0c0c2c0e80c03280c1e80e0303030303aa80e0380c0e0303a0303a030383dce0b0b0b0b0303030303030300c5c0c03a038cdce0b0b0b0b0303030303030340c4c0d03a030f330faaaa0b030b03aaa82eaa7aaa88aa80c0c2c1c2c1c0c0e82ea82c2c2c2c0c3c5c0ea82c2c2c0b1f0b2a82c2c2c2c0c5c5c0ea82c2c2d0b130b43c6c6c3e0a082c2c2c2e0a0b82e0b82e80282c0ba802c0c2c1c2c1c2c0c2c2c202c2c002c0b0b0b03c0f02c2c80b0b0b0f820b0b0b0b1f17171f0ba0b0b0f0b42c2c2d03c3c96960b0b0b0b9682e0b82e0ba44a0b42ea50b030b070b070b030b0b590b0b960b0b0b0b130f130f0ba0b0b130b02c2c2c550b42c2c2d1344d0b0b642c2c2c3c3d1360b0fa1782c3c3c2eaa8fa9e82e1785e83c0b2aa0b0f070b070f0b83e0b0f0f0b0f170f17a0f0f0b02c3c8ce0b0f0f0b17173317a170f0b42c3d0f330faaaaa030303030f03a88a03070303030f0303aaaaaaaaaaaaaa82c3c3c2c0c0c0c0c0c0c0c031f032aaa82c3c3c2c0c0c0c0c0c0c0d0313036a83ccc3e802a083c3c03c3c2c820f0703030f0703030b030f0382a0a8aaaa202a82c0f0f0f00c0c0f00e2a2083c4c3d0f0f0f42c3c3c2c0c7c7c0ea80f0f0f1f2912a583c3d43c3c2d9613070303130703030b030f0396a5a9aaaa9613130f04c4c3c0b0f0f0b030f1303aa656a82d0f0f0f40c0d1340e6a43d1313136a22aaaaaa07aa82c0c3c0eaaaaaaa7aaaaa2a02c3c3c2c0c3c0eaaaa9a90b0f0f0b033303aa0f330f002000a9c070000c001c2c1c2c800802a0baaaa0a0000a82c8c1c1c1c1c2c2e82c0000000000000000400401555555555400002a700030303030007001c0800a85eaa7aa02200000a80c0c0c0c0c0c0c0c1c1c0c0c0001c1c01c1c0285c0000000000000000015554044155555402aaa7aaa9e82eaaa82c2c0e9c2c3c0e9eaa82e3ea030b0b03aaaa0ba70b0f0ba70b0b030f0f030b0b0b0baaaa0ba70b0f0ba70b0b031717030b0b0b0b0f0f0f0f008008008070000c001c2c1c2c800800aa0baa9ea8280002aa0b17070707070b0ba0b000000000000000010010055555555550082c8e80c0c0c5e030b03030303a0300ca0380c0c0c1e80c0c0eaa0380e030380c0e80c0e80c0e5f7382c8c8c2c0c0c0c0c0c0c0c03170300e80e377382c8c8c2c0c0c0c0c0c0c0d03130340e80d7cdcdeaaa82c0c2c0eaaaa7a82eaaa22aa03030b070b070303a0baa0b0b0b0b030f0f03aa0b0f0b02c2c2caa0b0b0b0b03171703aa0b0f0b42c2c2d0f0f0f0f82c2e85c5e0b0b0b0b82c2eaa9c2c2c2c2e0b0baaa70b0b0b0ba883c3e0b0b0b0b0f0f0f0f0b0b0b0b0b0b0b0b8ccce0b0b0b0b171717170b0b0b0b0b0b0b0b0f0f0f0f00000b0b0b0b00a0b0b82ea782e0b0000a82c5c2c2c2c5c2c2c2c2c2c0000b000002c000b02c0000000800b000c007002c0800b07c0000b0b0b0b131713170ba0b0b0b0b3f0b130b0b000106c20a082c2c2c2e0a82c2e0ba9e0b82e802a802c2c2e17031707170717030b0b0a0b0ba00aa82c5c2c2c2c5c2c2c2c2c2c0010c1b02c2c0b02c5c1702c2c80b0b0b0b0b0b0b0b002c0b820b0b0b0b171717170ba0b1b431b46c6c6d0b0b0b1f0b9f0b0b06c6c 24 16777215 10 1023
def hc_87_19 : Nat → Nat := unpackHintV5 0x86493c40a4a01f12500eea27c7241443670ac19e0560c432b45e6ceb2c26c415213c89d3af449694d222ca20fbf55c6eabd43245441674ab89507a84062881c58f60ca86105923082671881028c406fe4582b23340ed9ae05b86d01b649804824c000090 0x82c3e80c0e03030303aa80c3e030380c0e0303a0300caa030703030380c0c0ea030303030383d3e0b0f0f0b0303030303a0303170300c0c0c8cd3e0b0f0f0b0303030303a0303130340c0c0d0f330f070070700307030703078001e0f03c1c1c1c00c0c01c030303007030f030f030303030383c5c0e0f0f000f03c3c3c030301c030303030f00c070070f0f0f0f030707030f0f0f43c4c3d1f03031f03c3c075070750307030703079101e1343c1c1c1d40c0d41d030303507030f032f030303030384c4c0e1317075070f0f0f0f0307070313130f04c4c3c1303030f551343c3c3d030341d030303031340d0f44d072f0f0707030703078307a70707030780c2f00e07070703030307030f032f030303030380c0e03070f070f0f0f0f03070703030f03c0c03030f0733072f0f0f2f03070703032f4bc0d0303330f330f81c1e80c1e0703070381ea0782c3e0f0b80c1e0703a0701caa03030f0f0ba81c1c1c1c0e07070781c1e0b0f0f0b0307070317a0f17170f05c7c3c81c1e0b0f0f0b0307070317a1717131745c4c5d0f330f078001e070070f0300f0f0f01c01c1c1c01c1c1c07070707070070f83c3c3e0f170f0f0f0f0707070701c0070707070f03c3c3c0701c1c1c0f1703c0f070070f130f43c3c3d0f0f0f0f07070707171f1f1703c3c3c7c079101e075070f0350f0f1341d41c1c1d41c1c1d07070707075071384c5c4e13132f0f0f17070707070750713130f04c4c3c0f0f0f0f07070707130f130f41d5070707071343c3c3d0741c1c1d131344d170f44c4c4d0781c0701e07070707070707070707070707070707070707a7070707070781c1c1e072f0f0f170707070707070707070701c1c1c0f0f0f0f07070707170f0f07070707070741c1c1d2f0f0f2f070707071733170f330f00200007a701c0003000707030b0707070700707000007070703070b20002c020b82e0380e80c2e80c2c00000000000000004004015555555554001c1c1c1c1e9c1c1c1c1c1e9c0c0c0c1c0c1c0c1c1c2e0c1c1c1c0c1c0c1c0c1c0c1c0c0c2e9c0c0c2e9c0c0c0c0c1c1c1c1c1c1c1c1c2e9c2c3c2e9c2c2c0c2c2c0c2c0c0c2c1c1c1c1c1c1c1c1c2e9c2c3c2e9c2c2c0c2c2c0c2c0c0c2c3c3c3c3c020001c000720000c000303030303030703a70a0000030303070303030320000c020380e0380e80c0e80c0c00000000000000004004015555555554001c1c1c1c0c0c0c0c0c1c0e9c0c0c0c0c0e0300c0380c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e03030380c0c1c1c1c1c2c3c3c2c0c0c0c0c0c0c0c030f0300c0c0c0c1c1c1c1c2c3c3c2c0c0c0c0c0c0c0d03130340c0c0c0c3c3c3c3c1c2c2c1c0c0c0c0c0c1c0e9c0c0c0c0c0c1c0e9c0c0c0c03030303030303030303030303030303070f0f070b0b0b0b030303030303030303030303073333070b0b0b0b0303030303030303030303030f0f0f0f82c2e80c0e03030303a1780e80c0e030b80c0e0303a0300ca030303a80c1c0c0c0ea030303030393d3e0b0b0b0b0303030303a0303170300c0c0c93d3e0b0b0b0b0303030303a0303130340c0c0d675757000003030303030b03a70000030703030303000303030303030303030303030303030300002c00030000c0300000000001c00b000c003000c1f00c0800000b0b0b0b030303030303032b0313030303030303000106c01c01c0c00c0c0c0c0c0c2c0e9c1e000781c1c02c2c2c1c0c0c00c0c0c0c0c1c000c0c0c1c0c0c0c0c000c00c0c0c0c0c0c0c0c0c0e03030380c0c0c0c0c0c0c0c0c0c10c1b02c2c0b02c0c0c0300c0c0c0c0c0c0c0c00300c0c0301c01c2c2c2c2c0c0c0c0c6d0c6d1b1b1b40c0c0c7c0cac0c0c0c0c0c0c1b1b01c01c1c00c1c0c1c0c1e000781c1c03c0b07030300700c0c0c01c0c2c0c2c0c0c0c0c0e1b170387c5c01f02c2c0f02c0c0c0700c0c0c0c6c0301c01c2c3c3c2c0c1c1c0c7c4c6d1b131f47c0c0c7c1b1b155540c0c0c0c0c2c0e9d55540c1c0c0c0c0d540c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d542c2c2c2c0c0c0c0c0c0c0cac0c7c0c0c0c0c0c0d5550b5540d550340d5555555511507542d503540d50344d035654546d15075070350303030303030b03a7079101e070750b0b0b0703035030303030307550303030703030303550350303030303030303030380c0c0e03030303030303030303075070b0b0b0b03030303131b1304c6c4c03030313032b03030303030353756d0b0b42d0b030340d0303030303030303540d030340d1344d075070750307030703079101e070751342c1c0c0d41d030303507030b030b030303030384c4c0e1317075070b13130b0307070313131304c4c4c13030313544d0b0b44d0b030341d030303031340d1344d070b07070307030707030707a70780c00e07070703030307030b030b030303030380c0e0307070b0b030707030300c030307070b0b030707030340d0303a0aa00aaa081c0c1c0c1c1c0c0c1c1c0c0e0aaa82a2aa8002c0b02c2c02c7c00c07221042d0b42c2d42c4d40d0766446c0a0aaa8281c1c0c0c1c1c0c0e081c0c1c0e282a0aaaaa82c2c02c3c0002c0b00c072202c2d42c3d5042d0b40d0766443c0000001b0f0b0b1b0f0b0b00070703030707030307030703000000aaaa000200000020007c4d46c4d42d1f40d07664007c500541130f0b0b130f0b0b41070703030707030307030703414505aaaa0013130131300b04c0301c88505655555564544caa0aaaa0aa0781e81c0c1c0c2a70a02aaaa0700a0802c00c07221069650b50341d991000000c1c0e9c0c0c0c0c00000c1c0c0c0c0c2a700aaaaaaaa00808080808800880080000000000000000005555555555011000000003030303030703a700000307030303030a9c02aaaaa0385eaa80202020202200220020000000000000000001555555555404400000001c1c2a700aaaa0080808080800000000000000555555011000000000000001c1c0c0c1c1c0c0c1c0c1c0c02aaaaaaaa80000000000000015555555555400000000000007030703070703030707030300aaaaaaaaa000000000000000555555555550000000703030700aaaa000000000055555500 25 33554431 10 1023
def hc_87_20 : Nat → Nat := unpackHintV5 0xb640fab0c160abe936a840eaa321489e393a98896c92d96c8ea10e88a97e82b17e7d395e77c15e73990a6f710a6a315064f15062b0905d495a57b16654f0b050d9064a91924409a23e596c38a96c34c0fa2a22a82022801622800bd2940002f4 0x29c00020001cbc1c2c001c0020b82c02081e000000000000005501105555000000003030303070300000307a0380c0c00080e0380c0e0303a0303a030300000000000000055555555555000000070f070b000a0faaaa170000aaaa17030707070717030000000000000000155555555554000080029c07000001c3c1c8000083e81e0000000000001001005555550029ca729ca70707070707a707a707a707a7aaa9ea7a9ea7aa0029ca729ca700005569da769da755550008200001e9c1e9c1e9c1e9ea802a7a9ea7a9eaaa800a729ca729c00000001a769da769d555554000000000000001c1c1c1c1c1c1c0c1c1c1c0c02aaaaaaa80000b0020001c008000b43d1f1351b1350741d99001f10540141551041c1c1c1c1c1c1c0c1c1c1c0d06aaaaaaa8002c1304c4c04c4c01c072214150b5565541d559151328029ea02081c1c1c1ea0781ea0aaaaaaaa8002c28200701c88410b5a5941d076644a0aa00aaa081c1c1c1c1c1c01c0c1c070382aaaaaaaa000b02c0b0b00b1f00701c88410b42d0b0b50b1350741d9911b0282aaa0a0701c0c01c0e081c1c1c1c1c1eaaaa0aaaa83c3c03c3c0003c0f01c072203c4d43c3d5043d0f41d0766443c0000001b0f1b0b1b0f1b0b0000000707070700aaaaaaaa0002000001c00001f1351b1351b47d0741d99001f14015044c3c4c2c4c3c4c2d0514141c1c1c1d06aaaaaaa8004c4c04c4c04c1301c072214159555507554544caa0aaa801e9c2800707070782aaaaaaaaa00a080bc01c07221069652f50741d99100001e9c001c0c1c0c001c00702002a0380c00720000000000000005555011055000000000000281c0c1e070307070707070700a0f17a0f0f83e0f81e070000000000000005555555555500000000000001c1c1c1c1c1e81c0c1e07030082e0ba0b0ba0b0b81e07000000000000000555555555550000aa00aa000703070300000000550055550000000070307030000a85ea17a81ea070000170b170f170f170baaaa000000000000000001555555555554000000003c5c5c0001c1e81c1c1e0707070700172b17172b0f1717171717a0707000000000000005555555555000000007070707002f1717a07070000000000555555000000000200007a70707070708000021785e0781c0000000000004004015555540282a802aa8207030307030307070301c1c20aaaaaaaaa8002c2c0b02c2c02c7c00c07221042c2d0b42c2d42c4d40d0766446ca00aa0aaa081c1c01c1c0c07030307030382aaaaaaaaa000f0f00f0f00f0f03c3c0301c88410f1350f0f50f3343c3d0341d9910f000001c0c1c0c00006c2c6c3c6c3c6c2c000002aaaaaaa8000007c00c008008001b47d0341d1f1351b13599001f105041c0c1c0d40144c2c4c3c4c3c4c2c155106aaaaaaa8004c1300c0704c4c04c4c221415544d40d559559151320a8001e9c1c0c1c0eaaaa020aaaaaaaaa80000c072820884150341da59664481c1e80c1e0703070381ea0782c2e0b0b80c1e0703a0701ca0b0b0ba80c0e81c1c1c1c0e07070781c1e0b0b0b0b030707030b17a0b0b0b170b02c2c2c81c1e0b0b0b0b030707030b17a0b0b0b130b42c2c2d67575707007078001e0b0300f02c2c1c01c1c1c1c1c1c1c1c07070070070b0b0b0b0b85c5c2e171707070707000b0b03c0b0707070701c1c1c1702c070070b0f0f0b1f131b46c4c7d07070707170b0b1706c6c07507079101e0b0351342c2c1d41c1c1c1c1c1c1c1d07075075070b0b0b0b0b84c4c2e131707070707075070b13130b13131304c4c4c07070707130b0b13550b0b44d0b0707070741c1c1d1342d1344d070707070781c0701e070707070707078307a707070707070707070707070b0b0b0b0781c1e070707070707070707070b0b07070701c1c07070707170b0b17070707070b0b07070741c1d07070707170b0b17070707070303030303030303030703a70380c0300e0307030303030303030303030303030303030380c0c0e0303070707070b0b0b0b0303030303030300c7c0c03030303070707070b0b0b0b0303030303030340c4c0d030303030f1b1b0f 24 16777215 10 1023
def hc_87_21 : Nat → Nat := unpackHintV5 0xc795e9bd5e7811e50d3a25d580012e 0x1c1c1c0c1c1c1c0c1c1c1c1c02aaaaaaa80008000f00000003c3d43c4d43d0f41d07664007c50054145054107070703070707030707070741aaaaaaaa0013130131300f03c0701c8850565543d555515132a0a70a020aa0781e81c1c1c1e0aaaaaaaa8028200f03c0701c8841a594cd0f41d07664400822a81e9c1e9c1e9c1e9c02aaa7a9ea7a9c02a800a729ca729c00000155a769da769c01555400000000c1c0c0c0c0c00000e03030307a00020380e030380c0e80c0e80c0c0000000000000155555555540000001c2c1c2c002aa0baa85c0002aaa82c0c1c1c1c1c2c0c000000000000000555555555500 20 1048575 9 511
def nh_87 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_87_21 (Nat.sub p 672)) (hc_87_20 (Nat.sub p 640)) (Nat.blt p 672)) (hc_87_19 (Nat.sub p 608)) (Nat.blt p 640)) (Bool.rec (Bool.rec (hc_87_18 (Nat.sub p 576)) (hc_87_17 (Nat.sub p 544)) (Nat.blt p 576)) (hc_87_16 (Nat.sub p 512)) (Nat.blt p 544)) (Nat.blt p 608)) (Bool.rec (Bool.rec (Bool.rec (hc_87_15 (Nat.sub p 480)) (hc_87_14 (Nat.sub p 448)) (Nat.blt p 480)) (hc_87_13 (Nat.sub p 416)) (Nat.blt p 448)) (Bool.rec (hc_87_12 (Nat.sub p 384)) (hc_87_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 416)) (Nat.blt p 512)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_87_10 (Nat.sub p 320)) (hc_87_9 (Nat.sub p 288)) (Nat.blt p 320)) (hc_87_8 (Nat.sub p 256)) (Nat.blt p 288)) (Bool.rec (Bool.rec (hc_87_7 (Nat.sub p 224)) (hc_87_6 (Nat.sub p 192)) (Nat.blt p 224)) (hc_87_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 256)) (Bool.rec (Bool.rec (Bool.rec (hc_87_4 (Nat.sub p 128)) (hc_87_3 (Nat.sub p 96)) (Nat.blt p 128)) (hc_87_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_87_1 (Nat.sub p 32)) (hc_87_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 352)
def f_87 : Nat → Nat × Nat := unpackForestF 0x151955a8c2a80317e9fadb4fb49a7d2480316e9c6c34e2610062bd351b297acb4b945a5c2280314e928b349455a48aad24154016be00b5ba2a36d151868a4d945261a2d23d14980016af42b5ea15ab50a4d68506a00b53a0524d025168108a00b4f9f1a74f88e67c26b3e035005a5cf0946782bb3c05d005a3cd759e6b8ad35b679ada74d6d366b4733593b9ac9bcd64d66b077358379ac1a802d0e668b333455998aaccc154014bf31c5b98e2980296e5c8db2e461971b64b8d865d68f2e3600052bcae97a574ad2b92595c1280294e536932994594c2280293e4d8d726a4e9351f49a4964d04a00a4b925a8c92576490ba00a478eeb3c771ae3b6ad1da678ed274768fa3b47b1d92b8ec93c764963b0571d8278ec1280290e366bd1b3568d89ac6c0d40147f1825e8c12b4608fa3024b180250051dc5716a2b8a51594d8ac268028de294a906d6b89d3e41b59e2547b06b4483533c1a97e21acd06a5e8352d438d121c2db0e06d8352bc351aa0d4ad06a5285c0ac1a4ae158a90692783492c231521104d0682b83e2a41a09e0d04a00a33004afc1291209288ff4538191a40c4d1fe6a701a3480c9a3fcd0dfe2bcff1567f8a73fc4f8012b6f7c6d7be30bded85ef696fbd7c7ddbe3ded0def4c2f7a4b7cabe3e49f1ef486f827c7bd1980255de82bcf41567a00c3d0055e9086f4014004a9bbed8ddf692efa6377d24bc409ddf466f023377c2280253dd38bee9c5374da9ba6d2dd9268e9b4374cab3a6539d327cea34374c0a80252dadac6d6c6373eb435adbdcc6d8e635c6b5b1b5ad7dad6a6e446e6b5a8b8d1b1ad69ee236c6b5a1b855a1ad4dedfa6c6fd2e35a98dad4bed6a536edb735a945b98d8d6a4f6b521b5a8fdad476da4606b51bb62d11b14d8d6a336b4a735c8cdad0ba009476ac9a348d0da44acd215e690a73484f9a5686d2015004a1b2ed7d976bccbb5a65dabb2ed59976a4cba5b66d2232e94d97472cc25b65c1a8024fd922bcc91566489f32405401276c5c5a62e2931d1818b4aec5a4162c268024dd89268c1b5360caf3065598329cc193e60c0a8024cd788b6bc4535e12f2f0969784acbc2525e1272f0909798b6bc02500497ae6579732acb994e5cc0a8024ad716c0b64575b1ad2d8d496c684b603d00493ad4511648a6b215e590ab2c85396427cb201500491ac253d6128e0085f578a22bc111538a6ad93456c1a2a6d4d58268ac03454da1aa6179530aca984e54c1f00216d448daa2461511b0a88d2d4caf8a637c511a1a8898544496a3d7c51d3e28890d454f8a22330042ba7a1793d0ac9e82c4f41327c50d3d048008534bdb1a5ed252f4c697a494dc93a5e8cd2f2de9a2334bca2a648e52f27e9824e4bc9780213d1e8be8f453479afa3cd4d1e69e8f34b49c2e23cd1d248a892034479a1a3c1591e09c8f03e47da1a3c0980109677d633be31a355a0ef6de8bb6c45dae1ded8cef6be77b5344e371ded45118d877b4f43db61ded0d0dad077a6f42936214970ef4c677a5f3bd29a0cdb8ef4a28246c3bd27a049b0ef48677a3f3bd1d9fd180ef46e7db443ed361de8ccef2de7c2333bcae9ecdb0ef27e7a4603bc9b9de4bcf16c0779273bc2700211ced068713433ac121c490ce904871233388ab1c4178e209c7103e38da19c4098010866835f341af1a0d68d06ae68356341a91a096cd9488682533411c9ac8e4d02be6a36c340ab9a496cd026a6812f0041f99c090c94766485e3242b1920f8c904c0083b2fa2d17d148c58c05f2572f920985180be2ae5f14d2fda817c49c0106e5e0342c9a9974090b24a65c0242c919964178b20ac5904e2c81f164098010664f45b2bd2213d14c9e4be4f25e2792d13c95c9e4ac4f2522792713c908a549c4f15f28d3613c55ca14884f14f27e2d93c4940105e4c85e2642b1321389904c0082b25db011d15c8e6b447352239a1124d808e2ae48350238a391c4f40104e4604420a29914090824a64402420921904178820ac4104e2081f104098010463c45f1e2298f0d4c786963c3431e0af0f05587829c3c13e0040f8d317c698a634b5f1a5a98d2d3c6969634b471be2a0d2d0c690bc348561a4270d20f86904c0081b19d3403b5bc654b00ed6318d3403b1bc614900ec63179ac8bc9601d8be2e3490762d8b2d84594c00ec57159a48ac9201d8a62a268075b78a48e01d6c627c5913d2c03ad7c4d6bc0eb5b12a308949801d6ae23b5e11d1c03ad4c1d69e2234e075a58849401d68e1d4540e9b78791503d8a81e2700e9b38748e01d6860ea630752f06d14c1d4b61a5620752d03a95831288174530b8af05c5381d4a61656e0752903a9382929c0ea4b09e3583a90c258dc0ea420751f0445781d4761056b0751983cdb81d4640081706c2a00517c190880145305c1a004d4c026960a034009a180ed3c0768603a4301d1d80e8cc0d2680634301ca180e4ec072660392301c0f004490020bc01056008270040f8010260003f 10 11
def ch_87 : Nat → Bool := dagCheckNodeV5 fullMask g_87 ep_87 6 63 bds_87 677 (dagTraceF fullMask rootStock 11 f_87) cur_87 nh_87
set_option maxHeartbeats 0 in
theorem rc_87 : dagCheckRootsV5 fullMask g_87 ep_87 6 63 677 bds_87 (dagTraceF fullMask rootStock 11 f_87) (cur_87 0) (nh_87 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_0 : treeBlockF 0 32 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_1 : treeBlockF 32 64 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_2 : treeBlockF 64 96 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_3 : treeBlockF 96 128 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_4 : treeBlockF 128 160 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_5 : treeBlockF 160 192 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_6 : treeBlockF 192 224 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_7 : treeBlockF 224 256 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_8 : treeBlockF 256 288 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_9 : treeBlockF 288 320 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_10 : treeBlockF 320 352 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_11 : treeBlockF 352 384 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_12 : treeBlockF 384 416 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_13 : treeBlockF 416 448 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_14 : treeBlockF 448 480 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_15 : treeBlockF 480 512 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_16 : treeBlockF 512 544 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_17 : treeBlockF 544 576 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_18 : treeBlockF 576 608 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_19 : treeBlockF 608 640 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_20 : treeBlockF 640 672 ch_87 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_21 : treeBlockF 672 677 ch_87 = true := by decide +kernel
theorem nj_87_1 : ∀ i, 0 ≤ i → i < 64 → ch_87 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_87_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_87_1 h1 h2)
theorem nj_87_2 : ∀ i, 0 ≤ i → i < 96 → ch_87 i = true := block_join nj_87_1 (fun _ h1 h2 => treeBlockF_at nb_87_2 h1 h2)
theorem nj_87_3 : ∀ i, 0 ≤ i → i < 128 → ch_87 i = true := block_join nj_87_2 (fun _ h1 h2 => treeBlockF_at nb_87_3 h1 h2)
theorem nj_87_4 : ∀ i, 0 ≤ i → i < 160 → ch_87 i = true := block_join nj_87_3 (fun _ h1 h2 => treeBlockF_at nb_87_4 h1 h2)
theorem nj_87_5 : ∀ i, 0 ≤ i → i < 192 → ch_87 i = true := block_join nj_87_4 (fun _ h1 h2 => treeBlockF_at nb_87_5 h1 h2)
theorem nj_87_6 : ∀ i, 0 ≤ i → i < 224 → ch_87 i = true := block_join nj_87_5 (fun _ h1 h2 => treeBlockF_at nb_87_6 h1 h2)
theorem nj_87_7 : ∀ i, 0 ≤ i → i < 256 → ch_87 i = true := block_join nj_87_6 (fun _ h1 h2 => treeBlockF_at nb_87_7 h1 h2)
theorem nj_87_8 : ∀ i, 0 ≤ i → i < 288 → ch_87 i = true := block_join nj_87_7 (fun _ h1 h2 => treeBlockF_at nb_87_8 h1 h2)
theorem nj_87_9 : ∀ i, 0 ≤ i → i < 320 → ch_87 i = true := block_join nj_87_8 (fun _ h1 h2 => treeBlockF_at nb_87_9 h1 h2)
theorem nj_87_10 : ∀ i, 0 ≤ i → i < 352 → ch_87 i = true := block_join nj_87_9 (fun _ h1 h2 => treeBlockF_at nb_87_10 h1 h2)
theorem nj_87_11 : ∀ i, 0 ≤ i → i < 384 → ch_87 i = true := block_join nj_87_10 (fun _ h1 h2 => treeBlockF_at nb_87_11 h1 h2)
theorem nj_87_12 : ∀ i, 0 ≤ i → i < 416 → ch_87 i = true := block_join nj_87_11 (fun _ h1 h2 => treeBlockF_at nb_87_12 h1 h2)
theorem nj_87_13 : ∀ i, 0 ≤ i → i < 448 → ch_87 i = true := block_join nj_87_12 (fun _ h1 h2 => treeBlockF_at nb_87_13 h1 h2)
theorem nj_87_14 : ∀ i, 0 ≤ i → i < 480 → ch_87 i = true := block_join nj_87_13 (fun _ h1 h2 => treeBlockF_at nb_87_14 h1 h2)
theorem nj_87_15 : ∀ i, 0 ≤ i → i < 512 → ch_87 i = true := block_join nj_87_14 (fun _ h1 h2 => treeBlockF_at nb_87_15 h1 h2)
theorem nj_87_16 : ∀ i, 0 ≤ i → i < 544 → ch_87 i = true := block_join nj_87_15 (fun _ h1 h2 => treeBlockF_at nb_87_16 h1 h2)
theorem nj_87_17 : ∀ i, 0 ≤ i → i < 576 → ch_87 i = true := block_join nj_87_16 (fun _ h1 h2 => treeBlockF_at nb_87_17 h1 h2)
theorem nj_87_18 : ∀ i, 0 ≤ i → i < 608 → ch_87 i = true := block_join nj_87_17 (fun _ h1 h2 => treeBlockF_at nb_87_18 h1 h2)
theorem nj_87_19 : ∀ i, 0 ≤ i → i < 640 → ch_87 i = true := block_join nj_87_18 (fun _ h1 h2 => treeBlockF_at nb_87_19 h1 h2)
theorem nj_87_20 : ∀ i, 0 ≤ i → i < 672 → ch_87 i = true := block_join nj_87_19 (fun _ h1 h2 => treeBlockF_at nb_87_20 h1 h2)
theorem nj_87_21 : ∀ i, 0 ≤ i → i < 677 → ch_87 i = true := block_join nj_87_20 (fun _ h1 h2 => treeBlockF_at nb_87_21 h1 h2)
theorem nc_87 : ∀ i, 0 ≤ i → i < 677 → ch_87 i = true := nj_87_21
theorem lb_87 : LowerBin fullMask rootStock g_87 12 :=
  lowerDagV5 (kn_cons lb_56 (kn_cons lb_52 (kn_cons lb_49 (kn_cons lb_76 (kn_cons lb_80 (kn_cons lb_65 (kn_cons lb_55 (kn_cons lb_66 (kn_cons lb_64 (kn_cons lb_54 (kn_cons lb_45 (kn_cons lb_53 (kn_cons lb_75 (kn_cons lb_82 (kn_cons lb_81 (kn_cons lb_48 (kn_cons lb_46 (kn_cons lb_70 (kn_cons lb_44 (kn_cons lb_60 (kn_cons lb_73 (kn_cons lb_72 (kn_cons lb_57 (kn_cons lb_58 (kn_cons lb_43 (kn_cons lb_71 (kn_cons lb_77 (kn_cons lb_62 (kn_cons lb_74 (kn_cons lb_59 (kn_cons lb_61 (kn_cons lb_51 (kn_cons lb_63 (kn_cons lb_69 (kn_cons lb_42 (kn_cons lb_83 (kn_cons lb_85 (kn_cons lb_86 (kn_cons lb_84 (kn_cons lb_79 (kn_cons lb_16 (kn_cons lb_78 (kn_cons lb_67 (kn_cons lb_68 (kn_nil))))))))))))))))))))))))))))))))))))))))))))) rc_87 nc_87 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [7, 13]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 3936929920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276808360 * 2 ^ 32 + 3936929920)) (13 - 1) := by
  rw [show canon fullMask (4276808360 * 2 ^ 32 + 3936929920) = g_87 by decide]
  exact lb_87

end PEqualNP.Outside.L_meta_48476

theorem PEqualNP.Outside.L_meta_48476 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 3936929920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 3936929920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48476.table2_from_lowerBin (4276808360 * 2 ^ 32 + 3936929920) 13 PEqualNP.Outside.L_meta_48476.root_lb PEqualNP.Outside.L_meta_48476.wg 18 rfl PEqualNP.Outside.L_meta_48476.wfits PEqualNP.Outside.L_meta_48476.weval
