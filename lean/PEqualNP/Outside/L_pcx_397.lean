import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_397_aux

section

def hdrSplit : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: r => some (0, r)
  | true :: r => (hdrSplit r).map (fun p => (p.1 + 1, p.2))

def parse (x : List Bool) : Option (ℕ × ℕ × ℕ × ℕ × List Bool) :=
  (hdrSplit x).bind fun p1 => (hdrSplit p1.2).bind fun p2 => (hdrSplit p2.2).bind fun p3 =>
    (hdrSplit p3.2).map fun p4 => (p1.1, p2.1, p3.1, p4.1, p4.2)

def scan : Bool → Bool → List Bool → List Bool → List Bool
  | _, _, [], _ => []
  | _, _, x :: v, [] => x :: v
  | m0, m1, x :: v, y :: b =>
    (if m0 then (if m1 then Bool.xor x y else x) else (if y then false else x)) ::
      scan (m0 || y) (if m0 then m1 else (if y then x else m1)) v b

def red1 (b v : List Bool) : List Bool := scan false false v b

def reduce (B : List (List Bool)) (v : List Bool) : List Bool :=
  B.foldl (fun v b => red1 b v) v

def ins (B : List (List Bool)) (v : List Bool) : List (List Bool) :=
  if (reduce B v).any id then B ++ [reduce B v] else B

def basisOf (vs : List (List Bool)) : List (List Bool) := vs.foldl ins []

def mask (ci cj : List Bool) : List Bool :=
  (ci.zip cj).flatMap fun p => (ci.zip cj).map fun q => Bool.xor (p.1 && q.2) (p.2 && q.1)

def dotAcc : Bool → List Bool → List Bool → Bool
  | acc, [], _ => acc
  | acc, x :: z, a => dotAcc (Bool.xor acc (x && a.headD false)) z a.tail

def dots (z : List Bool) : ℕ → List Bool → List Bool
  | 0, _ => []
  | e + 1, a => dotAcc false z a :: dots z e (a.drop z.length)

def chunk (len : ℕ) : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | c + 1, l => l.take len :: chunk len c (l.drop len)

def verifyFn (z : List Bool × List Bool) : Bool :=
  match parse z.1 with
  | none => false
  | some (n, m, k, d, a) =>
    decide (k ≤ m) && decide (a.length = m * n * n) &&
      decide (z.2.length = (n + m - (k + d)) * n) &&
      decide (n + m - (k + d) ≤ (basisOf (chunk n (n + m - (k + d)) z.2)).length) &&
      decide ((basisOf ((chunk n (n + m - (k + d)) z.2).flatMap fun ci =>
        (chunk n (n + m - (k + d)) z.2).map fun cj => dots (mask ci cj) m a)).length ≤ k)

def Rel : Set (List Bool × List Bool) :=
  let F := ZMod 2
  let header := fun n : ℕ => List.replicate n true ++ [false]
  let pack := fun (n m k d : ℕ) (A : Fin m → Fin n → Fin n → Bool) =>
    header n ++ header m ++ header k ++ header d ++
      (List.finRange m).flatMap (fun e => (List.finRange n).flatMap
        (fun i => (List.finRange n).map (fun j => A e i j)))
  let quad := fun (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool)
      (x : Fin n → F) (e : Fin m) =>
    Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
      if A e i j then x i * x j else 0))
  {z | ∃ (n m k d : ℕ)
      (A : Fin m → Fin n → Fin n → Bool),
    k ≤ m ∧ pack n m k d A = z.1 ∧
      let t := n+m-(k+d)
      let Q := quad n m A
      ∃ cols : Fin t → (Fin n → F),
        (List.finRange t).flatMap (fun i => (List.finRange n).map
          (fun j => decide (cols i j = 1))) = z.2 ∧
        Module.finrank F (Submodule.span F (Set.range cols)) = t ∧
        Module.finrank F (Submodule.span F (Set.range (fun ij : Fin t × Fin t =>
          Q (cols ij.1 + cols ij.2) - Q (cols ij.1) - Q (cols ij.2) + Q 0))) ≤ k}

def toVec (n : ℕ) (l : List Bool) : Fin n → ZMod 2 := fun i => if l.getD i false then 1 else 0

end

section

theorem rk_scan_len : ∀ (v b : List Bool) (m0 m1 : Bool), (scan m0 m1 v b).length = v.length
  | [], _, _, _ => by simp [scan]
  | _ :: _, [], _, _ => by simp [scan]
  | _ :: v, _ :: b, m0, m1 => by simp [scan, rk_scan_len v b]

theorem rk_scan_tf : ∀ (v b : List Bool), scan true false v b = v
  | [], _ => by simp [scan]
  | _ :: _, [] => by simp [scan]
  | _ :: v, _ :: b => by simp [scan, rk_scan_tf v b]

theorem rk_scan_tt : ∀ (v b : List Bool), v.length = b.length →
    scan true true v b = List.zipWith Bool.xor v b
  | [], _, _ => by simp [scan]
  | _ :: _, [], h => by simp at h
  | _ :: v, _ :: b, h => by
    have h' : v.length = b.length := by simpa using h
    simp [scan, rk_scan_tt v b h']

theorem rk_getD_xor : ∀ (v b : List Bool) (i : ℕ), v.length = b.length →
    (List.zipWith Bool.xor v b).getD i false = Bool.xor (v.getD i false) (b.getD i false)
  | [], [], _, _ => by simp
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | _ :: _, _ :: _, 0, _ => by simp
  | _ :: v, _ :: b, i + 1, h => by
    have h' : v.length = b.length := by simpa using h
    simpa using rk_getD_xor v b i h'

theorem rk_red1_spec : ∀ (b : List Bool),
    ((∀ i, b.getD i false = false) ∧ ∀ v : List Bool, v.length = b.length → red1 b v = v) ∨
    ∃ p, p < b.length ∧ b.getD p false = true ∧ ∀ v : List Bool, v.length = b.length →
      red1 b v = if v.getD p false then List.zipWith Bool.xor v b else v
  | [] => Or.inl ⟨by simp, by intro v hv; cases v <;> simp [red1, scan] at *⟩
  | false :: b => by
    rcases rk_red1_spec b with ⟨h1, h2⟩ | ⟨p, hp, hbp, h2⟩
    · left
      refine ⟨?_, ?_⟩
      · intro i
        cases i with
        | zero => simp
        | succ i => simpa using h1 i
      · intro v hv
        cases v with
        | nil => simp at hv
        | cons x v =>
          have hv' : v.length = b.length := by simpa using hv
          have h3 := h2 v hv'
          simp only [red1] at h3 ⊢
          simp [scan, h3]
    · right
      refine ⟨p + 1, by simpa using hp, by simpa using hbp, ?_⟩
      intro v hv
      cases v with
      | nil => simp at hv
      | cons x v =>
        have hv' : v.length = b.length := by simpa using hv
        have h3 := h2 v hv'
        simp only [red1] at h3 ⊢
        simp [scan, h3]
        split <;> rfl
  | true :: b => by
    right
    refine ⟨0, by simp, by simp, ?_⟩
    intro v hv
    cases v with
    | nil => simp at hv
    | cons x v =>
      have hv' : v.length = b.length := by simpa using hv
      cases x <;> simp [red1, scan, rk_scan_tf, rk_scan_tt v b hv']

theorem rk_toVec_xor (n : ℕ) (v b : List Bool) (h : v.length = b.length) :
    toVec n (List.zipWith Bool.xor v b) = toVec n v + toVec n b := by
  funext i
  simp only [toVec, Pi.add_apply, rk_getD_xor v b i h]
  cases v.getD i false <;> cases b.getD i false <;> decide

def rk_Piv (n : ℕ) (b : List Bool) (p : Fin n) : Prop :=
  toVec n b p = 1 ∧ ∀ v : List Bool, v.length = n →
    toVec n (red1 b v) = toVec n v + toVec n v p • toVec n b

theorem rk_piv_of_ne (n : ℕ) (b : List Bool) (hb : b.length = n) (hne : toVec n b ≠ 0) :
    ∃ p : Fin n, rk_Piv n b p := by
  rcases rk_red1_spec b with ⟨h1, _⟩ | ⟨p, hp, hbp, h2⟩
  · exfalso
    apply hne
    funext i
    show (if b.getD i false then (1 : ZMod 2) else 0) = 0
    rw [h1]
    rfl
  · refine ⟨⟨p, hb ▸ hp⟩, ?_, ?_⟩
    · show (if b.getD p false then (1 : ZMod 2) else 0) = 1
      rw [hbp]
      rfl
    · intro v hv
      rw [h2 v (hv.trans hb.symm)]
      cases hvp : v.getD p false
      · have h3 : toVec n v ⟨p, hb ▸ hp⟩ = 0 := by
          show (if v.getD p false then (1 : ZMod 2) else 0) = 0
          rw [hvp]
          rfl
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h3, zero_smul, add_zero]
      · have h3 : toVec n v ⟨p, hb ▸ hp⟩ = 1 := by
          show (if v.getD p false then (1 : ZMod 2) else 0) = 1
          rw [hvp]
          rfl
        simp only [↓reduceIte]
        rw [h3, rk_toVec_xor n v b (hv.trans hb.symm), one_smul]

theorem rk_any_iff (n : ℕ) (r : List Bool) (h : r.length = n) :
    r.any id = true ↔ toVec n r ≠ 0 := by
  constructor
  · intro ha hz
    rw [List.any_eq_true] at ha
    obtain ⟨x, hx, hxt⟩ := ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have h3 := congrFun hz ⟨i, h ▸ hi⟩
    simp only [id] at hxt
    simp [toVec, hi, hxt] at h3
  · intro hne
    by_contra ha
    apply hne
    funext i
    have h4 : r.getD i false = false := by
      by_contra h5
      apply ha
      rw [List.any_eq_true]
      have hi : (i : ℕ) < r.length := h ▸ i.2
      refine ⟨r[(i : ℕ)], List.getElem_mem hi, ?_⟩
      simpa [hi] using h5
    show (if r.getD i false then (1 : ZMod 2) else 0) = 0
    rw [h4]
    rfl

def rk_S (n : ℕ) (L : List (List Bool)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) {u : Fin n → ZMod 2 | ∃ v ∈ L, toVec n v = u}

theorem rk_S_nil (n : ℕ) : rk_S n [] = ⊥ := by simp [rk_S]

theorem rk_S_append (n : ℕ) (L M : List (List Bool)) :
    rk_S n (L ++ M) = rk_S n L ⊔ rk_S n M := by
  unfold rk_S
  rw [← Submodule.span_union]
  congr 1
  ext u
  simp [or_and_right, exists_or]

theorem rk_S_single (n : ℕ) (b : List Bool) :
    rk_S n [b] = Submodule.span (ZMod 2) {toVec n b} := by
  unfold rk_S
  congr 1
  ext u
  simp [eq_comm]

theorem rk_S_cons (n : ℕ) (b : List Bool) (L : List (List Bool)) :
    rk_S n (b :: L) = Submodule.span (ZMod 2) {toVec n b} ⊔ rk_S n L := by
  rw [← rk_S_single, ← rk_S_append]
  rfl

theorem rk_S_snoc (n : ℕ) (L : List (List Bool)) (b : List Bool) :
    rk_S n (L ++ [b]) = rk_S n L ⊔ Submodule.span (ZMod 2) {toVec n b} := by
  rw [rk_S_append, rk_S_single]

theorem rk_S_vanish (n : ℕ) (L : List (List Bool)) (p : Fin n)
    (h : ∀ c ∈ L, toVec n c p = 0) (u : Fin n → ZMod 2) (hu : u ∈ rk_S n L) : u p = 0 := by
  have hle : rk_S n L ≤
      LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n => ZMod 2) p) := by
    apply Submodule.span_le.mpr
    rintro u ⟨c, hc, rfl⟩
    simpa using h c hc
  simpa using hle hu

def rk_Ech (n : ℕ) : List (List Bool) → Prop
  | [] => True
  | b :: rest => b.length = n ∧
      (∃ p : Fin n, rk_Piv n b p ∧ ∀ c ∈ rest, toVec n c p = 0) ∧ rk_Ech n rest

theorem rk_reduce_len : ∀ (B : List (List Bool)) (v : List Bool),
    (reduce B v).length = v.length
  | [], _ => rfl
  | b :: B, v => by
    show (reduce B (red1 b v)).length = v.length
    rw [rk_reduce_len B, red1, rk_scan_len]

theorem rk_reduce_mod (n : ℕ) : ∀ (B : List (List Bool)) (v : List Bool),
    rk_Ech n B → v.length = n →
    ∃ s ∈ rk_S n B, toVec n (reduce B v) = toVec n v + s
  | [], v, _, _ => ⟨0, Submodule.zero_mem _, by simp [reduce]⟩
  | b :: B, v, hE, hv => by
    obtain ⟨hb, ⟨p, ⟨hp1, hp2⟩, hrest⟩, hE'⟩ := hE
    have hw : (red1 b v).length = n := by rw [red1, rk_scan_len, hv]
    obtain ⟨s, hs, hs2⟩ := rk_reduce_mod n B (red1 b v) hE' hw
    refine ⟨toVec n v p • toVec n b + s, ?_, ?_⟩
    · rw [rk_S_cons]
      exact Submodule.add_mem_sup
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) hs
    · show toVec n (reduce B (red1 b v)) = _
      rw [hs2, hp2 v hv, add_assoc]

theorem rk_reduce_zero (n : ℕ) : ∀ (B : List (List Bool)) (v : List Bool),
    rk_Ech n B → v.length = n → toVec n v ∈ rk_S n B → toVec n (reduce B v) = 0
  | [], v, _, _, hm => by
    rw [rk_S_nil] at hm
    simpa [reduce] using hm
  | b :: B, v, hE, hv, hm => by
    obtain ⟨hb, ⟨p, ⟨hp1, hp2⟩, hrest⟩, hE'⟩ := hE
    have hw : (red1 b v).length = n := by rw [red1, rk_scan_len, hv]
    rw [rk_S_cons] at hm
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hm
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hzp : z p = 0 := rk_S_vanish n B p hrest z hz
    have ha : toVec n v p = a := by
      rw [← hyz]
      simp [hp1, hzp]
    have hwz : toVec n (red1 b v) = z := by
      rw [hp2 v hv, ha, ← hyz]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [add_comm (a * toVec n b i) (z i), add_assoc, CharTwo.add_self_eq_zero, add_zero]
    show toVec n (reduce B (red1 b v)) = 0
    exact rk_reduce_zero n B (red1 b v) hE' hw (hwz ▸ hz)

theorem rk_ech_snoc (n : ℕ) : ∀ (B : List (List Bool)) (v : List Bool),
    rk_Ech n B → v.length = n → toVec n (reduce B v) ≠ 0 → rk_Ech n (B ++ [reduce B v])
  | [], v, _, hv, hne => by
    obtain ⟨p, hp⟩ := rk_piv_of_ne n v hv hne
    exact ⟨hv, ⟨p, hp, by simp⟩, trivial⟩
  | b :: B, v, hE, hv, hne => by
    obtain ⟨hb, ⟨p, ⟨hp1, hp2⟩, hrest⟩, hE'⟩ := hE
    have hw : (red1 b v).length = n := by rw [red1, rk_scan_len, hv]
    have hrec := rk_ech_snoc n B (red1 b v) hE' hw hne
    refine ⟨hb, ⟨p, ⟨hp1, hp2⟩, ?_⟩, hrec⟩
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hrest c hc
    · rw [List.mem_singleton] at hc
      subst hc
      obtain ⟨s, hs, hs2⟩ := rk_reduce_mod n B (red1 b v) hE' hw
      have hsp := rk_S_vanish n B p hrest s hs
      show toVec n (reduce B (red1 b v)) p = 0
      rw [hs2, hp2 v hv]
      simp [hp1, hsp, CharTwo.add_self_eq_zero]

theorem rk_ech_finrank (n : ℕ) : ∀ (B : List (List Bool)), rk_Ech n B →
    Module.finrank (ZMod 2) (rk_S n B) = B.length
  | [], _ => by
    rw [rk_S_nil]
    simp
  | b :: B, hE => by
    obtain ⟨hb, ⟨p, ⟨hp1, hp2⟩, hrest⟩, hE'⟩ := hE
    have ih := rk_ech_finrank n B hE'
    have hbne : toVec n b ≠ 0 := fun h => by simp [h] at hp1
    have hnot : toVec n b ∉ rk_S n B := fun h => by
      have h3 := rk_S_vanish n B p hrest _ h
      rw [hp1] at h3
      exact one_ne_zero h3
    have hdisj : Submodule.span (ZMod 2) {toVec n b} ⊓ rk_S n B = ⊥ := by
      rw [inf_comm, ← disjoint_iff]
      exact (Submodule.disjoint_span_singleton' hbne).mpr hnot
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span (ZMod 2) {toVec n b}) (rk_S n B)
    rw [hdisj, finrank_bot, finrank_span_singleton hbne, ih, ← rk_S_cons] at h4
    rw [List.length_cons]
    omega

theorem rk_sup_span (n : ℕ) (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (x y s : Fin n → ZMod 2) (hs : s ∈ S) (h : y = x + s) :
    S ⊔ Submodule.span (ZMod 2) {y} = S ⊔ Submodule.span (ZMod 2) {x} := by
  apply le_antisymm
  · refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    rw [h]
    exact add_mem (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
      (Submodule.mem_sup_left hs)
  · refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    have hx : x = y - s := eq_sub_of_add_eq h.symm
    rw [hx]
    exact sub_mem (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))
      (Submodule.mem_sup_left hs)

theorem rk_ins (n : ℕ) (B P : List (List Bool)) (v : List Bool) (hv : v.length = n)
    (hE : rk_Ech n B) (hS : rk_S n B = rk_S n P) :
    rk_Ech n (ins B v) ∧ rk_S n (ins B v) = rk_S n (P ++ [v]) := by
  have hlen : (reduce B v).length = n := by rw [rk_reduce_len, hv]
  obtain ⟨s, hs, hs2⟩ := rk_reduce_mod n B v hE hv
  unfold ins
  by_cases hany : (reduce B v).any id = true
  · simp only [hany, ↓reduceIte]
    have hne := (rk_any_iff n _ hlen).mp hany
    refine ⟨rk_ech_snoc n B v hE hv hne, ?_⟩
    rw [rk_S_snoc, rk_S_snoc, ← hS]
    exact rk_sup_span n _ _ _ s hs hs2
  · simp only [hany]
    have hz : toVec n (reduce B v) = 0 := by
      by_contra hne
      exact hany ((rk_any_iff n _ hlen).mpr hne)
    refine ⟨hE, ?_⟩
    rw [rk_S_snoc, ← hS]
    have hvm : toVec n v ∈ rk_S n B := by
      have h5 : toVec n v = -s := eq_neg_of_add_eq_zero_left (hs2 ▸ hz)
      rw [h5]
      exact neg_mem hs
    exact (sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hvm)).symm

theorem rk_fold (n : ℕ) : ∀ (vs : List (List Bool)) (B P : List (List Bool)),
    (∀ v ∈ vs, v.length = n) → rk_Ech n B → rk_S n B = rk_S n P →
    rk_Ech n (vs.foldl ins B) ∧ rk_S n (vs.foldl ins B) = rk_S n (P ++ vs)
  | [], B, P, _, hE, hS => by simpa using ⟨hE, hS⟩
  | v :: vs, B, P, h, hE, hS => by
    have hv : v.length = n := h v (by simp)
    have key := rk_ins n B P v hv hE hS
    have h6 := rk_fold n vs (ins B v) (P ++ [v]) (fun w hw => h w (by simp [hw])) key.1 key.2
    simpa using h6

theorem basisOf_rank (n : ℕ) (vs : List (List Bool)) (h : ∀ v ∈ vs, v.length = n) :
    (basisOf vs).length = Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) {u : Fin n → ZMod 2 | ∃ v ∈ vs, toVec n v = u}) := by
  have h7 := rk_fold n vs [] [] h trivial rfl
  have h8 := rk_ech_finrank n _ h7.1
  rw [h7.2] at h8
  exact h8.symm

end

section

theorem rl_hdrSplit_iff (x : List Bool) : ∀ (c : ℕ) (r : List Bool),
    hdrSplit x = some (c, r) ↔ x = List.replicate c true ++ false :: r := by
  induction x with
  | nil => intro c r; simp [hdrSplit]
  | cons b x ih =>
    intro c r
    cases b
    · cases c <;> simp [hdrSplit, List.replicate_succ]
    · cases c with
      | zero => simp [hdrSplit]
      | succ c =>
        simp only [hdrSplit, List.replicate_succ, List.cons_append, List.cons.injEq, true_and,
          ← ih, Option.map_eq_some_iff, Prod.mk.injEq, Nat.add_right_cancel_iff]
        constructor
        · rintro ⟨⟨p1, p2⟩, hp, h1, h2⟩
          simp only at h1 h2
          rw [hp, h1, h2]
        · intro h
          exact ⟨(c, r), h, rfl, rfl⟩

theorem rl_parse_iff (x : List Bool) (n m k d : ℕ) (a : List Bool) :
    parse x = some (n, m, k, d, a) ↔
      x = List.replicate n true ++ [false] ++ (List.replicate m true ++ [false]) ++
        (List.replicate k true ++ [false]) ++ (List.replicate d true ++ [false]) ++ a := by
  unfold parse
  constructor
  · intro h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨c1, r1⟩, h1, ⟨c2, r2⟩, h2, ⟨c3, r3⟩, h3, ⟨c4, r4⟩, h4, e1, e2, e3, e4, e5⟩ := h
    simp only at h2 h3 h4 e1 e2 e3 e4 e5
    subst e1 e2 e3 e4 e5
    rw [rl_hdrSplit_iff] at h1 h2 h3 h4
    subst h4 h3 h2
    rw [h1]
    simp [List.append_assoc]
  · intro h
    have h1 : hdrSplit x = some (n, List.replicate m true ++ false ::
        (List.replicate k true ++ false :: (List.replicate d true ++ false :: a))) := by
      rw [rl_hdrSplit_iff, h]; simp [List.append_assoc]
    rw [h1]
    simp only [Option.bind_some]
    rw [(rl_hdrSplit_iff _ m _).2 rfl]
    simp only [Option.bind_some]
    rw [(rl_hdrSplit_iff _ k _).2 rfl]
    simp only [Option.bind_some]
    rw [(rl_hdrSplit_iff _ d _).2 rfl]
    rfl

def rl_b2 (b : Bool) : ZMod 2 := if b then 1 else 0

theorem rl_b2_xor (p q : Bool) : rl_b2 (Bool.xor p q) = rl_b2 p + rl_b2 q := by
  cases p <;> cases q <;> decide

theorem rl_b2_and (p q : Bool) : rl_b2 (p && q) = rl_b2 p * rl_b2 q := by
  cases p <;> cases q <;> decide

theorem rl_b2_decide (c : ZMod 2) : rl_b2 (decide (c = 1)) = c := by
  revert c; decide

theorem rl_decide_b2 (b : Bool) : decide (rl_b2 b = 1) = b := by
  cases b <;> decide

theorem rl_flatMap_getD {α : Type} (len : ℕ) (g : α → List Bool) :
    ∀ (L : List α), (∀ x ∈ L, (g x).length = len) →
      (L.flatMap g).length = L.length * len ∧
      ∀ (i : ℕ) (x : α), L[i]? = some x → ∀ j, j < len →
        (L.flatMap g).getD (i * len + j) false = (g x).getD j false := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons y L ih =>
    intro h
    have hy : (g y).length = len := h y (by simp)
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => h x (by simp [hx]))
    refine ⟨?_, ?_⟩
    · simp only [List.flatMap_cons, List.length_append, ih1, hy, List.length_cons]; ring
    · intro i x hx j hj
      simp only [List.flatMap_cons]
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by omega)]
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        rw [List.getD_append_right _ _ _ _ (by rw [hy, Nat.succ_mul]; omega)]
        rw [← ih2 i x hx j hj]
        congr 1
        rw [hy, Nat.succ_mul]; omega

theorem rl_sum_range_mul (t n : ℕ) (f : ℕ → ZMod 2) :
    ∑ i ∈ Finset.range (t * n), f i =
      ∑ p ∈ Finset.range t, ∑ q ∈ Finset.range n, f (p * n + q) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem rl_tail_getD (a : List Bool) (i : ℕ) : a.tail.getD i false = a.getD (i + 1) false := by
  cases a <;> simp

theorem rl_dotAcc (z : List Bool) : ∀ (acc : Bool) (a : List Bool),
    rl_b2 (dotAcc acc z a) = rl_b2 acc +
      ∑ i ∈ Finset.range z.length, rl_b2 (z.getD i false) * rl_b2 (a.getD i false) := by
  induction z with
  | nil => intro acc a; simp [dotAcc]
  | cons x z ih =>
    intro acc a
    simp only [dotAcc, List.length_cons]
    rw [ih, Finset.sum_range_succ', rl_b2_xor, rl_b2_and]
    simp only [List.getD_cons_succ, List.getD_cons_zero, rl_tail_getD]
    have : a.headD false = a.getD 0 false := by cases a <;> simp
    rw [this]; ring

theorem rl_dots_length (z : List Bool) : ∀ (m : ℕ) (a : List Bool), (dots z m a).length = m := by
  intro m
  induction m with
  | zero => intro a; simp [dots]
  | succ m ih => intro a; simp [dots, ih]

theorem rl_dots_getD (z : List Bool) : ∀ (m : ℕ) (a : List Bool) (e : ℕ), e < m →
    (dots z m a).getD e false = dotAcc false z (a.drop (e * z.length)) := by
  intro m
  induction m with
  | zero => intro a e he; omega
  | succ m ih =>
    intro a e he
    cases e with
    | zero => simp [dots]
    | succ e =>
      simp only [dots, List.getD_cons_succ]
      rw [ih _ e (by omega), List.drop_drop]
      congr 2
      rw [Nat.succ_mul]; omega

theorem rl_getD_getElem {β : Type} (L : List β) (d : β) (i : ℕ) (hi : i < L.length) :
    L.getD i d = L[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem rl_chunk_length (len : ℕ) : ∀ (c : ℕ) (l : List Bool), (chunk len c l).length = c := by
  intro c
  induction c with
  | zero => intro l; simp [chunk]
  | succ c ih => intro l; simp [chunk, ih]

theorem rl_chunk_getD (len : ℕ) : ∀ (c : ℕ) (l : List Bool) (i : ℕ), i < c →
    (chunk len c l).getD i [] = (l.drop (i * len)).take len := by
  intro c
  induction c with
  | zero => intro l i hi; omega
  | succ c ih =>
    intro l i hi
    cases i with
    | zero => simp [chunk]
    | succ i =>
      simp only [chunk, List.getD_cons_succ]
      rw [ih _ i (by omega), List.drop_drop]
      congr 2
      rw [Nat.succ_mul]; omega

theorem rl_chunk_row_length (n t : ℕ) (w : List Bool) (hw : w.length = t * n) (i : ℕ)
    (hi : i < t) : ((chunk n t w).getD i []).length = n := by
  rw [rl_chunk_getD n t w i hi, List.length_take, List.length_drop, hw]
  have : (i + 1) * n ≤ t * n := Nat.mul_le_mul_right n hi
  rw [Nat.succ_mul] at this
  omega

theorem rl_chunk_mem_length (n t : ℕ) (w : List Bool) (hw : w.length = t * n) :
    ∀ v ∈ chunk n t w, v.length = n := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
  have hi' : i < t := by rw [rl_chunk_length] at hi; exact hi
  rw [← rl_getD_getElem _ [] i hi]
  exact rl_chunk_row_length n t w hw i hi'

theorem rl_chunk_toVec (n t : ℕ) (w : List Bool) (i : ℕ) (hi : i < t) (j : Fin n) :
    toVec n ((chunk n t w).getD i []) j = rl_b2 (w.getD (i * n + j.val) false) := by
  show rl_b2 (((chunk n t w).getD i []).getD j.val false) = _
  rw [rl_chunk_getD n t w i hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, j.isLt]

theorem rl_chunk_row_getD (n t : ℕ) (w : List Bool) (i : ℕ) (hi : i < t) (j : ℕ) (hj : j < n) :
    ((chunk n t w).getD i []).getD j false = w.getD (i * n + j) false := by
  rw [rl_chunk_getD n t w i hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hj]

theorem rl_set_range {β γ : Type} (t : ℕ) (L : List β) (hL : L.length = t) (d : β) (F : β → γ) :
    {u | ∃ v ∈ L, F v = u} = Set.range (fun i : Fin t => F (L.getD i.val d)) := by
  subst hL
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
    exact ⟨⟨i, hi⟩, by rw [rl_getD_getElem L d i hi]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨L.getD i.val d, by rw [rl_getD_getElem L d i.val i.isLt]; exact List.getElem_mem _, rfl⟩

theorem rl_set_range2 {β γ δ : Type} (t : ℕ) (L : List β) (hL : L.length = t) (d : β)
    (G : β → β → δ) (F : δ → γ) :
    {u | ∃ v ∈ L.flatMap (fun ci => L.map (fun cj => G ci cj)), F v = u} =
      Set.range (fun ij : Fin t × Fin t => F (G (L.getD ij.1.val d) (L.getD ij.2.val d))) := by
  subst hL
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_range, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨v, ⟨ci, hci, cj, hcj, rfl⟩, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hci
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hcj
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), by
      rw [rl_getD_getElem L d i hi, rl_getD_getElem L d j hj]⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    refine ⟨_, ⟨L.getD i.val d, ?_, L.getD j.val d, ?_, rfl⟩, rfl⟩
    · rw [rl_getD_getElem L d i.val i.isLt]; exact List.getElem_mem _
    · rw [rl_getD_getElem L d j.val j.isLt]; exact List.getElem_mem _

theorem rl_mask (n : ℕ) (ci cj : List Bool) (hi : ci.length = n) (hj : cj.length = n) :
    (mask ci cj).length = n * n ∧ ∀ p q, p < n → q < n →
      (mask ci cj).getD (p * n + q) false =
        Bool.xor (ci.getD p false && cj.getD q false) (cj.getD p false && ci.getD q false) := by
  have hz : (ci.zip cj).length = n := by simp [hi, hj]
  have hzg : ∀ p, p < n → (ci.zip cj)[p]? = some (ci.getD p false, cj.getD p false) := by
    intro p hp
    rw [List.getElem?_zip_eq_some]
    simp [List.getD_eq_getElem?_getD, hi, hj, hp]
  obtain ⟨h1, h2⟩ := rl_flatMap_getD n
    (fun p : Bool × Bool => (ci.zip cj).map fun q => Bool.xor (p.1 && q.2) (p.2 && q.1))
    (ci.zip cj) (by intro x _; simp [hi, hj])
  refine ⟨?_, ?_⟩
  · unfold mask; rw [h1, hz]
  · intro p q hp hq
    unfold mask
    rw [h2 p _ (hzg p hp) q hq]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hzg q hq]

def rl_Q (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (x : Fin n → ZMod 2) (e : Fin m) : ZMod 2 :=
  Finset.univ.sum (fun i => Finset.univ.sum (fun j => if A e i j then x i * x j else 0))

theorem rl_Q_polar (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool) (x y : Fin n → ZMod 2) :
    rl_Q n m A (x + y) - rl_Q n m A x - rl_Q n m A y + rl_Q n m A 0 =
      fun e => ∑ p : Fin n, ∑ q : Fin n, if A e p q then (x p * y q + y p * x q) else 0 := by
  funext e
  simp only [rl_Q, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  split_ifs
  · ring
  · ring

theorem rl_polar (n m : ℕ) (a : List Bool) (A : Fin m → Fin n → Fin n → Bool)
    (hA : ∀ e p q, A e p q = a.getD (e.val * (n * n) + (p.val * n + q.val)) false)
    (ci cj : List Bool) (hi : ci.length = n) (hj : cj.length = n) :
    toVec m (dots (mask ci cj) m a) =
      fun e => ∑ p : Fin n, ∑ q : Fin n,
        if A e p q then (toVec n ci p * toVec n cj q + toVec n cj p * toVec n ci q) else 0 := by
  funext e
  obtain ⟨hm1, hm2⟩ := rl_mask n ci cj hi hj
  show rl_b2 ((dots (mask ci cj) m a).getD e.val false) = _
  rw [rl_dots_getD _ m a e.val e.isLt, rl_dotAcc, hm1, rl_sum_range_mul]
  show (0 : ZMod 2) + _ = _
  rw [zero_add, Finset.sum_range]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [hm2 p.val q.val p.isLt q.isLt, hA e p q, rl_b2_xor, rl_b2_and, rl_b2_and]
  have hd : (List.drop (e.val * (n * n)) a).getD (p.val * n + q.val) false =
      a.getD (e.val * (n * n) + (p.val * n + q.val)) false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [hd]
  show _ = if _ then (rl_b2 _ * rl_b2 _ + rl_b2 _ * rl_b2 _) else 0
  cases a.getD (e.val * (n * n) + (p.val * n + q.val)) false
  · simp [rl_b2]
  · simp [rl_b2]

theorem rl_fin_flatMap (t len : ℕ) (g : Fin t → List Bool) (hg : ∀ i, (g i).length = len) :
    ((List.finRange t).flatMap g).length = t * len ∧ ∀ (i : Fin t) (j : ℕ), j < len →
      ((List.finRange t).flatMap g).getD (i.val * len + j) false = (g i).getD j false := by
  obtain ⟨h1, h2⟩ := rl_flatMap_getD len g (List.finRange t) (fun x _ => hg x)
  exact ⟨by rw [h1, List.length_finRange], fun i j hj => h2 i.val i (by simp) j hj⟩

theorem rl_flat2 (t n : ℕ) (f : Fin t → Fin n → Bool) :
    ((List.finRange t).flatMap (fun i => (List.finRange n).map (fun j => f i j))).length = t * n ∧
    ∀ (i : Fin t) (j : Fin n),
      ((List.finRange t).flatMap (fun i => (List.finRange n).map (fun j => f i j))).getD
        (i.val * n + j.val) false = f i j := by
  obtain ⟨h1, h2⟩ := rl_fin_flatMap t n (fun i => (List.finRange n).map (fun j => f i j))
    (by intro i; simp)
  refine ⟨h1, fun i j => ?_⟩
  rw [h2 i j.val j.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem rl_lt_sq (n p q : ℕ) (hp : p < n) (hq : q < n) : p * n + q < n * n := by
  have : (p + 1) * n ≤ n * n := Nat.mul_le_mul_right n hp
  rw [Nat.succ_mul] at this
  omega

theorem rl_flat3 (m n : ℕ) (A : Fin m → Fin n → Fin n → Bool) :
    ((List.finRange m).flatMap (fun e => (List.finRange n).flatMap
        (fun i => (List.finRange n).map (fun j => A e i j)))).length = m * n * n ∧
    ∀ (e : Fin m) (p q : Fin n),
      ((List.finRange m).flatMap (fun e => (List.finRange n).flatMap
        (fun i => (List.finRange n).map (fun j => A e i j)))).getD
        (e.val * (n * n) + (p.val * n + q.val)) false = A e p q := by
  obtain ⟨h1, h2⟩ := rl_fin_flatMap m (n * n) (fun e => (List.finRange n).flatMap
        (fun i => (List.finRange n).map (fun j => A e i j))) (fun e => (rl_flat2 n n (A e)).1)
  refine ⟨by rw [h1, Nat.mul_assoc], fun e p q => ?_⟩
  rw [h2 e (p.val * n + q.val) (rl_lt_sq n p.val q.val p.isLt q.isLt)]
  exact (rl_flat2 n n (A e)).2 p q

theorem rl_divmod (t n idx : ℕ) (h : idx < t * n) :
    ∃ i j, i < t ∧ j < n ∧ idx = i * n + j := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at h
    · exact h0
  refine ⟨idx / n, idx % n, (Nat.div_lt_iff_lt_mul hn).2 h, Nat.mod_lt _ hn, ?_⟩
  rw [Nat.mul_comm]; exact (Nat.div_add_mod idx n).symm

theorem rl_flat2_ext (t n : ℕ) (f : Fin t → Fin n → Bool) (w : List Bool) (hw : w.length = t * n)
    (h : ∀ i j, f i j = w.getD (i.val * n + j.val) false) :
    (List.finRange t).flatMap (fun i => (List.finRange n).map (fun j => f i j)) = w := by
  obtain ⟨h1, h2⟩ := rl_flat2 t n f
  apply List.ext_getElem (by rw [h1, hw])
  intro idx hi1 hi2
  rw [← rl_getD_getElem _ false idx hi1, ← rl_getD_getElem _ false idx hi2]
  obtain ⟨i, j, hi, hj, rfl⟩ := rl_divmod t n idx (by rw [← hw]; exact hi2)
  rw [h2 ⟨i, hi⟩ ⟨j, hj⟩, h ⟨i, hi⟩ ⟨j, hj⟩]

theorem rl_flat3_ext (m n : ℕ) (A : Fin m → Fin n → Fin n → Bool) (a : List Bool)
    (ha : a.length = m * n * n)
    (h : ∀ e p q, A e p q = a.getD (e.val * (n * n) + (p.val * n + q.val)) false) :
    (List.finRange m).flatMap (fun e => (List.finRange n).flatMap
        (fun i => (List.finRange n).map (fun j => A e i j))) = a := by
  obtain ⟨h1, h2⟩ := rl_flat3 m n A
  apply List.ext_getElem (by rw [h1, ha])
  intro idx hi1 hi2
  rw [← rl_getD_getElem _ false idx hi1, ← rl_getD_getElem _ false idx hi2]
  obtain ⟨e, r, he, hr, rfl⟩ := rl_divmod m (n * n) idx (by rw [← Nat.mul_assoc, ← ha]; exact hi2)
  obtain ⟨p, q, hp, hq, rfl⟩ := rl_divmod n n r hr
  rw [h2 ⟨e, he⟩ ⟨p, hp⟩ ⟨q, hq⟩, h ⟨e, he⟩ ⟨p, hp⟩ ⟨q, hq⟩]

theorem rl_core1 (n t : ℕ) (w : List Bool) (cols : Fin t → Fin n → ZMod 2)
    (hw : w.length = t * n)
    (hcols : ∀ i j, cols i j = rl_b2 (w.getD (i.val * n + j.val) false)) :
    (basisOf (chunk n t w)).length =
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range cols)) := by
  have hc : cols = fun i : Fin t => toVec n ((chunk n t w).getD i.val []) := by
    funext i j
    rw [rl_chunk_toVec n t w i.val i.isLt j, hcols]
  rw [basisOf_rank n _ (rl_chunk_mem_length n t w hw),
    rl_set_range t _ (rl_chunk_length n t w) [] (toVec n), hc]

theorem rl_core2 (n m t : ℕ) (a w : List Bool) (A : Fin m → Fin n → Fin n → Bool)
    (cols : Fin t → Fin n → ZMod 2) (hw : w.length = t * n)
    (hcols : ∀ i j, cols i j = rl_b2 (w.getD (i.val * n + j.val) false))
    (hA : ∀ e p q, A e p q = a.getD (e.val * (n * n) + (p.val * n + q.val)) false) :
    (basisOf ((chunk n t w).flatMap fun ci =>
        (chunk n t w).map fun cj => dots (mask ci cj) m a)).length =
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (fun ij : Fin t × Fin t =>
        rl_Q n m A (cols ij.1 + cols ij.2) - rl_Q n m A (cols ij.1) - rl_Q n m A (cols ij.2) +
          rl_Q n m A 0))) := by
  have hc : cols = fun i : Fin t => toVec n ((chunk n t w).getD i.val []) := by
    funext i j
    rw [rl_chunk_toVec n t w i.val i.isLt j, hcols]
  have hlen : ∀ v ∈ ((chunk n t w).flatMap fun ci =>
      (chunk n t w).map fun cj => dots (mask ci cj) m a), v.length = m := by
    intro v hv
    simp only [List.mem_flatMap, List.mem_map] at hv
    obtain ⟨ci, _, cj, _, rfl⟩ := hv
    exact rl_dots_length _ m a
  have hf : (fun ij : Fin t × Fin t =>
        rl_Q n m A (cols ij.1 + cols ij.2) - rl_Q n m A (cols ij.1) - rl_Q n m A (cols ij.2) +
          rl_Q n m A 0) = fun ij : Fin t × Fin t =>
        toVec m (dots (mask ((chunk n t w).getD ij.1.val [])
          ((chunk n t w).getD ij.2.val [])) m a) := by
    funext ij
    rw [rl_Q_polar, rl_polar n m a A hA _ _ (rl_chunk_row_length n t w hw ij.1.val ij.1.isLt)
      (rl_chunk_row_length n t w hw ij.2.val ij.2.isLt), hc]
  rw [basisOf_rank m _ hlen, rl_set_range2 t _ (rl_chunk_length n t w) []
    (fun ci cj => dots (mask ci cj) m a) (toVec m), hf]

theorem rl_mem_Rel (z : List Bool × List Bool) : z ∈ Rel ↔
    ∃ (n m k d : ℕ) (A : Fin m → Fin n → Fin n → Bool),
      k ≤ m ∧
      List.replicate n true ++ [false] ++ (List.replicate m true ++ [false]) ++
        (List.replicate k true ++ [false]) ++ (List.replicate d true ++ [false]) ++
        (List.finRange m).flatMap (fun e => (List.finRange n).flatMap
          (fun i => (List.finRange n).map (fun j => A e i j))) = z.1 ∧
      ∃ cols : Fin (n + m - (k + d)) → (Fin n → ZMod 2),
        (List.finRange (n + m - (k + d))).flatMap (fun i => (List.finRange n).map
          (fun j => decide (cols i j = 1))) = z.2 ∧
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range cols)) = n + m - (k + d) ∧
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          (Set.range (fun ij : Fin (n + m - (k + d)) × Fin (n + m - (k + d)) =>
            rl_Q n m A (cols ij.1 + cols ij.2) - rl_Q n m A (cols ij.1) -
              rl_Q n m A (cols ij.2) + rl_Q n m A 0))) ≤ k :=
  Iff.rfl

theorem verifyFn_iff (z : List Bool × List Bool) : verifyFn z = true ↔ z ∈ Rel := by
  rw [rl_mem_Rel]
  obtain ⟨x, w⟩ := z
  constructor
  · intro h
    unfold verifyFn at h
    cases hp : parse x with
    | none =>
      simp only [hp] at h
      exact absurd h (by simp)
    | some q =>
      obtain ⟨n, m, k, d, a⟩ := q
      simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hkm, ha⟩, hw⟩, h1⟩, h2⟩ := h
      rw [rl_parse_iff] at hp
      refine ⟨n, m, k, d, fun e p q => a.getD (e.val * (n * n) + (p.val * n + q.val)) false, hkm,
        ?_, fun i j => rl_b2 (w.getD (i.val * n + j.val) false), ?_, ?_, ?_⟩
      · rw [hp, rl_flat3_ext m n _ a ha (fun _ _ _ => rfl)]
      · exact rl_flat2_ext _ n _ w hw (fun i j => rl_decide_b2 _)
      · have c1 := rl_core1 n _ w (fun i j => rl_b2 (w.getD (i.val * n + j.val) false)) hw
          (fun _ _ => rfl)
        rw [← c1]
        refine le_antisymm ?_ h1
        rw [c1]
        have := finrank_range_le_card (R := ZMod 2)
          (fun (i : Fin (n + m - (k + d))) (j : Fin n) => rl_b2 (w.getD (i.val * n + j.val) false))
        rw [Fintype.card_fin] at this
        exact this
      · rw [← rl_core2 n m _ a w _ _ hw (fun _ _ => rfl) (fun _ _ _ => rfl)]
        exact h2
  · rintro ⟨n, m, k, d, A, hkm, hpack, cols, hw, hr1, hr2⟩
    simp only at hpack hw
    obtain ⟨ha1, ha2⟩ := rl_flat3 m n A
    obtain ⟨hw1, hw2⟩ := rl_flat2 (n + m - (k + d)) n (fun i j => decide (cols i j = 1))
    rw [hw] at hw1 hw2
    have hp := (rl_parse_iff x n m k d _).2 hpack.symm
    have c1 := rl_core1 n _ w cols hw1 (fun i j => by rw [hw2, rl_b2_decide])
    have c2 := rl_core2 n m _ _ w A cols hw1 (fun i j => by rw [hw2, rl_b2_decide])
      (fun e p q => (ha2 e p q).symm)
    unfold verifyFn
    simp only [hp, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨hkm, ha1⟩, hw1⟩, by rw [c1, hr1]⟩, by rw [c2]; exact hr2⟩

theorem rel_len (x w : List Bool) (h : (x, w) ∈ Rel) : w.length ≤ x.length ^ 2 := by
  rw [rl_mem_Rel] at h
  obtain ⟨n, m, k, d, A, hkm, hpack, cols, hw, hr1, hr2⟩ := h
  simp only at hpack hw
  have hw1 := (rl_flat2 (n + m - (k + d)) n (fun i j => decide (cols i j = 1))).1
  rw [hw] at hw1
  have ht : n + m - (k + d) ≤ n := by
    have := Submodule.finrank_le (Submodule.span (ZMod 2) (Set.range cols))
    rw [hr1] at this
    simpa using this
  have hx : n + 1 ≤ x.length := by
    rw [← hpack]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  rw [hw1]
  calc (n + m - (k + d)) * n ≤ n * n := Nat.mul_le_mul_right n ht
    _ ≤ x.length * x.length := Nat.mul_le_mul (by omega) (by omega)
    _ = x.length ^ 2 := (sq _).symm

end

section
open Turing

section generic

variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}

inductive Prog (K : Type) (Γ : K → Type) (σ : Type) : Type
  | push (k : K) (f : σ → Γ k) : Prog K Γ σ
  | pop (k : K) (f : σ → Option (Γ k) → σ) : Prog K Γ σ
  | load (f : σ → σ) : Prog K Γ σ
  | seq (p q : Prog K Γ σ) : Prog K Γ σ
  | ite (c : σ → Bool) (p q : Prog K Γ σ) : Prog K Γ σ
  | loop (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (b : Prog K Γ σ) : Prog K Γ σ

structure St (K : Type) (Γ : K → Type) (σ : Type) where
  var : σ
  stk : ∀ k, List (Γ k)

def loopExec (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (body : St K Γ σ → St K Γ σ) :
    List (Γ k) → St K Γ σ → St K Γ σ
  | [], s => ⟨f s.var none, Function.update s.stk k []⟩
  | x :: l, s =>
    if c (f s.var (some x)) then
      loopExec k f c body l (body ⟨f s.var (some x), Function.update s.stk k l⟩)
    else ⟨f s.var (some x), Function.update s.stk k l⟩

def exec : Prog K Γ σ → St K Γ σ → St K Γ σ
  | .push k f, s => ⟨s.var, Function.update s.stk k (f s.var :: s.stk k)⟩
  | .pop k f, s => ⟨f s.var (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | .load f, s => ⟨f s.var, s.stk⟩
  | .seq p q, s => exec q (exec p s)
  | .ite c p q, s => if c s.var then exec p s else exec q s
  | .loop k f c b, s => loopExec k f c (exec b) (s.stk k) s

def loopCost (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (body : St K Γ σ → St K Γ σ)
    (bc : St K Γ σ → ℕ) : List (Γ k) → St K Γ σ → ℕ
  | [], _ => 1
  | x :: l, s =>
    if c (f s.var (some x)) then
      loopCost k f c body bc l (body ⟨f s.var (some x), Function.update s.stk k l⟩) +
        (bc ⟨f s.var (some x), Function.update s.stk k l⟩ + 1)
    else 1

def cost : Prog K Γ σ → St K Γ σ → ℕ
  | .push _ _, _ => 1
  | .pop _ _, _ => 1
  | .load _, _ => 1
  | .seq p q, s => cost q (exec p s) + cost p s
  | .ite c p q, s => (if c s.var then cost p s else cost q s) + 1
  | .loop k f c b, s => loopCost k f c (exec b) (cost b) (s.stk k) s

def NoTouch (k : K) : Prog K Γ σ → Prop
  | .push k' _ => k' ≠ k
  | .pop k' _ => k' ≠ k
  | .load _ => True
  | .seq p q => NoTouch k p ∧ NoTouch k q
  | .ite _ p q => NoTouch k p ∧ NoTouch k q
  | .loop k' _ _ b => k' ≠ k ∧ NoTouch k b

def WF : Prog K Γ σ → Prop
  | .push _ _ => True
  | .pop _ _ => True
  | .load _ => True
  | .seq p q => WF p ∧ WF q
  | .ite _ p q => WF p ∧ WF q
  | .loop k f c b => (∀ v, c (f v none) = false) ∧ NoTouch k b ∧ WF b

def Pos : Prog K Γ σ → Type
  | .push _ _ => Unit
  | .pop _ _ => Unit
  | .load _ => Unit
  | .seq p q => Pos p ⊕ Pos q
  | .ite _ p q => Option (Pos p ⊕ Pos q)
  | .loop _ _ _ b => Option (Pos b)

def entry : (p : Prog K Γ σ) → Pos p
  | .push _ _ => ()
  | .pop _ _ => ()
  | .load _ => ()
  | .seq p _ => Sum.inl (entry p)
  | .ite _ _ _ => none
  | .loop _ _ _ _ => none

instance posFintype : (p : Prog K Γ σ) → Fintype (Pos p)
  | .push _ _ => inferInstanceAs (Fintype Unit)
  | .pop _ _ => inferInstanceAs (Fintype Unit)
  | .load _ => inferInstanceAs (Fintype Unit)
  | .seq p q => @instFintypeSum _ _ (posFintype p) (posFintype q)
  | .ite _ p q => @instFintypeOption _ (@instFintypeSum _ _ (posFintype p) (posFintype q))
  | .loop _ _ _ b => @instFintypeOption _ (posFintype b)

def stmt {Λ : Type} : (p : Prog K Γ σ) → (Pos p → Λ) → Λ → Pos p → TM2.Stmt Γ Λ σ
  | .push k f, _, cont, _ => .push k f (.goto fun _ => cont)
  | .pop k f, _, cont, _ => .pop k f (.goto fun _ => cont)
  | .load f, _, cont, _ => .load f (.goto fun _ => cont)
  | .seq p q, inj, cont, a =>
    match a with
    | Sum.inl a => stmt p (fun x => inj (Sum.inl x)) (inj (Sum.inr (entry q))) a
    | Sum.inr b => stmt q (fun x => inj (Sum.inr x)) cont b
  | .ite c p q, inj, cont, a =>
    match a with
    | none => .branch c (.goto fun _ => inj (some (Sum.inl (entry p))))
        (.goto fun _ => inj (some (Sum.inr (entry q))))
    | some (Sum.inl a) => stmt p (fun x => inj (some (Sum.inl x))) cont a
    | some (Sum.inr b) => stmt q (fun x => inj (some (Sum.inr x))) cont b
  | .loop k f c b, inj, cont, a =>
    match a with
    | none => .pop k f (.branch c (.goto fun _ => inj (some (entry b))) (.goto fun _ => cont))
    | some a => stmt b (fun x => inj (some x)) (inj none) a

theorem noTouch_exec (k : K) (p : Prog K Γ σ) (h : NoTouch k p) (s : St K Γ σ) :
    (exec p s).stk k = s.stk k := by
  induction p generalizing s with
  | push k' f => simp only [exec]; exact Function.update_of_ne (Ne.symm h) _ _
  | pop k' f => simp only [exec]; exact Function.update_of_ne (Ne.symm h) _ _
  | load f => rfl
  | seq p q ihp ihq => simp only [exec]; rw [ihq h.2, ihp h.1]
  | ite c p q ihp ihq =>
    simp only [exec]
    split
    · exact ihp h.1 s
    · exact ihq h.2 s
  | loop k' f c b ih =>
    simp only [exec]
    generalize s.stk k' = l
    induction l generalizing s with
    | nil => simp only [loopExec]; exact Function.update_of_ne (Ne.symm h.1) _ _
    | cons x l ihl =>
      simp only [loopExec]
      split
      · rw [ihl, ih h.2]; exact Function.update_of_ne (Ne.symm h.1) _ _
      · exact Function.update_of_ne (Ne.symm h.1) _ _

theorem exec_loop_nil (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (b : Prog K Γ σ)
    (s : St K Γ σ) (h : s.stk k = []) :
    exec (Prog.loop k f c b) s = ⟨f s.var none, Function.update s.stk k []⟩ := by
  simp only [exec, h, loopExec]

theorem cost_loop_nil (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (b : Prog K Γ σ)
    (s : St K Γ σ) (h : s.stk k = []) :
    cost (Prog.loop k f c b) s = 1 := by
  simp only [cost, h, loopCost]

theorem exec_loop_cons (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (b : Prog K Γ σ)
    (s : St K Γ σ) (x : Γ k) (l : List (Γ k)) (h : s.stk k = x :: l)
    (hc : c (f s.var (some x)) = true) (hnt : NoTouch k b) :
    exec (Prog.loop k f c b) s =
      exec (Prog.loop k f c b) (exec b ⟨f s.var (some x), Function.update s.stk k l⟩) := by
  have hk : (exec b ⟨f s.var (some x), Function.update s.stk k l⟩).stk k = l := by
    rw [noTouch_exec k b hnt]; simp
  conv_lhs => simp only [exec, h, loopExec, hc, ite_true]
  simp only [exec, hk]

theorem cost_loop_cons (k : K) (f : σ → Option (Γ k) → σ) (c : σ → Bool) (b : Prog K Γ σ)
    (s : St K Γ σ) (x : Γ k) (l : List (Γ k)) (h : s.stk k = x :: l)
    (hc : c (f s.var (some x)) = true) (hnt : NoTouch k b) :
    cost (Prog.loop k f c b) s =
      cost (Prog.loop k f c b) (exec b ⟨f s.var (some x), Function.update s.stk k l⟩) +
        (cost b ⟨f s.var (some x), Function.update s.stk k l⟩ + 1) := by
  have hk : (exec b ⟨f s.var (some x), Function.update s.stk k l⟩).stk k = l := by
    rw [noTouch_exec k b hnt]; simp
  conv_lhs => simp only [cost, h, loopCost, hc, ite_true]
  simp only [cost, hk]

theorem iter_add {α : Type} (f : α → Option α) (m n : ℕ) (a b : α) (c : Option α)
    (h1 : (flip bind f)^[n] (some a) = some b) (h2 : (flip bind f)^[m] (some b) = c) :
    (flip bind f)^[m + n] (some a) = c := by
  rw [Function.iterate_add_apply, h1, h2]

theorem one_step {Λ : Type} (M : Λ → TM2.Stmt Γ Λ σ) (l : Λ) (v : σ) (S : ∀ k, List (Γ k))
    (q : TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) (hq : M l = q) (hc : TM2.stepAux q v S = c) :
    (flip bind (TM2.step M))^[1] (some ⟨some l, v, S⟩) = some c := by
  subst hq hc; rfl

theorem compile_correct {Λ : Type} (M : Λ → TM2.Stmt Γ Λ σ) (p : Prog K Γ σ) (hwf : WF p) :
    ∀ (inj : Pos p → Λ) (cont : Λ), (∀ a, M (inj a) = stmt p inj cont a) → ∀ s : St K Γ σ,
    (flip bind (TM2.step M))^[cost p s] (some ⟨some (inj (entry p)), s.var, s.stk⟩) =
      some ⟨some cont, (exec p s).var, (exec p s).stk⟩ := by
  induction p with
  | push k f =>
    intro inj cont hM s
    exact one_step M _ _ _ _ _ (hM ()) rfl
  | pop k f =>
    intro inj cont hM s
    exact one_step M _ _ _ _ _ (hM ()) rfl
  | load f =>
    intro inj cont hM s
    exact one_step M _ _ _ _ _ (hM ()) rfl
  | seq p q ihp ihq =>
    intro inj cont hM s
    have h1 := ihp hwf.1 (fun x => inj (Sum.inl x)) (inj (Sum.inr (entry q)))
      (fun a => hM (Sum.inl a)) s
    have h2 := ihq hwf.2 (fun x => inj (Sum.inr x)) cont (fun a => hM (Sum.inr a)) (exec p s)
    exact iter_add _ _ _ _ _ _ h1 h2
  | ite c p q ihp ihq =>
    intro inj cont hM s
    have h0 := hM none
    by_cases hc : c s.var = true
    · have e1 : cost (Prog.ite c p q) s = cost p s + 1 := by simp [cost, hc]
      have e2 : exec (Prog.ite c p q) s = exec p s := by simp [exec, hc]
      rw [e1, e2]
      refine iter_add _ _ 1 _ _ _ ?_
        (ihp hwf.1 (fun x => inj (some (Sum.inl x))) cont (fun a => hM (some (Sum.inl a))) s)
      refine one_step M _ _ _ _ _ h0 ?_
      simp [stmt, TM2.stepAux, hc]
    · have e1 : cost (Prog.ite c p q) s = cost q s + 1 := by simp [cost, hc]
      have e2 : exec (Prog.ite c p q) s = exec q s := by simp [exec, hc]
      rw [e1, e2]
      refine iter_add _ _ 1 _ _ _ ?_
        (ihq hwf.2 (fun x => inj (some (Sum.inr x))) cont (fun a => hM (some (Sum.inr a))) s)
      refine one_step M _ _ _ _ _ h0 ?_
      simp [stmt, TM2.stepAux, hc]
  | loop k f c b ih =>
    intro inj cont hM s
    have h0 := hM none
    have key : ∀ (l : List (Γ k)) (s : St K Γ σ), s.stk k = l →
        (flip bind (TM2.step M))^[loopCost k f c (exec b) (cost b) l s]
          (some ⟨some (inj none), s.var, s.stk⟩) =
        some ⟨some cont, (loopExec k f c (exec b) l s).var,
          (loopExec k f c (exec b) l s).stk⟩ := by
      intro l
      induction l with
      | nil =>
        intro s hl
        refine one_step M _ _ _ _ _ h0 ?_
        simp [stmt, TM2.stepAux, hl, hwf.1, loopExec]
      | cons x l ihl =>
        intro s hl
        by_cases hc : c (f s.var (some x)) = true
        · have e1 : loopCost k f c (exec b) (cost b) (x :: l) s =
              loopCost k f c (exec b) (cost b) l
                (exec b ⟨f s.var (some x), Function.update s.stk k l⟩) +
              (cost b ⟨f s.var (some x), Function.update s.stk k l⟩ + 1) := by
            simp [loopCost, hc]
          have e2 : loopExec k f c (exec b) (x :: l) s =
              loopExec k f c (exec b) l
                (exec b ⟨f s.var (some x), Function.update s.stk k l⟩) := by
            simp [loopExec, hc]
          rw [e1, e2]
          have hb := ih hwf.2.2 (fun x => inj (some x)) (inj none) (fun a => hM (some a))
            ⟨f s.var (some x), Function.update s.stk k l⟩
          have hk : (exec b ⟨f s.var (some x), Function.update s.stk k l⟩).stk k = l := by
            rw [noTouch_exec k b hwf.2.1]; simp
          have hrest := ihl (exec b ⟨f s.var (some x), Function.update s.stk k l⟩) hk
          refine iter_add _ _ _ _ _ _ (iter_add _ _ 1 _ _ _ ?_ hb) hrest
          refine one_step M _ _ _ _ _ h0 ?_
          simp [stmt, TM2.stepAux, hl, hc]
        · have e1 : loopCost k f c (exec b) (cost b) (x :: l) s = 1 := by
            simp [loopCost, hc]
          have e2 : loopExec k f c (exec b) (x :: l) s =
              ⟨f s.var (some x), Function.update s.stk k l⟩ := by
            simp [loopExec, hc]
          rw [e1, e2]
          refine one_step M _ _ _ _ _ h0 ?_
          simp [stmt, TM2.stepAux, hl, hc]
    exact key (s.stk k) s rfl

end generic

end

section
open Turing

inductive W : Type
  | N
  | Nb
  | N2
  | N2b
  | M
  | Mb
  | Kc
  | Kb
  | D
  | T
  | Tb
  | T2
  | T2b
  | P
  | A
  | Ab
  | C2
  | C2b
  | C3
  | CI
  | CIb
  | CI2
  | CI2b
  | CJ
  | CJ2
  | CJ2b
  | Z
  | Zb
  | V
  | Vb
  | B
  | Bb
  | R
  | Rb
  deriving DecidableEq

instance : Fintype W :=
  Fintype.ofList [.N, .Nb, .N2, .N2b, .M, .Mb, .Kc, .Kb, .D, .T, .Tb, .T2, .T2b, .P, .A, .Ab, .C2, .C2b, .C3, .CI, .CIb, .CI2, .CI2b, .CJ, .CJ2, .CJ2b, .Z, .Zb, .V, .Vb, .B, .Bb, .R, .Rb]
    (by intro a; cases a <;> simp)

inductive K : Type
  | inp
  | out
  | w (a : W)
  deriving DecidableEq

noncomputable instance : Fintype K :=
  Fintype.ofInjective (fun k : K => match k with | .inp => (none : Option (Option W)) | .out => some none | .w a => some (some a))
    (by intro a b h; cases a <;> cases b <;> simp_all)

def Γ : K → Type
  | .inp => Bool ⊕ Bool
  | .out => Bool
  | .w _ => Bool

structure Reg where
  go : Bool
  tag : Bool
  x : Bool
  y : Bool
  u : Bool
  w : Bool
  acc : Bool
  m0 : Bool
  m1 : Bool
  ph : Fin 6
  ok : Bool
  res : Bool
  deriving DecidableEq

noncomputable instance : Fintype Reg :=
  Fintype.ofInjective
    (fun r : Reg => (r.go, r.tag, r.x, r.y, r.u, r.w, r.acc, r.m0, r.m1, r.ph, r.ok, r.res))
    (by intro a b h; cases a; cases b; simp_all)

structure Stk where
  inp : List (Bool ⊕ Bool)
  N : List Bool
  Nb : List Bool
  N2 : List Bool
  N2b : List Bool
  M : List Bool
  Mb : List Bool
  Kc : List Bool
  Kb : List Bool
  D : List Bool
  T : List Bool
  Tb : List Bool
  T2 : List Bool
  T2b : List Bool
  P : List Bool
  A : List Bool
  Ab : List Bool
  C2 : List Bool
  C2b : List Bool
  C3 : List Bool
  CI : List Bool
  CIb : List Bool
  CI2 : List Bool
  CI2b : List Bool
  CJ : List Bool
  CJ2 : List Bool
  CJ2b : List Bool
  Z : List Bool
  Zb : List Bool
  V : List Bool
  Vb : List Bool
  B : List Bool
  Bb : List Bool
  R : List Bool
  Rb : List Bool

def Stk.get (s : Stk) : W → List Bool
  | .N => s.N
  | .Nb => s.Nb
  | .N2 => s.N2
  | .N2b => s.N2b
  | .M => s.M
  | .Mb => s.Mb
  | .Kc => s.Kc
  | .Kb => s.Kb
  | .D => s.D
  | .T => s.T
  | .Tb => s.Tb
  | .T2 => s.T2
  | .T2b => s.T2b
  | .P => s.P
  | .A => s.A
  | .Ab => s.Ab
  | .C2 => s.C2
  | .C2b => s.C2b
  | .C3 => s.C3
  | .CI => s.CI
  | .CIb => s.CIb
  | .CI2 => s.CI2
  | .CI2b => s.CI2b
  | .CJ => s.CJ
  | .CJ2 => s.CJ2
  | .CJ2b => s.CJ2b
  | .Z => s.Z
  | .Zb => s.Zb
  | .V => s.V
  | .Vb => s.Vb
  | .B => s.B
  | .Bb => s.Bb
  | .R => s.R
  | .Rb => s.Rb

def Stk.set (s : Stk) : W → List Bool → Stk
  | .N, l => { s with N := l }
  | .Nb, l => { s with Nb := l }
  | .N2, l => { s with N2 := l }
  | .N2b, l => { s with N2b := l }
  | .M, l => { s with M := l }
  | .Mb, l => { s with Mb := l }
  | .Kc, l => { s with Kc := l }
  | .Kb, l => { s with Kb := l }
  | .D, l => { s with D := l }
  | .T, l => { s with T := l }
  | .Tb, l => { s with Tb := l }
  | .T2, l => { s with T2 := l }
  | .T2b, l => { s with T2b := l }
  | .P, l => { s with P := l }
  | .A, l => { s with A := l }
  | .Ab, l => { s with Ab := l }
  | .C2, l => { s with C2 := l }
  | .C2b, l => { s with C2b := l }
  | .C3, l => { s with C3 := l }
  | .CI, l => { s with CI := l }
  | .CIb, l => { s with CIb := l }
  | .CI2, l => { s with CI2 := l }
  | .CI2b, l => { s with CI2b := l }
  | .CJ, l => { s with CJ := l }
  | .CJ2, l => { s with CJ2 := l }
  | .CJ2b, l => { s with CJ2b := l }
  | .Z, l => { s with Z := l }
  | .Zb, l => { s with Zb := l }
  | .V, l => { s with V := l }
  | .Vb, l => { s with Vb := l }
  | .B, l => { s with B := l }
  | .Bb, l => { s with Bb := l }
  | .R, l => { s with R := l }
  | .Rb, l => { s with Rb := l }

def toFun (s : Stk) : ∀ k, List (Γ k)
  | .inp => s.inp
  | .out => []
  | .w a => s.get a

theorem get_set (s : Stk) (a b : W) (l : List Bool) :
    (s.set a l).get b = if b = a then l else s.get b := by
  cases a <;> cases b <;> rfl

theorem get_set_self (s : Stk) (a : W) (l : List Bool) : (s.set a l).get a = l := by
  rw [get_set]; simp

theorem get_set_ne (s : Stk) (a b : W) (l : List Bool) (h : b ≠ a) :
    (s.set a l).get b = s.get b := by
  rw [get_set]; simp [h]

theorem set_inp (s : Stk) (a : W) (l : List Bool) : (s.set a l).inp = s.inp := by
  cases a <;> rfl

theorem Stk.ext_get (s s' : Stk) (hi : s.inp = s'.inp) (h : ∀ a, s.get a = s'.get a) : s = s' := by
  cases s
  cases s'
  simp only [Stk.mk.injEq]
  exact ⟨hi, h .N, h .Nb, h .N2, h .N2b, h .M, h .Mb, h .Kc, h .Kb, h .D, h .T, h .Tb, h .T2, h .T2b, h .P, h .A, h .Ab, h .C2, h .C2b, h .C3, h .CI, h .CIb, h .CI2, h .CI2b, h .CJ, h .CJ2, h .CJ2b, h .Z, h .Zb, h .V, h .Vb, h .B, h .Bb, h .R, h .Rb⟩

theorem set_set (s : Stk) (a : W) (l l' : List Bool) : (s.set a l).set a l' = s.set a l' := by
  apply Stk.ext_get
  · simp only [set_inp]
  · intro b
    simp only [get_set]
    split <;> rfl

theorem set_comm (s : Stk) (a b : W) (l l' : List Bool) (h : a ≠ b) :
    (s.set a l).set b l' = (s.set b l').set a l := by
  apply Stk.ext_get
  · simp only [set_inp]
  · intro c
    simp only [get_set]
    by_cases h1 : c = a
    · have h2 : c ≠ b := fun e => h (h1.symm.trans e)
      simp [h1, h]
    · simp [h1]

theorem set_get_self (s : Stk) (a : W) : s.set a (s.get a) = s := by
  apply Stk.ext_get
  · simp only [set_inp]
  · intro b
    simp only [get_set]
    split
    · next h => rw [h]
    · rfl

theorem toFun_w (s : Stk) (a : W) : toFun s (K.w a) = s.get a := rfl

theorem toFun_inp (s : Stk) : toFun s K.inp = s.inp := rfl

theorem update_toFun (s : Stk) (a : W) (l : List Bool) :
    Function.update (toFun s) (K.w a) l = toFun (s.set a l) := by
  funext k
  cases k with
  | inp => simp [Function.update, toFun, set_inp]; rfl
  | out => simp [Function.update, toFun]
  | w b =>
    by_cases h : b = a
    · subst h; simp [Function.update, toFun, get_set_self]; rfl
    · simp [Function.update, toFun, get_set_ne _ _ _ _ h, h]; rfl

theorem update_toFun_inp (s : Stk) (l : List (Bool ⊕ Bool)) :
    Function.update (toFun s) K.inp l = toFun { s with inp := l } := by
  funext k
  cases k with
  | inp => simp [Function.update, toFun]; rfl
  | out => simp [Function.update, toFun]
  | w b => simp only [Function.update, toFun, reduceCtorEq]; cases b <;> rfl

end

section
open Turing

abbrev Pg := Prog K Γ Reg

def nrm (v : Reg) : Reg :=
  { v with go := false, tag := false, x := false, y := false, u := false, w := false }

def wpush (a : W) (f : Reg → Bool) : Pg := Prog.push (K.w a) f

def wpop (a : W) (f : Reg → Option Bool → Reg) : Pg := Prog.pop (K.w a) f

def popF (f : Reg → Bool → Reg) (g : Reg → Reg) (v : Reg) : Option Bool → Reg
  | some b => { f v b with go := true }
  | none => nrm (g v)

def forPop (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) : Pg :=
  Prog.loop (K.w a) (popF f g) (fun v => v.go) body

def move (a b : W) : Pg :=
  forPop a (fun v c => { v with u := c }) id (wpush b (fun v => v.u))

def drain (a : W) : Pg := forPop a (fun v _ => v) id (Prog.load id)

def forC (c cb : W) (body : Pg) : Pg :=
  Prog.seq (forPop c (fun v _ => v) id (Prog.seq (wpush cb (fun _ => true)) body)) (move cb c)

theorem exec_wpush (a : W) (f : Reg → Bool) (v : Reg) (s : Stk) :
    exec (wpush a f) ⟨v, toFun s⟩ = ⟨v, toFun (s.set a (f v :: s.get a))⟩ :=
  congrArg (St.mk v) (update_toFun s a (f v :: s.get a))

theorem exec_wpop (a : W) (f : Reg → Option Bool → Reg) (v : Reg) (s : Stk) :
    exec (wpop a f) ⟨v, toFun s⟩ = ⟨f v (s.get a).head?, toFun (s.set a (s.get a).tail)⟩ :=
  congrArg (St.mk (f v (s.get a).head?)) (update_toFun s a (s.get a).tail)

theorem exec_load (f : Reg → Reg) (v : Reg) (S : ∀ k, List (Γ k)) :
    exec (Prog.load f : Pg) ⟨v, S⟩ = ⟨f v, S⟩ := rfl

theorem exec_seq (p q : Pg) (s : St K Γ Reg) : exec (Prog.seq p q) s = exec q (exec p s) := rfl

theorem exec_ite (c : Reg → Bool) (p q : Pg) (v : Reg) (S : ∀ k, List (Γ k)) :
    exec (Prog.ite c p q) ⟨v, S⟩ = if c v then exec p ⟨v, S⟩ else exec q ⟨v, S⟩ := rfl

theorem cost_wpush (a : W) (f : Reg → Bool) (s : St K Γ Reg) : cost (wpush a f) s = 1 := rfl

theorem cost_wpop (a : W) (f : Reg → Option Bool → Reg) (s : St K Γ Reg) :
    cost (wpop a f) s = 1 := rfl

theorem cost_load (f : Reg → Reg) (s : St K Γ Reg) : cost (Prog.load f : Pg) s = 1 := rfl

theorem cost_seq (p q : Pg) (s : St K Γ Reg) :
    cost (Prog.seq p q) s = cost q (exec p s) + cost p s := rfl

theorem cost_ite (c : Reg → Bool) (p q : Pg) (v : Reg) (S : ∀ k, List (Γ k)) :
    cost (Prog.ite c p q) ⟨v, S⟩ = (if c v then cost p ⟨v, S⟩ else cost q ⟨v, S⟩) + 1 := rfl

theorem exec_forPop_nil (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) (v : Reg)
    (s : Stk) (h : s.get a = []) :
    exec (forPop a f g body) ⟨v, toFun s⟩ = ⟨nrm (g v), toFun s⟩ := by
  have e := exec_loop_nil (K.w a) (popF f g) (fun v => v.go) body ⟨v, toFun s⟩ h
  refine e.trans (congrArg (St.mk (nrm (g v))) ?_)
  refine (update_toFun s a []).trans ?_
  rw [← h, set_get_self]

theorem cost_forPop_nil (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) (v : Reg)
    (s : Stk) (h : s.get a = []) :
    cost (forPop a f g body) ⟨v, toFun s⟩ = 1 := by
  have e := cost_loop_nil (K.w a) (popF f g) (fun v => v.go) body ⟨v, toFun s⟩ h
  exact e

theorem exec_forPop_cons (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) (v : Reg)
    (s : Stk) (x : Bool) (l : List Bool) (h : s.get a = x :: l) (hnt : NoTouch (K.w a) body) :
    exec (forPop a f g body) ⟨v, toFun s⟩ =
      exec (forPop a f g body) (exec body ⟨{ f v x with go := true }, toFun (s.set a l)⟩) := by
  have e := exec_loop_cons (K.w a) (popF f g) (fun v => v.go) body ⟨v, toFun s⟩ x l h rfl hnt
  refine e.trans ?_
  exact congrArg (fun S => exec (forPop a f g body) (exec body ⟨{ f v x with go := true }, S⟩))
    (update_toFun s a l)

theorem cost_forPop_cons (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) (v : Reg)
    (s : Stk) (x : Bool) (l : List Bool) (h : s.get a = x :: l) (hnt : NoTouch (K.w a) body) :
    cost (forPop a f g body) ⟨v, toFun s⟩ =
      cost (forPop a f g body) (exec body ⟨{ f v x with go := true }, toFun (s.set a l)⟩) +
        (cost body ⟨{ f v x with go := true }, toFun (s.set a l)⟩ + 1) := by
  have e := cost_loop_cons (K.w a) (popF f g) (fun v => v.go) body ⟨v, toFun s⟩ x l h rfl hnt
  refine e.trans ?_
  exact congrArg (fun S => cost (forPop a f g body) (exec body ⟨{ f v x with go := true }, S⟩) +
    (cost body ⟨{ f v x with go := true }, S⟩ + 1)) (update_toFun s a l)

theorem noTouch_wpush (k : K) (a : W) (f : Reg → Bool) : NoTouch k (wpush a f) ↔ K.w a ≠ k :=
  Iff.rfl

theorem noTouch_wpop (k : K) (a : W) (f : Reg → Option Bool → Reg) :
    NoTouch k (wpop a f) ↔ K.w a ≠ k := Iff.rfl

theorem noTouch_load (k : K) (f : Reg → Reg) : NoTouch k (Prog.load f : Pg) ↔ True := Iff.rfl

theorem noTouch_seq (k : K) (p q : Pg) : NoTouch k (Prog.seq p q) ↔ NoTouch k p ∧ NoTouch k q :=
  Iff.rfl

theorem noTouch_ite (k : K) (c : Reg → Bool) (p q : Pg) :
    NoTouch k (Prog.ite c p q) ↔ NoTouch k p ∧ NoTouch k q := Iff.rfl

theorem noTouch_forPop (k : K) (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) :
    NoTouch k (forPop a f g body) ↔ K.w a ≠ k ∧ NoTouch k body := Iff.rfl

theorem noTouch_move (k : K) (a b : W) : NoTouch k (move a b) ↔ K.w a ≠ k ∧ K.w b ≠ k :=
  Iff.rfl

theorem noTouch_drain (k : K) (a : W) : NoTouch k (drain a) ↔ K.w a ≠ k := by
  simp [drain, noTouch_forPop, noTouch_load]

theorem noTouch_forC (k : K) (c cb : W) (body : Pg) :
    NoTouch k (forC c cb body) ↔ (K.w c ≠ k ∧ K.w cb ≠ k ∧ NoTouch k body) ∧ K.w cb ≠ k ∧ K.w c ≠ k :=
  Iff.rfl

theorem St_eq (v v' : Reg) (s s' : Stk) (hv : v = v') (hs : s = s') :
    (⟨v, toFun s⟩ : St K Γ Reg) = ⟨v', toFun s'⟩ := by
  subst hv hs; rfl

theorem move_spec (a b : W) (hab : a ≠ b) (l : List Bool) : ∀ (v : Reg) (s : Stk), s.get a = l →
    exec (move a b) ⟨v, toFun s⟩ =
        ⟨nrm v, toFun ((s.set a []).set b (l.reverse ++ s.get b))⟩ ∧
      cost (move a b) ⟨v, toFun s⟩ = 2 * l.length + 1 := by
  have hnt : NoTouch (K.w a) (wpush b (fun v => v.u)) := by
    rw [noTouch_wpush]; exact fun e => hab (K.w.inj e).symm
  induction l with
  | nil =>
    intro v s h
    refine ⟨?_, ?_⟩
    · rw [move, exec_forPop_nil _ _ _ _ _ _ h]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get
      · simp [set_inp]
      · intro c
        simp only [get_set]
        by_cases h1 : c = b
        · simp [h1]
        · by_cases h2 : c = a
          · simp [h2, h, hab]
          · simp [h1, h2]
    · rw [move, cost_forPop_nil _ _ _ _ _ _ h]; rfl
  | cons x l ih =>
    intro v s h
    have hs : ((s.set a l).set b (x :: (s.set a l).get b)).get a = l := by
      rw [get_set_ne _ _ _ _ hab, get_set_self]
    obtain ⟨e1, e2⟩ := ih { v with u := x, go := true } ((s.set a l).set b (x :: (s.set a l).get b)) hs
    refine ⟨?_, ?_⟩
    · rw [move, exec_forPop_cons _ _ _ _ _ _ x l h hnt, exec_wpush]
      rw [move] at e1
      rw [e1]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get
      · simp [set_inp]
      · intro c
        simp only [get_set]
        by_cases h1 : c = b
        · simp [h1, Ne.symm hab]
        · by_cases h2 : c = a
          · simp [h2, hab]
          · simp [h1, h2]
    · rw [move, cost_forPop_cons _ _ _ _ _ _ x l h hnt, exec_wpush, cost_wpush]
      rw [move] at e2
      rw [e2]
      simp only [List.length_cons]
      ring

theorem drain_spec (a : W) (l : List Bool) : ∀ (v : Reg) (s : Stk), s.get a = l →
    exec (drain a) ⟨v, toFun s⟩ = ⟨nrm v, toFun (s.set a [])⟩ ∧
      cost (drain a) ⟨v, toFun s⟩ = 2 * l.length + 1 := by
  have hnt : NoTouch (K.w a) (Prog.load id : Pg) := trivial
  induction l with
  | nil =>
    intro v s h
    refine ⟨?_, ?_⟩
    · rw [drain, exec_forPop_nil _ _ _ _ _ _ h]
      refine St_eq _ _ _ _ rfl ?_
      rw [← h, set_get_self]
    · rw [drain, cost_forPop_nil _ _ _ _ _ _ h]; rfl
  | cons x l ih =>
    intro v s h
    obtain ⟨e1, e2⟩ := ih { v with go := true } (s.set a l) (get_set_self s a l)
    refine ⟨?_, ?_⟩
    · rw [drain, exec_forPop_cons _ _ _ _ _ _ x l h hnt, exec_load]
      rw [drain] at e1
      refine e1.trans (St_eq _ _ _ _ rfl ?_)
      rw [set_set]
    · rw [drain, cost_forPop_cons _ _ _ _ _ _ x l h hnt, exec_load, cost_load]
      rw [drain] at e2
      exact (congrArg (fun z => z + (1 + 1)) e2).trans (by simp only [List.length_cons]; ring)

def emp : Stk :=
  { inp := [], N := [], Nb := [], N2 := [], N2b := [], M := [], Mb := [], Kc := [], Kb := [], D := [], T := [], Tb := [], T2 := [], T2b := [], P := [], A := [], Ab := [], C2 := [], C2b := [], C3 := [], CI := [], CIb := [], CI2 := [], CI2b := [], CJ := [], CJ2 := [], CJ2b := [], Z := [], Zb := [], V := [], Vb := [], B := [], Bb := [], R := [], Rb := [] }

end

section
open Turing

def tt : Reg → Bool := fun _ => true

def cl (v : Reg) : Reg := nrm { v with acc := false, m0 := false, m1 := false }

def parseBody : Pg :=
  Prog.ite (fun v => v.tag)
    (Prog.seq (Prog.load fun v => { v with ok := v.ok && decide (4 ≤ v.ph.val), ph := 5 })
      (wpush .C2b (fun v => v.x)))
    (Prog.ite (fun v => decide (v.ph = 0))
      (Prog.ite (fun v => v.x) (Prog.seq (wpush .N tt) (Prog.seq (wpush .N2 tt) (wpush .T tt)))
        (Prog.load fun v => { v with ph := 1 }))
      (Prog.ite (fun v => decide (v.ph = 1))
        (Prog.ite (fun v => v.x) (Prog.seq (wpush .M tt) (wpush .T tt))
          (Prog.load fun v => { v with ph := 2 }))
        (Prog.ite (fun v => decide (v.ph = 2))
          (Prog.ite (fun v => v.x) (wpush .Kc tt) (Prog.load fun v => { v with ph := 3 }))
          (Prog.ite (fun v => decide (v.ph = 3))
            (Prog.ite (fun v => v.x) (wpush .D tt) (Prog.load fun v => { v with ph := 4 }))
            (wpush .Ab (fun v => v.x))))))

def inpF (v : Reg) : Option (Bool ⊕ Bool) → Reg
  | some (Sum.inl b) => { v with go := true, tag := false, x := b }
  | some (Sum.inr b) => { v with go := true, tag := true, x := b }
  | none => nrm v

def parseLoop : Pg := Prog.loop K.inp inpF (fun v => v.go) parseBody

def parseP : Pg :=
  Prog.seq parseLoop (Prog.load fun v => { v with ok := v.ok && decide (4 ≤ v.ph.val) })

def subK : Pg :=
  Prog.seq
    (forPop .Kc (fun v _ => v) id
      (Prog.seq (wpush .Kb tt)
        (Prog.seq (wpop .T (fun v _ => v))
          (Prog.seq (wpop .M (fun v o => { v with y := o.isSome }))
            (Prog.seq (Prog.load fun v => { v with ok := v.ok && v.y })
              (Prog.ite (fun v => v.y) (wpush .Mb tt) (Prog.load id)))))))
    (Prog.seq (move .Kb .Kc) (move .Mb .M))

def subD : Pg := forPop .D (fun v _ => v) id (wpop .T (fun v _ => v))

def prodA : Pg := forC .M .Mb (forC .N .Nb (forC .N2 .N2b (wpush .P tt)))

def cmpA : Pg :=
  Prog.seq
    (forPop .Ab (fun v b => { v with x := b }) id
      (Prog.seq (wpush .A (fun v => v.x))
        (Prog.seq (wpop .P (fun v o => { v with y := o.isSome }))
          (Prog.load fun v => { v with ok := v.ok && v.y }))))
    (Prog.seq (wpop .P (fun v o => { v with ok := v.ok && !o.isSome })) (drain .P))

def copyT : Pg := forC .T .Tb (wpush .T2 tt)

def prodW : Pg := forC .T .Tb (forC .N .Nb (wpush .P tt))

def cmpW : Pg :=
  Prog.seq
    (forPop .C2b (fun v b => { v with x := b }) id
      (Prog.seq (wpush .C2 (fun v => v.x))
        (Prog.seq (wpush .C3 (fun v => v.x))
          (Prog.seq (wpop .P (fun v o => { v with y := o.isSome }))
            (Prog.load fun v => { v with ok := v.ok && v.y })))))
    (Prog.seq (wpop .P (fun v o => { v with ok := v.ok && !o.isSome })) (drain .P))

def validP : Pg :=
  Prog.seq subK (Prog.seq subD (Prog.seq prodA (Prog.seq cmpA
    (Prog.seq copyT (Prog.seq prodW cmpW)))))

def scanLoop : Pg :=
  forPop .V (fun v b => { v with x := b }) (fun v => { v with m0 := false, m1 := false })
    (Prog.seq (wpop .B (fun v o => { v with y := o.getD false }))
      (Prog.seq (wpush .Bb (fun v => v.y))
        (Prog.seq
          (wpush .Vb (fun v =>
            if v.m0 then (if v.m1 then Bool.xor v.x v.y else v.x) else (if v.y then false else v.x)))
          (Prog.load fun v =>
            { v with m0 := v.m0 || v.y, m1 := if v.m0 then v.m1 else (if v.y then v.x else v.m1) }))))

def reduceP : Pg :=
  forC .R .Rb
    (Prog.seq (Prog.load fun v => { v with m0 := false, m1 := false })
      (Prog.seq scanLoop (move .Vb .V)))

def nzLoop : Pg :=
  forPop .V (fun v b => { v with x := b }) id
    (Prog.seq (wpush .Vb (fun v => v.x)) (Prog.load fun v => { v with acc := v.acc || v.x }))

def insertP : Pg :=
  Prog.seq reduceP
    (Prog.seq (Prog.load fun v => { v with acc := false })
      (Prog.seq nzLoop
        (Prog.seq
          (Prog.ite (fun v => v.acc) (Prog.seq (move .Vb .B) (wpush .R tt)) (drain .Vb))
          (Prog.seq (move .Bb .B)
            (Prog.load fun v => { v with acc := false, m0 := false, m1 := false })))))

def loadV : Pg :=
  Prog.seq
    (forC .N .Nb
      (Prog.seq (wpop .C2 (fun v o => { v with x := o.getD false }))
        (Prog.seq (wpush .C2b (fun v => v.x)) (wpush .Vb (fun v => v.x)))))
    (move .Vb .V)

def cmpRT : Pg :=
  Prog.seq (Prog.load fun v => { v with acc := false })
    (Prog.seq
      (forC .T .Tb
        (Prog.seq (wpop .R (fun v o => { v with y := o.isSome }))
          (Prog.load fun v => { v with acc := v.acc || !v.y })))
      (Prog.load fun v => { v with res := !v.acc, acc := false }))

def phase2 : Pg :=
  Prog.seq (forC .T .Tb (Prog.seq loadV insertP))
    (Prog.seq (move .C2b .C2) (Prog.seq cmpRT (Prog.seq (drain .R) (drain .B))))

def loadI : Pg :=
  Prog.seq
    (forC .N .Nb
      (Prog.seq (wpop .C3 (fun v o => { v with x := o.getD false })) (wpush .CIb (fun v => v.x))))
    (forPop .CIb (fun v b => { v with x := b }) id
      (Prog.seq (wpush .CI (fun v => v.x)) (wpush .CI2 (fun v => v.x))))

def loadJ : Pg :=
  Prog.seq
    (forC .N .Nb
      (Prog.seq (wpop .C2 (fun v o => { v with x := o.getD false }))
        (Prog.seq (wpush .C2b (fun v => v.x)) (wpush .CJ2b (fun v => v.x)))))
    (forPop .CJ2b (fun v b => { v with x := b }) id
      (Prog.seq (wpush .CJ (fun v => v.x)) (wpush .CJ2 (fun v => v.x))))

def maskRow : Pg :=
  forPop .CI2 (fun v b => { v with u := b }) id
    (Prog.seq (wpush .CI2b (fun v => v.u))
      (Prog.seq (wpop .CJ2 (fun v o => { v with w := o.getD false }))
        (Prog.seq (wpush .CJ2b (fun v => v.w))
          (wpush .Zb (fun v => Bool.xor (v.x && v.w) (v.y && v.u))))))

def maskP : Pg :=
  Prog.seq
    (forPop .CI (fun v b => { v with x := b }) id
      (Prog.seq (wpush .CIb (fun v => v.x))
        (Prog.seq (wpop .CJ (fun v o => { v with y := o.getD false }))
          (Prog.seq maskRow (Prog.seq (move .CI2b .CI2) (move .CJ2b .CJ2))))))
    (Prog.seq (move .CIb .CI) (move .Zb .Z))

def dotLoop : Pg :=
  forPop .Z (fun v b => { v with x := b }) id
    (Prog.seq (wpush .Zb (fun v => v.x))
      (Prog.seq (wpop .A (fun v o => { v with y := o.getD false }))
        (Prog.seq (wpush .Ab (fun v => v.y))
          (Prog.load fun v => { v with acc := Bool.xor v.acc (v.x && v.y) }))))

def dotsP : Pg :=
  Prog.seq
    (forC .M .Mb
      (Prog.seq (Prog.load fun v => { v with acc := false })
        (Prog.seq dotLoop (Prog.seq (move .Zb .Z) (wpush .Vb (fun v => v.acc))))))
    (Prog.seq (Prog.load fun v => { v with acc := false })
      (Prog.seq (move .Ab .A) (move .Vb .V)))

def pairP : Pg :=
  Prog.seq loadJ (Prog.seq maskP (Prog.seq (drain .CJ2) (Prog.seq dotsP
    (Prog.seq (drain .Z) insertP))))

def colP : Pg :=
  Prog.seq loadI (Prog.seq (forC .T2 .T2b pairP)
    (Prog.seq (move .C2b .C2) (Prog.seq (drain .CI) (drain .CI2))))

def cmpRK : Pg :=
  Prog.seq (Prog.load fun v => { v with acc := false })
    (Prog.seq
      (forPop .R (fun v _ => v) id
        (Prog.seq (wpop .Kc (fun v o => { v with y := o.isSome }))
          (Prog.load fun v => { v with acc := v.acc || !v.y })))
      (Prog.load fun v => { v with res := v.res && !v.acc, acc := false }))

def phase3 : Pg := Prog.seq (forC .T .Tb colP) cmpRK

def mainP : Pg := Prog.seq phase2 phase3

def drainAll : Pg :=
  [W.N, .Nb, .N2, .N2b, .M, .Mb, .Kc, .Kb, .D, .T, .Tb, .T2, .T2b, .P, .A, .Ab, .C2, .C2b, .C3,
    .CI, .CIb, .CI2, .CI2b, .CJ, .CJ2, .CJ2b, .Z, .Zb, .V, .Vb, .B, .Bb, .R].foldr
    (fun a p => Prog.seq (drain a) p) (drain .Rb)

def prog : Pg :=
  Prog.seq parseP (Prog.seq validP
    (Prog.seq (Prog.ite (fun v => v.ok) mainP (Prog.load id)) drainAll))

def regInit : Reg :=
  { go := false, tag := false, x := false, y := false, u := false, w := false, acc := false,
    m0 := false, m1 := false, ph := 0, ok := true, res := false }

end

section
open Turing

theorem scanLoop_spec (l : List Bool) : ∀ (v : Reg) (s : Stk), s.V = l → l.length ≤ s.B.length →
    exec scanLoop ⟨v, toFun s⟩ =
        ⟨nrm { v with m0 := false, m1 := false },
          toFun { s with V := [], B := s.B.drop l.length,
                         Bb := (s.B.take l.length).reverse ++ s.Bb,
                         Vb := (scan v.m0 v.m1 l s.B).reverse ++ s.Vb }⟩ ∧
      cost scanLoop ⟨v, toFun s⟩ = 5 * l.length + 1 := by
  have hnt : NoTouch (K.w W.V)
      (Prog.seq (wpop .B (fun v o => { v with y := o.getD false }))
      (Prog.seq (wpush .Bb (fun v => v.y))
        (Prog.seq
          (wpush .Vb (fun v =>
            if v.m0 then (if v.m1 then Bool.xor v.x v.y else v.x) else (if v.y then false else v.x)))
          (Prog.load fun v =>
            { v with m0 := v.m0 || v.y, m1 := if v.m0 then v.m1 else (if v.y then v.x else v.m1) })))) := by
    simp [noTouch_seq, noTouch_wpop, noTouch_wpush, noTouch_load]
  induction l with
  | nil =>
    intro v s hV hB
    refine ⟨?_, ?_⟩
    · rw [scanLoop, exec_forPop_nil .V _ _ _ v s hV]
      refine St_eq _ _ _ _ rfl ?_
      cases s
      simp_all [scan]
    · rw [scanLoop, cost_forPop_nil .V _ _ _ v s hV]; rfl
  | cons x l ih =>
    intro v s hV hB
    obtain ⟨y, b, hb⟩ : ∃ y b, s.B = y :: b := by
      cases h : s.B with
      | nil => rw [h] at hB; simp at hB
      | cons y b => exact ⟨y, b, rfl⟩
    rw [hb] at hB
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hB
    refine ⟨?_, ?_⟩
    · rw [scanLoop, exec_forPop_cons .V _ _ _ v s x l hV hnt]
      simp only [exec_seq, exec_wpop, exec_wpush, exec_load, Stk.get, Stk.set, hb, List.head?_cons,
        List.tail_cons, Option.getD_some]
      rw [← scanLoop, (ih _ _ rfl (by simpa using hB)).1]
      refine St_eq _ _ _ _ rfl ?_
      simp [scan]
    · rw [scanLoop, cost_forPop_cons .V _ _ _ v s x l hV hnt]
      simp only [exec_seq, exec_wpop, exec_wpush, exec_load, cost_seq, cost_wpop, cost_wpush,
        cost_load, Stk.get, Stk.set, hb, List.head?_cons, List.tail_cons, Option.getD_some]
      rw [← scanLoop, (ih _ _ rfl (by simpa using hB)).2]
      simp only [List.length_cons]
      ring

end

section
open Turing

theorem in_scan_app : ∀ (v b r : List Bool) (m0 m1 : Bool), v.length ≤ b.length →
    scan m0 m1 v (b ++ r) = scan m0 m1 v b
  | [], _, _, _, _, _ => by simp [scan]
  | _ :: _, [], _, _, _, h => by simp at h
  | x :: v, y :: b, r, m0, m1, h => by
    simp only [List.cons_append, scan]
    rw [in_scan_app v b r _ _ (by simpa using h)]

theorem in_flatten_len (L : ℕ) : ∀ (Bl : List (List Bool)), (∀ b ∈ Bl, b.length = L) →
    Bl.flatten.length = Bl.length * L
  | [], _ => by simp
  | b :: Bl, h => by
    have h1 : b.length = L := h b (by simp)
    have h2 := in_flatten_len L Bl (fun c hc => h c (by simp [hc]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, h1, h2]
    ring

theorem in_rep (n : ℕ) (l : List Bool) :
    List.replicate n true ++ true :: l = true :: (List.replicate n true ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem in_red1_len (b v : List Bool) : (red1 b v).length = v.length := by
  rw [red1, rk_scan_len]

theorem in_body_spec (b rest : List Bool) (v : Reg) (s : Stk) (hB : s.B = b ++ rest)
    (hl : b.length = s.V.length) (hVb : s.Vb = []) :
    exec (Prog.seq (Prog.load fun v => { v with m0 := false, m1 := false })
        (Prog.seq scanLoop (move .Vb .V))) ⟨v, toFun s⟩ =
        ⟨nrm { v with m0 := false, m1 := false },
          toFun { s with V := red1 b s.V, B := rest, Bb := b.reverse ++ s.Bb }⟩ ∧
      cost (Prog.seq (Prog.load fun v => { v with m0 := false, m1 := false })
        (Prog.seq scanLoop (move .Vb .V))) ⟨v, toFun s⟩ = 7 * s.V.length + 3 := by
  have hle : s.V.length ≤ s.B.length := by rw [hB, List.length_append]; omega
  have h1 := scanLoop_spec s.V { v with m0 := false, m1 := false } s rfl hle
  have hsc : scan false false s.V s.B = red1 b s.V := by
    rw [hB, red1, in_scan_app _ _ _ _ _ (le_of_eq hl.symm)]
  refine ⟨?_, ?_⟩
  · simp only [exec_seq, exec_load]
    rw [h1.1, (move_spec .Vb .V (by decide) _ _ _ rfl).1]
    refine St_eq _ _ _ _ (by simp [nrm]) ?_
    simp only [Stk.set, Stk.get, hVb, hB, ← hl]
    cases s
    simp_all
  · simp only [cost_seq, exec_load, cost_load]
    rw [h1.1, h1.2, (move_spec .Vb .V (by decide) _ _ _ rfl).2]
    simp only [Stk.get, hVb, List.append_nil, List.length_reverse, rk_scan_len]
    ring

def in_rbody : Pg :=
  Prog.seq (Prog.load fun v => { v with m0 := false, m1 := false })
    (Prog.seq scanLoop (move .Vb .V))

def in_rloop : Pg :=
  forPop .R (fun v _ => v) id (Prog.seq (wpush .Rb (fun _ => true)) in_rbody)

theorem in_reduceP_eq : reduceP = Prog.seq in_rloop (move .Rb .R) := rfl

theorem in_rloop_nt : NoTouch (K.w W.R) (Prog.seq (wpush .Rb (fun _ => true)) in_rbody) := by
  simp [in_rbody, scanLoop, noTouch_seq, noTouch_wpop, noTouch_wpush, noTouch_load, noTouch_forPop,
    noTouch_move]

theorem in_rloop_spec : ∀ (Bl : List (List Bool)) (v : Reg) (s : Stk),
    s.B = Bl.flatten → s.R = List.replicate Bl.length true →
    (∀ b ∈ Bl, b.length = s.V.length) → s.Vb = [] →
    exec in_rloop ⟨v, toFun s⟩ =
        ⟨nrm { v with m0 := Bl.isEmpty && v.m0, m1 := Bl.isEmpty && v.m1 },
          toFun { s with V := reduce Bl s.V, B := [], Bb := Bl.flatten.reverse ++ s.Bb, R := [], Rb := List.replicate Bl.length true ++ s.Rb }⟩ ∧
      cost in_rloop ⟨v, toFun s⟩ = Bl.length * (7 * s.V.length + 5) + 1
  | [], v, s, hB, hR, _, _ => by
    refine ⟨?_, ?_⟩
    · rw [in_rloop, exec_forPop_nil .R _ _ _ v s hR]
      refine St_eq _ _ _ _ (by simp) ?_
      cases s
      simp_all [reduce]
    · rw [in_rloop, cost_forPop_nil .R _ _ _ v s hR]; simp
  | b :: Bl, v, s, hB, hR, hlen, hVb => by
    have hl : b.length = s.V.length := hlen b (by simp)
    have hB' : s.B = b ++ Bl.flatten := by rw [hB, List.flatten_cons]
    have hR' : s.get .R = true :: List.replicate Bl.length true := by
      simp only [Stk.get, hR, List.length_cons, List.replicate_succ]
    have hb := in_body_spec b Bl.flatten { v with go := true }
      { s with R := List.replicate Bl.length true, Rb := true :: s.Rb } hB' hl hVb
    have hi := in_rloop_spec Bl (nrm { v with go := true, m0 := false, m1 := false })
      { s with R := List.replicate Bl.length true, Rb := true :: s.Rb, V := red1 b s.V, B := Bl.flatten, Bb := b.reverse ++ s.Bb }
      rfl rfl (fun c hc => by
        show c.length = (red1 b s.V).length
        rw [in_red1_len]; exact hlen c (by simp [hc])) hVb
    refine ⟨?_, ?_⟩
    · rw [in_rloop, exec_forPop_cons .R _ _ _ v s true _ hR' in_rloop_nt]
      simp only [exec_seq, exec_wpush, Stk.get, Stk.set]
      rw [← in_rloop]
      refine (congrArg (exec in_rloop) hb.1).trans ?_
      refine hi.1.trans ?_
      refine St_eq _ _ _ _ (by simp [nrm]) ?_
      simp [reduce, List.replicate_succ, in_rep]
    · rw [in_rloop, cost_forPop_cons .R _ _ _ v s true _ hR' in_rloop_nt]
      simp only [exec_seq, exec_wpush, cost_seq, cost_wpush, Stk.get, Stk.set]
      rw [← in_rloop]
      refine (congrArg₂ (fun a c => cost in_rloop a + (c + 1 + 1)) hb.1 hb.2).trans ?_
      rw [hi.2]
      simp only [in_red1_len, List.length_cons]
      ring

theorem in_reduce_spec (Bl : List (List Bool)) (v : Reg) (s : Stk)
    (hB : s.B = Bl.flatten) (hR : s.R = List.replicate Bl.length true)
    (hlen : ∀ b ∈ Bl, b.length = s.V.length) (hVb : s.Vb = []) (hRb : s.Rb = []) :
    exec reduceP ⟨v, toFun s⟩ =
        ⟨nrm { v with m0 := Bl.isEmpty && v.m0, m1 := Bl.isEmpty && v.m1 },
          toFun { s with V := reduce Bl s.V, B := [], Bb := Bl.flatten.reverse ++ s.Bb }⟩ ∧
      cost reduceP ⟨v, toFun s⟩ = Bl.length * (7 * s.V.length + 7) + 2 := by
  have h1 := in_rloop_spec Bl v s hB hR hlen hVb
  refine ⟨?_, ?_⟩
  · rw [in_reduceP_eq, exec_seq, h1.1, (move_spec .Rb .R (by decide) _ _ _ rfl).1]
    refine St_eq _ _ _ _ (by simp [nrm]) ?_
    simp only [Stk.set, Stk.get, hRb]
    cases s
    simp_all
  · rw [in_reduceP_eq, cost_seq, h1.1, h1.2, (move_spec .Rb .R (by decide) _ _ _ rfl).2]
    simp only [Stk.get, hRb, List.append_nil, List.length_replicate]
    ring

theorem in_nz_spec (l : List Bool) : ∀ (v : Reg) (s : Stk), s.V = l →
    exec nzLoop ⟨v, toFun s⟩ =
        ⟨nrm { v with acc := v.acc || l.any id },
          toFun { s with V := [], Vb := l.reverse ++ s.Vb }⟩ ∧
      cost nzLoop ⟨v, toFun s⟩ = 3 * l.length + 1 := by
  have hnt : NoTouch (K.w W.V)
      (Prog.seq (wpush .Vb (fun v => v.x))
        (Prog.load fun v => { v with acc := v.acc || v.x })) := by
    simp [noTouch_seq, noTouch_wpush, noTouch_load]
  induction l with
  | nil =>
    intro v s hV
    refine ⟨?_, ?_⟩
    · rw [nzLoop, exec_forPop_nil .V _ _ _ v s hV]
      refine St_eq _ _ _ _ (by simp) ?_
      cases s
      simp_all
    · rw [nzLoop, cost_forPop_nil .V _ _ _ v s hV]; rfl
  | cons x l ih =>
    intro v s hV
    refine ⟨?_, ?_⟩
    · rw [nzLoop, exec_forPop_cons .V _ _ _ v s x l hV hnt]
      simp only [exec_seq, exec_wpush, exec_load, Stk.get, Stk.set]
      rw [← nzLoop, (ih _ _ rfl).1]
      refine St_eq _ _ _ _ (by simp [nrm, Bool.or_assoc]) ?_
      simp
    · rw [nzLoop, cost_forPop_cons .V _ _ _ v s x l hV hnt]
      simp only [exec_seq, exec_wpush, exec_load, cost_seq, cost_wpush, cost_load, Stk.get, Stk.set]
      rw [← nzLoop, (ih _ _ rfl).2]
      simp only [List.length_cons]
      ring

def in_tail : Pg :=
  Prog.seq
    (Prog.ite (fun v => v.acc) (Prog.seq (move .Vb .B) (wpush .R tt)) (drain .Vb))
    (Prog.seq (move .Bb .B)
      (Prog.load fun v => { v with acc := false, m0 := false, m1 := false }))

theorem in_tail_t (v : Reg) (s : Stk) (h : v.acc = true) :
    exec in_tail ⟨v, toFun s⟩ =
        ⟨cl v, toFun { s with Vb := [], Bb := [], B := s.Bb.reverse ++ (s.Vb.reverse ++ s.B), R := true :: s.R }⟩ ∧
      cost in_tail ⟨v, toFun s⟩ = 2 * s.Vb.length + 2 * s.Bb.length + 5 := by
  refine ⟨?_, ?_⟩
  · simp only [in_tail, exec_seq, exec_ite, h, ite_true]
    rw [(move_spec .Vb .B (by decide) _ _ _ rfl).1, exec_wpush,
      (move_spec .Bb .B (by decide) _ _ _ rfl).1, exec_load]
    refine St_eq _ _ _ _ (by simp [cl, nrm]) ?_
    simp [Stk.set, Stk.get, tt]
  · simp only [in_tail, exec_seq, exec_ite, cost_seq, cost_ite, cost_load, cost_wpush, h, ite_true]
    rw [(move_spec .Vb .B (by decide) _ _ _ rfl).1, (move_spec .Vb .B (by decide) _ _ _ rfl).2,
      exec_wpush, (move_spec .Bb .B (by decide) _ _ _ rfl).2]
    simp only [Stk.set, Stk.get]
    ring

theorem in_tail_f (v : Reg) (s : Stk) (h : v.acc = false) :
    exec in_tail ⟨v, toFun s⟩ =
        ⟨cl v, toFun { s with Vb := [], Bb := [], B := s.Bb.reverse ++ s.B }⟩ ∧
      cost in_tail ⟨v, toFun s⟩ = 2 * s.Vb.length + 2 * s.Bb.length + 4 := by
  refine ⟨?_, ?_⟩
  · simp only [in_tail, exec_seq, exec_ite, h, Bool.false_eq_true, ite_false]
    rw [(drain_spec .Vb _ _ _ rfl).1, (move_spec .Bb .B (by decide) _ _ _ rfl).1, exec_load]
    refine St_eq _ _ _ _ (by simp [cl, nrm]) ?_
    simp [Stk.set, Stk.get]
  · simp only [in_tail, exec_seq, exec_ite, cost_seq, cost_ite, cost_load, h, Bool.false_eq_true,
      ite_false]
    rw [(drain_spec .Vb _ _ _ rfl).1, (drain_spec .Vb _ _ _ rfl).2,
      (move_spec .Bb .B (by decide) _ _ _ rfl).2]
    simp only [Stk.set, Stk.get]
    ring

theorem in_insertP_eq : insertP =
    Prog.seq reduceP (Prog.seq (Prog.load fun v => { v with acc := false })
      (Prog.seq nzLoop in_tail)) := rfl

theorem in_arith (r L : ℕ) :
    2 * L + 2 * (r * L) + 5 + (3 * L + 1) + 1 + (r * (7 * L + 7) + 2) ≤ 16 * (r + 1) * (L + 1) := by
  nlinarith [Nat.zero_le (r * L), Nat.zero_le r, Nat.zero_le L]

theorem insert_spec (Bl : List (List Bool)) (v : Reg) (s : Stk)
    (hB : s.B = Bl.flatten) (hR : s.R = List.replicate Bl.length true)
    (hlen : ∀ b ∈ Bl, b.length = s.V.length)
    (hRb : s.Rb = []) (hBb : s.Bb = []) (hVb : s.Vb = []) :
    exec insertP ⟨v, toFun s⟩ =
        ⟨cl v, toFun { s with V := [], B := (ins Bl s.V).flatten,
                                        R := List.replicate (ins Bl s.V).length true }⟩ ∧
      cost insertP ⟨v, toFun s⟩ ≤ 16 * (Bl.length + 1) * (s.V.length + 1) := by
  have h1 := in_reduce_spec Bl v s hB hR hlen hVb hRb
  have hfl : Bl.flatten.length = Bl.length * s.V.length := in_flatten_len _ Bl hlen
  by_cases hany : (reduce Bl s.V).any id = true
  · refine ⟨?_, ?_⟩
    · rw [in_insertP_eq, exec_seq, h1.1, exec_seq, exec_load, exec_seq,
        (in_nz_spec _ _ _ rfl).1, (in_tail_t _ _ (by simp [nrm, hany])).1]
      refine St_eq _ _ _ _ (by simp [cl, nrm]) ?_
      cases s
      simp_all [ins, List.replicate_succ]
    · rw [in_insertP_eq, cost_seq, h1.1, h1.2, cost_seq, exec_load, cost_load, cost_seq,
        (in_nz_spec _ _ _ rfl).1, (in_nz_spec _ _ _ rfl).2, (in_tail_t _ _ (by simp [nrm, hany])).2]
      simp only [List.length_reverse, List.length_append, rk_reduce_len, hfl, hBb, hVb,
        List.length_nil, Nat.add_zero]
      exact in_arith _ _
  · have hany' : (reduce Bl s.V).any id = false := by simpa using hany
    refine ⟨?_, ?_⟩
    · rw [in_insertP_eq, exec_seq, h1.1, exec_seq, exec_load, exec_seq,
        (in_nz_spec _ _ _ rfl).1, (in_tail_f _ _ (by simp [nrm, hany'])).1]
      refine St_eq _ _ _ _ (by simp [cl, nrm]) ?_
      cases s
      simp_all [ins]
    · rw [in_insertP_eq, cost_seq, h1.1, h1.2, cost_seq, exec_load, cost_load, cost_seq,
        (in_nz_spec _ _ _ rfl).1, (in_nz_spec _ _ _ rfl).2, (in_tail_f _ _ (by simp [nrm, hany'])).2]
      simp only [List.length_reverse, List.length_append, rk_reduce_len, hfl, hBb, hVb,
        List.length_nil, Nat.add_zero]
      have := in_arith Bl.length s.V.length
      omega

end

section
open Turing

theorem mk_rep (n : ℕ) (l : List Bool) :
    List.replicate n true ++ true :: l = true :: (List.replicate n true ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem mk_cons_of_le (n : ℕ) (l : List Bool) (h : n + 1 ≤ l.length) :
    ∃ y c, l = y :: c ∧ n ≤ c.length := by
  cases l with
  | nil => simp at h
  | cons y c => exact ⟨y, c, rfl, by simpa using h⟩

def mk_lvB : Pg :=
  Prog.seq (wpush .Nb (fun _ => true))
    (Prog.seq (wpop .C2 (fun v o => { v with x := o.getD false }))
      (Prog.seq (wpush .C2b (fun v => v.x)) (wpush .Vb (fun v => v.x))))

def mk_lvL : Pg := forPop .N (fun v _ => v) id mk_lvB

theorem mk_lvL_spec (n : ℕ) : ∀ (v : Reg) (s : Stk), s.N = List.replicate n true →
    n ≤ s.C2.length →
    exec mk_lvL ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with N := [], Nb := List.replicate n true ++ s.Nb, C2 := s.C2.drop n, C2b := (s.C2.take n).reverse ++ s.C2b, Vb := (s.C2.take n).reverse ++ s.Vb }⟩ ∧
      cost mk_lvL ⟨v, toFun s⟩ = 5 * n + 1 := by
  have hnt : NoTouch (K.w W.N) mk_lvB := by
    simp [mk_lvB, noTouch_seq, noTouch_wpop, noTouch_wpush]
  induction n with
  | zero =>
    intro v s hN hC
    simp only [List.replicate_zero] at hN
    refine ⟨?_, ?_⟩
    · rw [mk_lvL, exec_forPop_nil .N _ _ _ v s hN]
      refine St_eq _ _ _ _ rfl ?_
      cases s
      simp_all
    · rw [mk_lvL, cost_forPop_nil .N _ _ _ v s hN]
  | succ n ih =>
    intro v s hN hC
    obtain ⟨y, c, hc, hC'⟩ := mk_cons_of_le n s.C2 hC
    rw [List.replicate_succ] at hN
    refine ⟨?_, ?_⟩
    · rw [mk_lvL, exec_forPop_cons .N _ _ _ v s true _ hN hnt, ← mk_lvL]
      simp only [mk_lvB, exec_seq, exec_wpop, exec_wpush, Stk.get, Stk.set, hc, List.head?_cons,
        List.tail_cons, Option.getD_some]
      rw [(ih _ _ rfl hC').1]
      refine St_eq _ _ _ _ rfl ?_
      simp [mk_rep, List.replicate_succ]
    · rw [mk_lvL, cost_forPop_cons .N _ _ _ v s true _ hN hnt, ← mk_lvL]
      simp only [mk_lvB, exec_seq, exec_wpop, exec_wpush, cost_seq, cost_wpop, cost_wpush,
        Stk.get, Stk.set, hc, List.head?_cons, List.tail_cons, Option.getD_some]
      rw [(ih _ _ rfl hC').2]
      ring

theorem loadV_spec (n : ℕ) (v : Reg) (s : Stk) (hN : s.N = List.replicate n true) (hNb : s.Nb = [])
    (hlen : n ≤ s.C2.length) (hVb : s.Vb = []) (hV : s.V = []) :
    exec loadV ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with C2 := s.C2.drop n, C2b := (s.C2.take n).reverse ++ s.C2b,
                                        V := s.C2.take n }⟩ ∧
      cost loadV ⟨v, toFun s⟩ ≤ 9 * n + 3 := by
  have e : loadV = Prog.seq (Prog.seq mk_lvL (move .Nb .N)) (move .Vb .V) := rfl
  obtain ⟨h1, h1c⟩ := mk_lvL_spec n v s hN hlen
  rw [e]
  simp only [exec_seq, cost_seq, h1, h1c]
  rw [(move_spec .Nb .N (by decide) _ _ _ rfl).2, (move_spec .Nb .N (by decide) _ _ _ rfl).1]
  simp only [Stk.set, Stk.get]
  rw [(move_spec .Vb .V (by decide) _ _ _ rfl).2, (move_spec .Vb .V (by decide) _ _ _ rfl).1]
  simp only [Stk.set, Stk.get]
  refine ⟨?_, ?_⟩
  · refine St_eq _ _ _ _ rfl ?_
    cases s
    simp_all
  · simp [hNb, hVb]
    omega

def mk_liB : Pg :=
  Prog.seq (wpush .Nb (fun _ => true))
    (Prog.seq (wpop .C3 (fun v o => { v with x := o.getD false })) (wpush .CIb (fun v => v.x)))

def mk_liL : Pg := forPop .N (fun v _ => v) id mk_liB

theorem mk_liL_spec (n : ℕ) : ∀ (v : Reg) (s : Stk), s.N = List.replicate n true →
    n ≤ s.C3.length →
    exec mk_liL ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with N := [], Nb := List.replicate n true ++ s.Nb, C3 := s.C3.drop n, CIb := (s.C3.take n).reverse ++ s.CIb }⟩ ∧
      cost mk_liL ⟨v, toFun s⟩ = 4 * n + 1 := by
  have hnt : NoTouch (K.w W.N) mk_liB := by
    simp [mk_liB, noTouch_seq, noTouch_wpop, noTouch_wpush]
  induction n with
  | zero =>
    intro v s hN hC
    simp only [List.replicate_zero] at hN
    refine ⟨?_, ?_⟩
    · rw [mk_liL, exec_forPop_nil .N _ _ _ v s hN]
      refine St_eq _ _ _ _ rfl ?_
      cases s
      simp_all
    · rw [mk_liL, cost_forPop_nil .N _ _ _ v s hN]
  | succ n ih =>
    intro v s hN hC
    obtain ⟨y, c, hc, hC'⟩ := mk_cons_of_le n s.C3 hC
    rw [List.replicate_succ] at hN
    refine ⟨?_, ?_⟩
    · rw [mk_liL, exec_forPop_cons .N _ _ _ v s true _ hN hnt, ← mk_liL]
      simp only [mk_liB, exec_seq, exec_wpop, exec_wpush, Stk.get, Stk.set, hc, List.head?_cons,
        List.tail_cons, Option.getD_some]
      rw [(ih _ _ rfl hC').1]
      refine St_eq _ _ _ _ rfl ?_
      simp [mk_rep, List.replicate_succ]
    · rw [mk_liL, cost_forPop_cons .N _ _ _ v s true _ hN hnt, ← mk_liL]
      simp only [mk_liB, exec_seq, exec_wpop, exec_wpush, cost_seq, cost_wpop, cost_wpush,
        Stk.get, Stk.set, hc, List.head?_cons, List.tail_cons, Option.getD_some]
      rw [(ih _ _ rfl hC').2]
      ring

def mk_liC : Pg :=
  forPop .CIb (fun v b => { v with x := b }) id
    (Prog.seq (wpush .CI (fun v => v.x)) (wpush .CI2 (fun v => v.x)))

theorem mk_liC_spec (l : List Bool) : ∀ (v : Reg) (s : Stk), s.CIb = l →
    exec mk_liC ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with CIb := [], CI := l.reverse ++ s.CI, CI2 := l.reverse ++ s.CI2 }⟩ ∧
      cost mk_liC ⟨v, toFun s⟩ = 3 * l.length + 1 := by
  have hnt : NoTouch (K.w W.CIb)
      (Prog.seq (wpush .CI (fun v => v.x)) (wpush .CI2 (fun v => v.x))) := by
    simp [noTouch_seq, noTouch_wpush]
  induction l with
  | nil =>
    intro v s hl
    refine ⟨?_, ?_⟩
    · rw [mk_liC, exec_forPop_nil .CIb _ _ _ v s hl]
      refine St_eq _ _ _ _ rfl ?_
      cases s
      simp_all
    · rw [mk_liC, cost_forPop_nil .CIb _ _ _ v s hl]; rfl
  | cons x l ih =>
    intro v s hl
    refine ⟨?_, ?_⟩
    · rw [mk_liC, exec_forPop_cons .CIb _ _ _ v s x l hl hnt]
      simp only [exec_seq, exec_wpush, Stk.get, Stk.set]
      rw [← mk_liC, (ih _ _ rfl).1]
      refine St_eq _ _ _ _ rfl ?_
      simp
    · rw [mk_liC, cost_forPop_cons .CIb _ _ _ v s x l hl hnt]
      simp only [exec_seq, exec_wpush, cost_seq, cost_wpush, Stk.get, Stk.set]
      rw [← mk_liC, (ih _ _ rfl).2]
      simp only [List.length_cons]
      ring

theorem loadI_spec (n : ℕ) (v : Reg) (s : Stk) (hN : s.N = List.replicate n true) (hNb : s.Nb = [])
    (hlen : n ≤ s.C3.length) (hCIb : s.CIb = []) (hCI : s.CI = []) (hCI2 : s.CI2 = []) :
    exec loadI ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with C3 := s.C3.drop n, CI := s.C3.take n, CI2 := s.C3.take n }⟩ ∧
      cost loadI ⟨v, toFun s⟩ ≤ 9 * n + 3 := by
  have e : loadI = Prog.seq (Prog.seq mk_liL (move .Nb .N)) mk_liC := rfl
  obtain ⟨h1, h1c⟩ := mk_liL_spec n v s hN hlen
  rw [e]
  simp only [exec_seq, cost_seq, h1, h1c]
  rw [(move_spec .Nb .N (by decide) _ _ _ rfl).2, (move_spec .Nb .N (by decide) _ _ _ rfl).1]
  simp only [Stk.set, Stk.get]
  rw [(mk_liC_spec _ _ _ rfl).2, (mk_liC_spec _ _ _ rfl).1]
  refine ⟨?_, ?_⟩
  · refine St_eq _ _ _ _ rfl ?_
    cases s
    simp_all
  · simp [hNb, hCIb]
    omega

def mk_ljB : Pg :=
  Prog.seq (wpush .Nb (fun _ => true))
    (Prog.seq (wpop .C2 (fun v o => { v with x := o.getD false }))
      (Prog.seq (wpush .C2b (fun v => v.x)) (wpush .CJ2b (fun v => v.x))))

def mk_ljL : Pg := forPop .N (fun v _ => v) id mk_ljB

theorem mk_ljL_spec (n : ℕ) : ∀ (v : Reg) (s : Stk), s.N = List.replicate n true →
    n ≤ s.C2.length →
    exec mk_ljL ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with N := [], Nb := List.replicate n true ++ s.Nb, C2 := s.C2.drop n, C2b := (s.C2.take n).reverse ++ s.C2b, CJ2b := (s.C2.take n).reverse ++ s.CJ2b }⟩ ∧
      cost mk_ljL ⟨v, toFun s⟩ = 5 * n + 1 := by
  have hnt : NoTouch (K.w W.N) mk_ljB := by
    simp [mk_ljB, noTouch_seq, noTouch_wpop, noTouch_wpush]
  induction n with
  | zero =>
    intro v s hN hC
    simp only [List.replicate_zero] at hN
    refine ⟨?_, ?_⟩
    · rw [mk_ljL, exec_forPop_nil .N _ _ _ v s hN]
      refine St_eq _ _ _ _ rfl ?_
      cases s
      simp_all
    · rw [mk_ljL, cost_forPop_nil .N _ _ _ v s hN]
  | succ n ih =>
    intro v s hN hC
    obtain ⟨y, c, hc, hC'⟩ := mk_cons_of_le n s.C2 hC
    rw [List.replicate_succ] at hN
    refine ⟨?_, ?_⟩
    · rw [mk_ljL, exec_forPop_cons .N _ _ _ v s true _ hN hnt, ← mk_ljL]
      simp only [mk_ljB, exec_seq, exec_wpop, exec_wpush, Stk.get, Stk.set, hc, List.head?_cons,
        List.tail_cons, Option.getD_some]
      rw [(ih _ _ rfl hC').1]
      refine St_eq _ _ _ _ rfl ?_
      simp [mk_rep, List.replicate_succ]
    · rw [mk_ljL, cost_forPop_cons .N _ _ _ v s true _ hN hnt, ← mk_ljL]
      simp only [mk_ljB, exec_seq, exec_wpop, exec_wpush, cost_seq, cost_wpop, cost_wpush,
        Stk.get, Stk.set, hc, List.head?_cons, List.tail_cons, Option.getD_some]
      rw [(ih _ _ rfl hC').2]
      ring

def mk_ljC : Pg :=
  forPop .CJ2b (fun v b => { v with x := b }) id
    (Prog.seq (wpush .CJ (fun v => v.x)) (wpush .CJ2 (fun v => v.x)))

theorem mk_ljC_spec (l : List Bool) : ∀ (v : Reg) (s : Stk), s.CJ2b = l →
    exec mk_ljC ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with CJ2b := [], CJ := l.reverse ++ s.CJ, CJ2 := l.reverse ++ s.CJ2 }⟩ ∧
      cost mk_ljC ⟨v, toFun s⟩ = 3 * l.length + 1 := by
  have hnt : NoTouch (K.w W.CJ2b)
      (Prog.seq (wpush .CJ (fun v => v.x)) (wpush .CJ2 (fun v => v.x))) := by
    simp [noTouch_seq, noTouch_wpush]
  induction l with
  | nil =>
    intro v s hl
    refine ⟨?_, ?_⟩
    · rw [mk_ljC, exec_forPop_nil .CJ2b _ _ _ v s hl]
      refine St_eq _ _ _ _ rfl ?_
      cases s
      simp_all
    · rw [mk_ljC, cost_forPop_nil .CJ2b _ _ _ v s hl]; rfl
  | cons x l ih =>
    intro v s hl
    refine ⟨?_, ?_⟩
    · rw [mk_ljC, exec_forPop_cons .CJ2b _ _ _ v s x l hl hnt]
      simp only [exec_seq, exec_wpush, Stk.get, Stk.set]
      rw [← mk_ljC, (ih _ _ rfl).1]
      refine St_eq _ _ _ _ rfl ?_
      simp
    · rw [mk_ljC, cost_forPop_cons .CJ2b _ _ _ v s x l hl hnt]
      simp only [exec_seq, exec_wpush, cost_seq, cost_wpush, Stk.get, Stk.set]
      rw [← mk_ljC, (ih _ _ rfl).2]
      simp only [List.length_cons]
      ring

theorem loadJ_spec (n : ℕ) (v : Reg) (s : Stk) (hN : s.N = List.replicate n true) (hNb : s.Nb = [])
    (hlen : n ≤ s.C2.length) (hCJ2b : s.CJ2b = []) (hCJ : s.CJ = []) (hCJ2 : s.CJ2 = []) :
    exec loadJ ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with C2 := s.C2.drop n, C2b := (s.C2.take n).reverse ++ s.C2b,
                                        CJ := s.C2.take n, CJ2 := s.C2.take n }⟩ ∧
      cost loadJ ⟨v, toFun s⟩ ≤ 10 * n + 3 := by
  have e : loadJ = Prog.seq (Prog.seq mk_ljL (move .Nb .N)) mk_ljC := rfl
  obtain ⟨h1, h1c⟩ := mk_ljL_spec n v s hN hlen
  rw [e]
  simp only [exec_seq, cost_seq, h1, h1c]
  rw [(move_spec .Nb .N (by decide) _ _ _ rfl).2, (move_spec .Nb .N (by decide) _ _ _ rfl).1]
  simp only [Stk.set, Stk.get]
  rw [(mk_ljC_spec _ _ _ rfl).2, (mk_ljC_spec _ _ _ rfl).1]
  refine ⟨?_, ?_⟩
  · refine St_eq _ _ _ _ rfl ?_
    cases s
    simp_all
  · simp [hNb, hCJ2b]
    omega

def mk_rtB : Pg :=
  Prog.seq (wpush .Tb (fun _ => true))
    (Prog.seq (wpop .R (fun v o => { v with y := o.isSome }))
      (Prog.load fun v => { v with acc := v.acc || !v.y }))

def mk_rtL : Pg := forPop .T (fun v _ => v) id mk_rtB

theorem mk_rtL_spec (n : ℕ) : ∀ (v : Reg) (s : Stk), s.T = List.replicate n true →
    exec mk_rtL ⟨v, toFun s⟩ =
        ⟨nrm { v with acc := v.acc || decide (s.R.length < n) }, toFun { s with T := [], Tb := List.replicate n true ++ s.Tb, R := s.R.drop n }⟩ ∧
      cost mk_rtL ⟨v, toFun s⟩ = 4 * n + 1 := by
  have hnt : NoTouch (K.w W.T) mk_rtB := by
    simp [mk_rtB, noTouch_seq, noTouch_wpop, noTouch_wpush, noTouch_load]
  induction n with
  | zero =>
    intro v s hT
    simp only [List.replicate_zero] at hT
    refine ⟨?_, ?_⟩
    · rw [mk_rtL, exec_forPop_nil .T _ _ _ v s hT]
      refine St_eq _ _ _ _ ?_ ?_
      · simp [nrm]
      · cases s
        simp_all
    · rw [mk_rtL, cost_forPop_nil .T _ _ _ v s hT]
  | succ n ih =>
    intro v s hT
    rw [List.replicate_succ] at hT
    refine ⟨?_, ?_⟩
    · rw [mk_rtL, exec_forPop_cons .T _ _ _ v s true _ hT hnt, ← mk_rtL]
      simp only [mk_rtB, exec_seq, exec_wpop, exec_wpush, exec_load, Stk.get, Stk.set]
      rw [(ih _ _ rfl).1]
      refine St_eq _ _ _ _ ?_ ?_
      · cases hR : s.R with
        | nil => simp [nrm]
        | cons y c =>
          simp [nrm]
          rfl
      · cases hR : s.R <;> simp [mk_rep, List.replicate_succ]
    · rw [mk_rtL, cost_forPop_cons .T _ _ _ v s true _ hT hnt, ← mk_rtL]
      simp only [mk_rtB, exec_seq, exec_wpop, exec_wpush, exec_load, cost_seq, cost_wpop,
        cost_wpush, cost_load, Stk.get, Stk.set]
      rw [(ih _ _ rfl).2]
      ring

theorem cmpRT_spec (t : ℕ) (v : Reg) (s : Stk) (hT : s.T = List.replicate t true)
    (hTb : s.Tb = []) :
    exec cmpRT ⟨v, toFun s⟩ =
        ⟨nrm { v with acc := false, res := decide (t ≤ s.R.length) },
          toFun { s with R := s.R.drop t }⟩ ∧
      cost cmpRT ⟨v, toFun s⟩ ≤ 6 * t + 4 := by
  have e : cmpRT = Prog.seq (Prog.load fun v => { v with acc := false })
      (Prog.seq (Prog.seq mk_rtL (move .Tb .T))
        (Prog.load fun v => { v with res := !v.acc, acc := false })) := rfl
  rw [e]
  simp only [exec_seq, cost_seq, exec_load, cost_load]
  rw [(mk_rtL_spec t _ s hT).2, (mk_rtL_spec t _ s hT).1]
  rw [(move_spec .Tb .T (by decide) _ _ _ rfl).2, (move_spec .Tb .T (by decide) _ _ _ rfl).1]
  simp only [Stk.set, Stk.get]
  refine ⟨?_, ?_⟩
  · refine St_eq _ _ _ _ ?_ ?_
    · rcases Nat.lt_or_ge s.R.length t with h | h
      · simp [nrm, h, Nat.not_le.mpr h]
      · simp [nrm, h, Nat.not_lt.mpr h]
    · cases s
      simp_all
  · simp [hTb]
    omega

def mk_rkB : Pg :=
  Prog.seq (wpop .Kc (fun v o => { v with y := o.isSome }))
    (Prog.load fun v => { v with acc := v.acc || !v.y })

def mk_rkL : Pg := forPop .R (fun v _ => v) id mk_rkB

theorem mk_rkL_spec (l : List Bool) : ∀ (v : Reg) (s : Stk), s.R = l →
    exec mk_rkL ⟨v, toFun s⟩ =
        ⟨nrm { v with acc := v.acc || decide (s.Kc.length < l.length) }, toFun { s with R := [], Kc := s.Kc.drop l.length }⟩ ∧
      cost mk_rkL ⟨v, toFun s⟩ = 3 * l.length + 1 := by
  have hnt : NoTouch (K.w W.R) mk_rkB := by
    simp [mk_rkB, noTouch_seq, noTouch_wpop, noTouch_load]
  induction l with
  | nil =>
    intro v s hR
    refine ⟨?_, ?_⟩
    · rw [mk_rkL, exec_forPop_nil .R _ _ _ v s hR]
      refine St_eq _ _ _ _ ?_ ?_
      · simp [nrm]
      · cases s
        simp_all
    · rw [mk_rkL, cost_forPop_nil .R _ _ _ v s hR]; rfl
  | cons x l ih =>
    intro v s hR
    refine ⟨?_, ?_⟩
    · rw [mk_rkL, exec_forPop_cons .R _ _ _ v s x l hR hnt, ← mk_rkL]
      simp only [mk_rkB, exec_seq, exec_wpop, exec_load, Stk.get, Stk.set]
      rw [(ih _ _ rfl).1]
      refine St_eq _ _ _ _ ?_ ?_
      · cases hK : s.Kc with
        | nil => simp [nrm]
        | cons y c =>
          simp [nrm]
          rfl
      · cases hK : s.Kc <;> simp
    · rw [mk_rkL, cost_forPop_cons .R _ _ _ v s x l hR hnt, ← mk_rkL]
      simp only [mk_rkB, exec_seq, exec_wpop, exec_load, cost_seq, cost_wpop, cost_load,
        Stk.get, Stk.set]
      rw [(ih _ _ rfl).2]
      simp only [List.length_cons]
      ring

theorem cmpRK_spec (v : Reg) (s : Stk) :
    exec cmpRK ⟨v, toFun s⟩ =
        ⟨nrm { v with acc := false, res := v.res && decide (s.R.length ≤ s.Kc.length) },
          toFun { s with R := [], Kc := s.Kc.drop s.R.length }⟩ ∧
      cost cmpRK ⟨v, toFun s⟩ ≤ 3 * s.R.length + 3 := by
  have e : cmpRK = Prog.seq (Prog.load fun v => { v with acc := false })
      (Prog.seq mk_rkL
        (Prog.load fun v => { v with res := v.res && !v.acc, acc := false })) := rfl
  rw [e]
  simp only [exec_seq, cost_seq, exec_load, cost_load]
  rw [(mk_rkL_spec s.R _ s rfl).2, (mk_rkL_spec s.R _ s rfl).1]
  refine ⟨?_, ?_⟩
  · refine St_eq _ _ _ _ ?_ rfl
    rcases Nat.lt_or_ge s.Kc.length s.R.length with h | h
    · simp [nrm, h, Nat.not_le.mpr h]
    · simp [nrm, h, Nat.not_lt.mpr h]
  · omega

def mk_mrB : Pg :=
  Prog.seq (wpush .CI2b (fun v => v.u))
    (Prog.seq (wpop .CJ2 (fun v o => { v with w := o.getD false }))
      (Prog.seq (wpush .CJ2b (fun v => v.w))
        (wpush .Zb (fun v => Bool.xor (v.x && v.w) (v.y && v.u)))))

theorem mk_mrow_eq : maskRow = forPop .CI2 (fun v b => { v with u := b }) id mk_mrB := rfl

theorem mk_mrow_spec (l1 : List Bool) : ∀ (l2 : List Bool) (v : Reg) (s : Stk), s.CI2 = l1 →
    s.CJ2 = l2 → l1.length = l2.length →
    exec maskRow ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with CI2 := [], CJ2 := [], CI2b := l1.reverse ++ s.CI2b, CJ2b := l2.reverse ++ s.CJ2b, Zb := ((l1.zip l2).map (fun q => Bool.xor (v.x && q.2) (v.y && q.1))).reverse ++ s.Zb }⟩ ∧
      cost maskRow ⟨v, toFun s⟩ = 5 * l1.length + 1 := by
  have hnt : NoTouch (K.w W.CI2) mk_mrB := by
    simp [mk_mrB, noTouch_seq, noTouch_wpop, noTouch_wpush]
  induction l1 with
  | nil =>
    intro l2 v s h1 h2 hlen
    cases l2 with
    | cons b l2 => simp at hlen
    | nil =>
      refine ⟨?_, ?_⟩
      · rw [mk_mrow_eq, exec_forPop_nil .CI2 _ _ _ v s h1]
        refine St_eq _ _ _ _ rfl ?_
        cases s
        simp_all
      · rw [mk_mrow_eq, cost_forPop_nil .CI2 _ _ _ v s h1]; rfl
  | cons a l ih =>
    intro l2 v s h1 h2 hlen
    cases l2 with
    | nil => simp at hlen
    | cons b l2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [mk_mrow_eq, exec_forPop_cons .CI2 _ _ _ v s a l h1 hnt,
        cost_forPop_cons .CI2 _ _ _ v s a l h1 hnt, ← mk_mrow_eq]
      simp only [mk_mrB, exec_seq, cost_seq, exec_wpop, exec_wpush, cost_wpop, cost_wpush, Stk.get,
        Stk.set, h2, List.head?_cons, List.tail_cons, Option.getD_some]
      rw [(ih _ _ _ rfl rfl hlen).1, (ih _ _ _ rfl rfl hlen).2]
      refine ⟨St_eq _ _ _ _ rfl ?_, ?_⟩
      · simp
      · simp only [List.length_cons]
        ring

def mk_moB : Pg :=
  Prog.seq (wpush .CIb (fun v => v.x))
    (Prog.seq (wpop .CJ (fun v o => { v with y := o.getD false }))
      (Prog.seq maskRow (Prog.seq (move .CI2b .CI2) (move .CJ2b .CJ2))))

def mk_moL : Pg := forPop .CI (fun v b => { v with x := b }) id mk_moB

theorem mk_moL_spec (l1 : List Bool) : ∀ (l2 : List Bool) (v : Reg) (s : Stk), s.CI = l1 →
    s.CJ = l2 → l1.length = l2.length → s.CI2.length = s.CJ2.length → s.CI2b = [] →
    s.CJ2b = [] →
    exec mk_moL ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with CI := [], CJ := [], CIb := l1.reverse ++ s.CIb, Zb := ((l1.zip l2).flatMap (fun p => (s.CI2.zip s.CJ2).map (fun q => Bool.xor (p.1 && q.2) (p.2 && q.1)))).reverse ++ s.Zb }⟩ ∧
      cost mk_moL ⟨v, toFun s⟩ = l1.length * (9 * s.CI2.length + 6) + 1 := by
  have hnt : NoTouch (K.w W.CI) mk_moB := by
    simp [mk_moB, maskRow, noTouch_seq, noTouch_wpop, noTouch_wpush, noTouch_forPop, noTouch_move]
  induction l1 with
  | nil =>
    intro l2 v s h1 h2 hlen hlen2 hb1 hb2
    cases l2 with
    | cons b l2 => simp at hlen
    | nil =>
      refine ⟨?_, ?_⟩
      · rw [mk_moL, exec_forPop_nil .CI _ _ _ v s h1]
        refine St_eq _ _ _ _ rfl ?_
        cases s
        simp_all
      · rw [mk_moL, cost_forPop_nil .CI _ _ _ v s h1]; simp
  | cons a l ih =>
    intro l2 v s h1 h2 hlen hlen2 hb1 hb2
    cases l2 with
    | nil => simp at hlen
    | cons b l2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [mk_moL, exec_forPop_cons .CI _ _ _ v s a l h1 hnt,
        cost_forPop_cons .CI _ _ _ v s a l h1 hnt, ← mk_moL]
      simp only [mk_moB, exec_seq, cost_seq, exec_wpop, exec_wpush, cost_wpop, cost_wpush, Stk.get,
        Stk.set, h2, List.head?_cons, List.tail_cons, Option.getD_some]
      rw [(mk_mrow_spec _ _ _ _ rfl rfl (by exact hlen2)).1,
        (mk_mrow_spec _ _ _ _ rfl rfl (by exact hlen2)).2]
      simp only [Stk.get, Stk.set]
      rw [(move_spec .CI2b .CI2 (by decide) _ _ _ rfl).1,
        (move_spec .CI2b .CI2 (by decide) _ _ _ rfl).2]
      simp only [Stk.get, Stk.set]
      rw [(move_spec .CJ2b .CJ2 (by decide) _ _ _ rfl).1,
        (move_spec .CJ2b .CJ2 (by decide) _ _ _ rfl).2]
      simp only [Stk.get, Stk.set]
      rw [(ih _ _ _ rfl rfl hlen (by simp [hb1, hb2, hlen2]) (by rfl) (by rfl)).1,
        (ih _ _ _ rfl rfl hlen (by simp [hb1, hb2, hlen2]) (by rfl) (by rfl)).2]
      refine ⟨St_eq _ _ _ _ rfl ?_, ?_⟩
      · simp [hb1, hb2]
      · simp only [hb1, hb2, List.length_cons, List.length_reverse,
          List.append_nil, ← hlen2]
        ring

theorem mk_flat_len (k : ℕ) (f : Bool × Bool → List Bool) (hf : ∀ p, (f p).length = k) :
    ∀ l : List (Bool × Bool), (l.flatMap f).length = l.length * k := by
  intro l
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.flatMap_cons, List.length_append, ih, hf, List.length_cons]
    ring

theorem mask_spec (v : Reg) (s : Stk) (hCI2 : s.CI2 = s.CI) (hCJ2 : s.CJ2 = s.CJ)
    (hlen : s.CI.length = s.CJ.length) (hCIb : s.CIb = []) (hCI2b : s.CI2b = [])
    (hCJ2b : s.CJ2b = []) (hZb : s.Zb = []) (hZ : s.Z = []) :
    exec maskP ⟨v, toFun s⟩ = ⟨nrm v, toFun { s with CJ := [], Z := mask s.CI s.CJ }⟩ ∧
      cost maskP ⟨v, toFun s⟩ ≤ 11 * (s.CI.length + 1) ^ 2 := by
  have e : maskP = Prog.seq mk_moL (Prog.seq (move .CIb .CI) (move .Zb .Z)) := rfl
  obtain ⟨h1, h1c⟩ := mk_moL_spec s.CI s.CJ v s rfl rfl hlen (by rw [hCI2, hCJ2, hlen]) hCI2b hCJ2b
  rw [e]
  simp only [exec_seq, cost_seq, h1, h1c]
  rw [(move_spec .CIb .CI (by decide) _ _ _ rfl).2, (move_spec .CIb .CI (by decide) _ _ _ rfl).1]
  simp only [Stk.set, Stk.get]
  rw [(move_spec .Zb .Z (by decide) _ _ _ rfl).2, (move_spec .Zb .Z (by decide) _ _ _ rfl).1]
  simp only [Stk.set, Stk.get]
  refine ⟨?_, ?_⟩
  · refine St_eq _ _ _ _ rfl ?_
    cases s
    simp_all [mask]
  · have hf : ((s.CI.zip s.CJ).flatMap (fun p => (s.CI2.zip s.CJ2).map
        (fun q => Bool.xor (p.1 && q.2) (p.2 && q.1)))).length = s.CI.length * s.CI.length := by
      rw [mk_flat_len s.CI.length _ (by intro p; simp [hCI2, hCJ2, hlen])]
      simp [hlen]
    simp only [hCIb, hZb, List.length_append, List.length_reverse, List.length_nil,
      Nat.add_zero]
    rw [hf, hCI2]
    nlinarith [Nat.zero_le s.CI.length]

def mk_dlB : Pg :=
  Prog.seq (wpush .Zb (fun v => v.x))
    (Prog.seq (wpop .A (fun v o => { v with y := o.getD false }))
      (Prog.seq (wpush .Ab (fun v => v.y))
        (Prog.load fun v => { v with acc := Bool.xor v.acc (v.x && v.y) })))

theorem mk_dl_eq : dotLoop = forPop .Z (fun v b => { v with x := b }) id mk_dlB := rfl

theorem mk_dl_spec (l : List Bool) : ∀ (v : Reg) (s : Stk), s.Z = l → l.length ≤ s.A.length →
    exec dotLoop ⟨v, toFun s⟩ =
        ⟨nrm { v with acc := dotAcc v.acc l s.A }, toFun { s with Z := [], Zb := l.reverse ++ s.Zb, A := s.A.drop l.length, Ab := (s.A.take l.length).reverse ++ s.Ab }⟩ ∧
      cost dotLoop ⟨v, toFun s⟩ = 5 * l.length + 1 := by
  have hnt : NoTouch (K.w W.Z) mk_dlB := by
    simp [mk_dlB, noTouch_seq, noTouch_wpop, noTouch_wpush, noTouch_load]
  induction l with
  | nil =>
    intro v s hZ hA
    refine ⟨?_, ?_⟩
    · rw [mk_dl_eq, exec_forPop_nil .Z _ _ _ v s hZ]
      refine St_eq _ _ _ _ ?_ ?_
      · simp [nrm, dotAcc]
      · cases s
        simp_all
    · rw [mk_dl_eq, cost_forPop_nil .Z _ _ _ v s hZ]; rfl
  | cons x l ih =>
    intro v s hZ hA
    obtain ⟨y, a, ha, hA'⟩ := mk_cons_of_le l.length s.A hA
    rw [mk_dl_eq, exec_forPop_cons .Z _ _ _ v s x l hZ hnt,
      cost_forPop_cons .Z _ _ _ v s x l hZ hnt, ← mk_dl_eq]
    simp only [mk_dlB, exec_seq, cost_seq, exec_wpop, exec_wpush, exec_load, cost_wpop, cost_wpush,
      cost_load, Stk.get, Stk.set, ha, List.head?_cons, List.tail_cons, Option.getD_some]
    rw [(ih _ _ rfl hA').1, (ih _ _ rfl hA').2]
    refine ⟨St_eq _ _ _ _ ?_ ?_, ?_⟩
    · simp [nrm, dotAcc]
    · simp
    · simp only [List.length_cons]
      ring

def mk_lastAcc : Bool → List Bool → ℕ → List Bool → Bool
  | b, _, 0, _ => b
  | _, z, m + 1, a => mk_lastAcc (dotAcc false z a) z m (a.drop z.length)

def mk_dmB : Pg :=
  Prog.seq (wpush .Mb (fun _ => true))
    (Prog.seq (Prog.load fun v => { v with acc := false })
      (Prog.seq dotLoop (Prog.seq (move .Zb .Z) (wpush .Vb (fun v => v.acc)))))

def mk_dmL : Pg := forPop .M (fun v _ => v) id mk_dmB

theorem mk_take_succ (m L : ℕ) (a : List Bool) :
    a.take ((m + 1) * L) = a.take L ++ (a.drop L).take (m * L) := by
  rw [Nat.succ_mul, Nat.add_comm, List.take_add]

theorem mk_drop_succ (m L : ℕ) (a : List Bool) :
    (a.drop L).drop (m * L) = a.drop ((m + 1) * L) := by
  rw [List.drop_drop, Nat.succ_mul]
  congr 1
  omega

theorem mk_dmL_spec (m : ℕ) : ∀ (v : Reg) (s : Stk), s.M = List.replicate m true →
    m * s.Z.length ≤ s.A.length → s.Zb = [] →
    exec mk_dmL ⟨v, toFun s⟩ =
        ⟨nrm { v with acc := mk_lastAcc v.acc s.Z m s.A }, toFun { s with M := [], Mb := List.replicate m true ++ s.Mb, A := s.A.drop (m * s.Z.length), Ab := (s.A.take (m * s.Z.length)).reverse ++ s.Ab, Vb := (dots s.Z m s.A).reverse ++ s.Vb }⟩ ∧
      cost mk_dmL ⟨v, toFun s⟩ = m * (7 * s.Z.length + 6) + 1 := by
  have hnt : NoTouch (K.w W.M) mk_dmB := by
    simp [mk_dmB, dotLoop, noTouch_seq, noTouch_wpop, noTouch_wpush, noTouch_load, noTouch_forPop,
      noTouch_move]
  induction m with
  | zero =>
    intro v s hM hA hZb
    simp only [List.replicate_zero] at hM
    refine ⟨?_, ?_⟩
    · rw [mk_dmL, exec_forPop_nil .M _ _ _ v s hM]
      refine St_eq _ _ _ _ ?_ ?_
      · simp [nrm, mk_lastAcc]
      · cases s
        simp_all [dots]
    · rw [mk_dmL, cost_forPop_nil .M _ _ _ v s hM]; simp
  | succ m ih =>
    intro v s hM hA hZb
    rw [List.replicate_succ] at hM
    have hL : s.Z.length ≤ s.A.length := by
      rw [Nat.succ_mul] at hA
      omega
    have hR : m * s.Z.length ≤ (s.A.drop s.Z.length).length := by
      rw [Nat.succ_mul] at hA
      rw [List.length_drop]
      omega
    rw [mk_dmL, exec_forPop_cons .M _ _ _ v s true _ hM hnt,
      cost_forPop_cons .M _ _ _ v s true _ hM hnt, ← mk_dmL]
    simp only [mk_dmB, exec_seq, cost_seq, exec_wpush, exec_load, cost_wpush, cost_load, Stk.get,
      Stk.set]
    rw [(mk_dl_spec _ _ _ rfl (by exact hL)).1, (mk_dl_spec _ _ _ rfl (by exact hL)).2]
    rw [(move_spec .Zb .Z (by decide) _ _ _ rfl).1, (move_spec .Zb .Z (by decide) _ _ _ rfl).2]
    simp only [exec_wpush, Stk.get, Stk.set]
    rw [(ih _ _ rfl (by simpa [hZb] using hR) (by rfl)).1,
      (ih _ _ rfl (by simpa [hZb] using hR) (by rfl)).2]
    refine ⟨St_eq _ _ _ _ ?_ ?_, ?_⟩
    · simp [nrm, mk_lastAcc, hZb]
    · simp [nrm, hZb, dots, mk_rep, List.replicate_succ, mk_take_succ, mk_drop_succ]
      rw [Nat.succ_mul, Nat.add_comm]
    · simp only [hZb, List.length_cons, List.length_reverse, List.length_append, List.length_nil,
        List.append_nil, List.reverse_reverse, Nat.add_zero]
      ring

theorem mk_dots_len (z : List Bool) : ∀ (m : ℕ) (a : List Bool), (dots z m a).length = m := by
  intro m
  induction m with
  | zero => intro a; rfl
  | succ m ih => intro a; simp [dots, ih]

theorem dots_spec (m : ℕ) (v : Reg) (s : Stk) (hM : s.M = List.replicate m true)
    (hlen : m * s.Z.length ≤ s.A.length) (hMb : s.Mb = []) (hZb : s.Zb = []) (hAb : s.Ab = [])
    (hVb : s.Vb = []) (hV : s.V = []) :
    exec dotsP ⟨v, toFun s⟩ =
        ⟨nrm { v with acc := false }, toFun { s with V := dots s.Z m s.A }⟩ ∧
      cost dotsP ⟨v, toFun s⟩ ≤ 10 * (m + 1) * (s.Z.length + 1) := by
  have e : dotsP = Prog.seq (Prog.seq mk_dmL (move .Mb .M))
      (Prog.seq (Prog.load fun v => { v with acc := false })
        (Prog.seq (move .Ab .A) (move .Vb .V))) := rfl
  obtain ⟨h1, h1c⟩ := mk_dmL_spec m v s hM hlen hZb
  rw [e]
  simp only [exec_seq, cost_seq, exec_load, cost_load, h1, h1c]
  rw [(move_spec .Mb .M (by decide) _ _ _ rfl).2, (move_spec .Mb .M (by decide) _ _ _ rfl).1]
  simp only [exec_load, Stk.set, Stk.get]
  rw [(move_spec .Ab .A (by decide) _ _ _ rfl).2, (move_spec .Ab .A (by decide) _ _ _ rfl).1]
  simp only [Stk.set, Stk.get]
  rw [(move_spec .Vb .V (by decide) _ _ _ rfl).2, (move_spec .Vb .V (by decide) _ _ _ rfl).1]
  simp only [Stk.set, Stk.get]
  refine ⟨?_, ?_⟩
  · refine St_eq _ _ _ _ rfl ?_
    cases s
    simp_all
  · simp only [hMb, hAb, hVb, List.length_append, List.length_reverse, List.length_nil,
      Nat.add_zero, List.length_replicate, mk_dots_len, List.length_take]
    have h2 : 10 * (m + 1) * (s.Z.length + 1) = 10 * (m * s.Z.length) + 10 * m + 10 * s.Z.length + 10 := by
      ring
    have h3 : m * (7 * s.Z.length + 6) = 7 * (m * s.Z.length) + 6 * m := by ring
    rw [h2, h3]
    omega

end

section
open Turing

theorem pa_nt_body : NoTouch K.inp parseBody := by
  simp [parseBody, noTouch_ite, noTouch_seq, noTouch_wpush, noTouch_load]

theorem pa_exec_nil (v : Reg) (s : Stk) (h : s.inp = []) :
    exec parseLoop ⟨v, toFun s⟩ = ⟨nrm v, toFun s⟩ := by
  have e := exec_loop_nil K.inp inpF (fun v => v.go) parseBody ⟨v, toFun s⟩ h
  refine e.trans (congrArg (St.mk (nrm v)) ?_)
  refine (update_toFun_inp s []).trans ?_
  rw [← h]

theorem pa_cost_nil (v : Reg) (s : Stk) (h : s.inp = []) :
    cost parseLoop ⟨v, toFun s⟩ = 1 := by
  have e := cost_loop_nil K.inp inpF (fun v => v.go) parseBody ⟨v, toFun s⟩ h
  exact e

theorem pa_exec_cons (v : Reg) (s : Stk) (x : Bool ⊕ Bool) (l : List (Bool ⊕ Bool))
    (h : s.inp = x :: l) :
    exec parseLoop ⟨v, toFun s⟩ =
      exec parseLoop (exec parseBody ⟨inpF v (some x), toFun { s with inp := l }⟩) := by
  have hc : (fun v : Reg => v.go) (inpF v (some x)) = true := by cases x <;> rfl
  have e := exec_loop_cons K.inp inpF (fun v => v.go) parseBody ⟨v, toFun s⟩ x l h hc pa_nt_body
  refine e.trans ?_
  exact congrArg (fun S => exec parseLoop (exec parseBody ⟨inpF v (some x), S⟩))
    (update_toFun_inp s l)

theorem pa_cost_cons (v : Reg) (s : Stk) (x : Bool ⊕ Bool) (l : List (Bool ⊕ Bool))
    (h : s.inp = x :: l) :
    cost parseLoop ⟨v, toFun s⟩ =
      cost parseLoop (exec parseBody ⟨inpF v (some x), toFun { s with inp := l }⟩) +
        (cost parseBody ⟨inpF v (some x), toFun { s with inp := l }⟩ + 1) := by
  have hc : (fun v : Reg => v.go) (inpF v (some x)) = true := by cases x <;> rfl
  have e := cost_loop_cons K.inp inpF (fun v => v.go) parseBody ⟨v, toFun s⟩ x l h hc pa_nt_body
  refine e.trans ?_
  exact congrArg (fun S => cost parseLoop (exec parseBody ⟨inpF v (some x), S⟩) +
    (cost parseBody ⟨inpF v (some x), S⟩ + 1)) (update_toFun_inp s l)

theorem pa_body_inr (v : Reg) (s : Stk) (b : Bool) :
    exec parseBody ⟨{ v with go := true, tag := true, x := b }, toFun s⟩ =
        ⟨{ v with go := true, tag := true, x := b, ok := v.ok && decide (4 ≤ v.ph.val), ph := 5 },
          toFun { s with C2b := b :: s.C2b }⟩ ∧
      cost parseBody ⟨{ v with go := true, tag := true, x := b }, toFun s⟩ = 3 := by
  refine ⟨?_, ?_⟩
  · simp only [parseBody, exec_ite, exec_seq, exec_load, exec_wpush, ite_true, Stk.get, Stk.set]
  · simp only [parseBody, exec_load, exec_wpush, cost_ite, cost_seq, cost_load,
      cost_wpush, ite_true, Stk.get, Stk.set]

def pa_wr (w : List Bool) (v : Reg) : Reg :=
  match w with
  | [] => v
  | _ :: _ => { v with ok := v.ok && decide (4 ≤ v.ph.val), ph := 5 }

theorem pa_wloop (w : List Bool) : ∀ (v : Reg) (s : Stk), s.inp = w.map Sum.inr →
    exec parseLoop ⟨v, toFun s⟩ =
        ⟨nrm (pa_wr w v), toFun { s with inp := [], C2b := w.reverse ++ s.C2b }⟩ ∧
      cost parseLoop ⟨v, toFun s⟩ = 4 * w.length + 1 := by
  induction w with
  | nil =>
    intro v s h
    refine ⟨?_, ?_⟩
    · rw [pa_exec_nil v s h]
      refine St_eq _ _ _ _ rfl ?_
      cases s
      simp_all
    · rw [pa_cost_nil v s h]; rfl
  | cons b w ih =>
    intro v s h
    have e0 : inpF v (some (Sum.inr b)) = { v with go := true, tag := true, x := b } := rfl
    refine ⟨?_, ?_⟩
    · rw [pa_exec_cons v s (Sum.inr b) (w.map Sum.inr) h, e0, (pa_body_inr _ _ _).1,
        (ih _ _ rfl).1]
      refine St_eq _ _ _ _ ?_ ?_
      · cases w <;> simp [pa_wr, nrm]
      · simp
    · rw [pa_cost_cons v s (Sum.inr b) (w.map Sum.inr) h, e0, (pa_body_inr _ _ _).1,
        (pa_body_inr _ _ _).2, (ih _ _ rfl).2]
      simp only [List.length_cons]
      ring

structure pa_Q where
  ph : Fin 6
  n : ℕ
  m : ℕ
  k : ℕ
  d : ℕ
  ab : List Bool

def pa_step (q : pa_Q) (b : Bool) : pa_Q :=
  if q.ph = 0 then (if b then { q with n := q.n + 1 } else { q with ph := 1 })
  else if q.ph = 1 then (if b then { q with m := q.m + 1 } else { q with ph := 2 })
  else if q.ph = 2 then (if b then { q with k := q.k + 1 } else { q with ph := 3 })
  else if q.ph = 3 then (if b then { q with d := q.d + 1 } else { q with ph := 4 })
  else { q with ab := b :: q.ab }

def pa_enc (q : pa_Q) (s : Stk) : Stk :=
  { s with N := List.replicate q.n true, N2 := List.replicate q.n true, T := List.replicate (q.n + q.m) true, M := List.replicate q.m true, Kc := List.replicate q.k true, D := List.replicate q.d true, Ab := q.ab }

theorem pa_body_inl (q : pa_Q) (v : Reg) (s : Stk) (b : Bool) (hph : v.ph = q.ph) :
    exec parseBody ⟨{ v with go := true, tag := false, x := b }, toFun (pa_enc q s)⟩ =
        ⟨{ v with go := true, tag := false, x := b, ph := (pa_step q b).ph },
          toFun (pa_enc (pa_step q b) s)⟩ ∧
      cost parseBody ⟨{ v with go := true, tag := false, x := b }, toFun (pa_enc q s)⟩ ≤ 7 := by
  obtain ⟨ph, n, m, k, d, ab⟩ := q
  obtain ⟨go, tag, x, y, u, w, acc, m0, m1, vph, ok, res⟩ := v
  simp only at hph
  subst hph
  fin_cases vph <;> cases b
  all_goals
    refine ⟨?_, ?_⟩
  all_goals
    simp [parseBody, exec_ite, exec_seq, exec_load, exec_wpush, cost_ite, cost_seq, cost_load,
      cost_wpush, Stk.get, Stk.set, pa_enc, pa_step, tt, List.replicate_succ, ← Nat.add_assoc, Nat.add_right_comm n 1 m]

theorem pa_xloop (w : List Bool) (x : List Bool) : ∀ (q : pa_Q) (v : Reg) (s : Stk), v.ph = q.ph →
    exec parseLoop ⟨v, toFun (pa_enc q { s with inp := x.map Sum.inl ++ w.map Sum.inr })⟩ =
        ⟨nrm (pa_wr w { v with ph := (x.foldl pa_step q).ph }),
          toFun (pa_enc (x.foldl pa_step q) { s with inp := [], C2b := w.reverse ++ s.C2b })⟩ ∧
      cost parseLoop ⟨v, toFun (pa_enc q { s with inp := x.map Sum.inl ++ w.map Sum.inr })⟩ ≤
        8 * x.length + 4 * w.length + 1 := by
  induction x with
  | nil =>
    intro q v s hph
    have hv : { v with ph := q.ph } = v := by cases v; simp_all
    obtain ⟨e1, e2⟩ := pa_wloop w v (pa_enc q { s with inp := w.map Sum.inr }) rfl
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_nil, hv]
      exact e1
    · refine le_of_eq (e2.trans ?_)
      simp
  | cons b x ih =>
    intro q v s hph
    have e0 : inpF v (some (Sum.inl b)) = { v with go := true, tag := false, x := b } := rfl
    have hs : (pa_enc q { s with inp := (b :: x).map Sum.inl ++ w.map Sum.inr }).inp =
        Sum.inl b :: (x.map Sum.inl ++ w.map Sum.inr) := rfl
    have hs2 : { pa_enc q { s with inp := (b :: x).map Sum.inl ++ w.map Sum.inr } with
        inp := x.map Sum.inl ++ w.map Sum.inr } =
        pa_enc q { s with inp := x.map Sum.inl ++ w.map Sum.inr } := rfl
    obtain ⟨b1, b2⟩ := pa_body_inl q v { s with inp := x.map Sum.inl ++ w.map Sum.inr } b hph
    obtain ⟨i1, i2⟩ := ih (pa_step q b) { v with go := true, tag := false, x := b, ph := (pa_step q b).ph } s rfl
    refine ⟨?_, ?_⟩
    · rw [pa_exec_cons _ _ _ _ hs, e0, hs2, b1, i1]
      refine St_eq _ _ _ _ ?_ rfl
      cases w <;> rfl
    · rw [pa_cost_cons _ _ _ _ hs, e0, hs2, b1]
      simp only [List.length_cons]
      omega

def pa_size (q : pa_Q) : ℕ := q.n + q.m + q.k + q.d + q.ab.length

theorem pa_size_step (q : pa_Q) (b : Bool) : pa_size (pa_step q b) ≤ pa_size q + 1 := by
  unfold pa_step
  split_ifs <;> simp [pa_size] <;> omega

theorem pa_size_fold (x : List Bool) : ∀ q : pa_Q, pa_size (x.foldl pa_step q) ≤ pa_size q + x.length := by
  induction x with
  | nil => intro q; simp
  | cons b x ih =>
    intro q
    have h1 := ih (pa_step q b)
    have h2 := pa_size_step q b
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem pa_fold4 (x : List Bool) : ∀ q : pa_Q, q.ph = 4 →
    x.foldl pa_step q = { q with ab := x.reverse ++ q.ab } := by
  induction x with
  | nil => intro q _; simp
  | cons b x ih =>
    intro q h
    have e : pa_step q b = { q with ab := b :: q.ab } := by simp [pa_step, h]
    rw [List.foldl_cons, e, ih { q with ab := b :: q.ab } h]
    simp

theorem pa_fold3 (x : List Bool) : ∀ q : pa_Q, q.ph = 3 →
    (hdrSplit x = none → (x.foldl pa_step q).ph = 3) ∧
      (∀ c r, hdrSplit x = some (c, r) →
        x.foldl pa_step q = r.foldl pa_step { q with ph := 4, d := q.d + c }) := by
  induction x with
  | nil => intro q h; simp [hdrSplit, h]
  | cons b x ih =>
    intro q h
    cases b with
    | false =>
      have e : pa_step q false = { q with ph := 4 } := by simp [pa_step, h]
      simp [hdrSplit, e]
    | true =>
      have e : pa_step q true = { q with d := q.d + 1 } := by simp [pa_step, h]
      obtain ⟨i1, i2⟩ := ih { q with d := q.d + 1 } h
      rw [List.foldl_cons, e]
      refine ⟨?_, ?_⟩
      · intro hn
        apply i1
        cases hx : hdrSplit x with
        | none => rfl
        | some p => simp [hdrSplit, hx] at hn
      · intro c r hc
        cases hx : hdrSplit x with
        | none => simp [hdrSplit, hx] at hc
        | some p =>
          obtain ⟨c', r'⟩ := p
          simp [hdrSplit, hx] at hc
          obtain ⟨hc1, hc2⟩ := hc
          subst hc1 hc2
          rw [i2 c' r' hx]
          simp [Nat.add_assoc, Nat.add_comm 1 c']

theorem pa_fold2 (x : List Bool) : ∀ q : pa_Q, q.ph = 2 →
    (hdrSplit x = none → (x.foldl pa_step q).ph = 2) ∧
      (∀ c r, hdrSplit x = some (c, r) →
        x.foldl pa_step q = r.foldl pa_step { q with ph := 3, k := q.k + c }) := by
  induction x with
  | nil => intro q h; simp [hdrSplit, h]
  | cons b x ih =>
    intro q h
    cases b with
    | false =>
      have e : pa_step q false = { q with ph := 3 } := by simp [pa_step, h]
      simp [hdrSplit, e]
    | true =>
      have e : pa_step q true = { q with k := q.k + 1 } := by simp [pa_step, h]
      obtain ⟨i1, i2⟩ := ih { q with k := q.k + 1 } h
      rw [List.foldl_cons, e]
      refine ⟨?_, ?_⟩
      · intro hn
        apply i1
        cases hx : hdrSplit x with
        | none => rfl
        | some p => simp [hdrSplit, hx] at hn
      · intro c r hc
        cases hx : hdrSplit x with
        | none => simp [hdrSplit, hx] at hc
        | some p =>
          obtain ⟨c', r'⟩ := p
          simp [hdrSplit, hx] at hc
          obtain ⟨hc1, hc2⟩ := hc
          subst hc1 hc2
          rw [i2 c' r' hx]
          simp [Nat.add_assoc, Nat.add_comm 1 c']

theorem pa_fold1 (x : List Bool) : ∀ q : pa_Q, q.ph = 1 →
    (hdrSplit x = none → (x.foldl pa_step q).ph = 1) ∧
      (∀ c r, hdrSplit x = some (c, r) →
        x.foldl pa_step q = r.foldl pa_step { q with ph := 2, m := q.m + c }) := by
  induction x with
  | nil => intro q h; simp [hdrSplit, h]
  | cons b x ih =>
    intro q h
    cases b with
    | false =>
      have e : pa_step q false = { q with ph := 2 } := by simp [pa_step, h]
      simp [hdrSplit, e]
    | true =>
      have e : pa_step q true = { q with m := q.m + 1 } := by simp [pa_step, h]
      obtain ⟨i1, i2⟩ := ih { q with m := q.m + 1 } h
      rw [List.foldl_cons, e]
      refine ⟨?_, ?_⟩
      · intro hn
        apply i1
        cases hx : hdrSplit x with
        | none => rfl
        | some p => simp [hdrSplit, hx] at hn
      · intro c r hc
        cases hx : hdrSplit x with
        | none => simp [hdrSplit, hx] at hc
        | some p =>
          obtain ⟨c', r'⟩ := p
          simp [hdrSplit, hx] at hc
          obtain ⟨hc1, hc2⟩ := hc
          subst hc1 hc2
          rw [i2 c' r' hx]
          simp [Nat.add_assoc, Nat.add_comm 1 c']

theorem pa_fold0 (x : List Bool) : ∀ q : pa_Q, q.ph = 0 →
    (hdrSplit x = none → (x.foldl pa_step q).ph = 0) ∧
      (∀ c r, hdrSplit x = some (c, r) →
        x.foldl pa_step q = r.foldl pa_step { q with ph := 1, n := q.n + c }) := by
  induction x with
  | nil => intro q h; simp [hdrSplit, h]
  | cons b x ih =>
    intro q h
    cases b with
    | false =>
      have e : pa_step q false = { q with ph := 1 } := by simp [pa_step, h]
      simp [hdrSplit, e]
    | true =>
      have e : pa_step q true = { q with n := q.n + 1 } := by simp [pa_step, h]
      obtain ⟨i1, i2⟩ := ih { q with n := q.n + 1 } h
      rw [List.foldl_cons, e]
      refine ⟨?_, ?_⟩
      · intro hn
        apply i1
        cases hx : hdrSplit x with
        | none => rfl
        | some p => simp [hdrSplit, hx] at hn
      · intro c r hc
        cases hx : hdrSplit x with
        | none => simp [hdrSplit, hx] at hc
        | some p =>
          obtain ⟨c', r'⟩ := p
          simp [hdrSplit, hx] at hc
          obtain ⟨hc1, hc2⟩ := hc
          subst hc1 hc2
          rw [i2 c' r' hx]
          simp [Nat.add_assoc, Nat.add_comm 1 c']

theorem pa_pure (x : List Bool) :
    (4 ≤ (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).ph.val →
        parse x = some ((x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).n, (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).m,
          (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).k, (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).d,
          (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).ab.reverse)) ∧
      (¬ 4 ≤ (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).ph.val → parse x = none) := by
  rcases h1 : hdrSplit x with _ | ⟨c1, r1⟩
  · have e := (pa_fold0 x ⟨0, 0, 0, 0, 0, []⟩ rfl).1 h1
    simp [parse, h1, e]
  · rw [(pa_fold0 x ⟨0, 0, 0, 0, 0, []⟩ rfl).2 c1 r1 h1]
    rcases h2 : hdrSplit r1 with _ | ⟨c2, r2⟩
    · have e := (pa_fold1 r1 ⟨1, 0 + c1, 0, 0, 0, []⟩ rfl).1 h2
      simp only [Nat.zero_add] at e
      simp [parse, h1, h2, e]
    · rw [(pa_fold1 r1 ⟨1, 0 + c1, 0, 0, 0, []⟩ rfl).2 c2 r2 h2]
      rcases h3 : hdrSplit r2 with _ | ⟨c3, r3⟩
      · have e := (pa_fold2 r2 ⟨2, 0 + c1, 0 + c2, 0, 0, []⟩ rfl).1 h3
        simp only [Nat.zero_add] at e
        simp [parse, h1, h2, h3, e]
      · rw [(pa_fold2 r2 ⟨2, 0 + c1, 0 + c2, 0, 0, []⟩ rfl).2 c3 r3 h3]
        rcases h4 : hdrSplit r3 with _ | ⟨c4, r4⟩
        · have e := (pa_fold3 r3 ⟨3, 0 + c1, 0 + c2, 0 + c3, 0, []⟩ rfl).1 h4
          simp only [Nat.zero_add] at e
          simp [parse, h1, h2, h3, h4, e]
        · rw [(pa_fold3 r3 ⟨3, 0 + c1, 0 + c2, 0 + c3, 0, []⟩ rfl).2 c4 r4 h4,
            pa_fold4 r4 ⟨4, 0 + c1, 0 + c2, 0 + c3, 0 + c4, []⟩ rfl]
          simp [parse, h1, h2, h3, h4]

theorem parse_spec (x w : List Bool) :
    ∃ (n m k d : ℕ) (ab : List Bool) (ph : Fin 6) (ok : Bool),
      exec parseP ⟨regInit, toFun { emp with inp := x.map Sum.inl ++ w.map Sum.inr }⟩ =
        ⟨{ regInit with ph := ph, ok := ok },
          toFun { emp with N := List.replicate n true, N2 := List.replicate n true,
                                        T := List.replicate (n + m) true, M := List.replicate m true,
                                        Kc := List.replicate k true, D := List.replicate d true,
                                        Ab := ab, C2b := w.reverse }⟩ ∧
      (ok = true → parse x = some (n, m, k, d, ab.reverse)) ∧
      (ok = false → parse x = none) ∧
      n + m + k + d + ab.length ≤ x.length ∧
      cost parseP ⟨regInit, toFun { emp with inp := x.map Sum.inl ++ w.map Sum.inr }⟩ ≤
        8 * (x.length + w.length) + 2 := by
  have hs : ({ emp with inp := x.map Sum.inl ++ w.map Sum.inr } : Stk) =
      pa_enc ⟨0, 0, 0, 0, 0, []⟩ { emp with inp := x.map Sum.inl ++ w.map Sum.inr } := rfl
  obtain ⟨e1, e2⟩ := pa_xloop w x ⟨0, 0, 0, 0, 0, []⟩ regInit emp rfl
  obtain ⟨p1, p2⟩ := pa_pure x
  have hsz := pa_size_fold x ⟨0, 0, 0, 0, 0, []⟩
  refine ⟨(x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).n, (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).m,
    (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).k, (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).d,
    (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).ab,
    (pa_wr w { regInit with ph := (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).ph }).ph,
    decide (4 ≤ (x.foldl pa_step ⟨0, 0, 0, 0, 0, []⟩).ph.val), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, parseP, exec_seq, e1, exec_load]
    refine St_eq _ _ _ _ ?_ ?_
    · cases w <;> simp [pa_wr, nrm, regInit] <;> exact decide_eq_decide.mpr Iff.rfl
    · simp [pa_enc, emp]
  · intro h
    exact p1 (by simpa using h)
  · intro h
    exact p2 (by simpa using h)
  · simpa [pa_size] using hsz
  · rw [hs, parseP, cost_seq, cost_load]
    exact le_trans (Nat.add_le_add_left e2 1) (by omega)

def pa_Push (body : Pg) (p : W) (j T0 : ℕ) (I : Stk → Prop) : Prop :=
  ∀ (v : Reg) (s : Stk), I s → ∃ v' : Reg, nrm v' = nrm v ∧
    exec body ⟨v, toFun s⟩ = ⟨v', toFun (s.set p (List.replicate j true ++ s.get p))⟩ ∧
    cost body ⟨v, toFun s⟩ ≤ T0

theorem pa_forC_loop (c cb p : W) (hcb : c ≠ cb) (hcp : c ≠ p) (hbp : cb ≠ p) (body : Pg)
    (j T0 : ℕ) (I : Stk → Prop) (hIc : ∀ s l, I s → I (s.set c l))
    (hIb : ∀ s l, I s → I (s.set cb l)) (hIp : ∀ s l, I s → I (s.set p l))
    (hnt : NoTouch (K.w c) body) (hbody : pa_Push body p j T0 I) (cnt : ℕ) :
    ∀ (v : Reg) (s : Stk), I s → s.get c = List.replicate cnt true →
    exec (forPop c (fun v _ => v) id (Prog.seq (wpush cb (fun _ => true)) body)) ⟨v, toFun s⟩ =
        ⟨nrm v, toFun (((s.set c []).set cb (List.replicate cnt true ++ s.get cb)).set p
          (List.replicate (cnt * j) true ++ s.get p))⟩ ∧
      cost (forPop c (fun v _ => v) id (Prog.seq (wpush cb (fun _ => true)) body)) ⟨v, toFun s⟩ ≤
        cnt * (T0 + 2) + 1 := by
  have hnt' : NoTouch (K.w c) (Prog.seq (wpush cb (fun _ => true)) body) := by
    rw [noTouch_seq, noTouch_wpush]
    exact ⟨fun e => hcb (K.w.inj e).symm, hnt⟩
  induction cnt with
  | zero =>
    intro v s hI h
    refine ⟨?_, ?_⟩
    · rw [exec_forPop_nil c _ _ _ v s h]
      refine St_eq _ _ _ _ rfl ?_
      apply Stk.ext_get
      · simp [set_inp]
      · intro a
        simp only [get_set]
        by_cases h1 : a = p
        · simp [h1, hbp, hcp, hcb, Ne.symm hbp, Ne.symm hcp, Ne.symm hcb]
        · by_cases h2 : a = cb
          · simp [h2, hbp, hcp, hcb, Ne.symm hbp, Ne.symm hcp, Ne.symm hcb]
          · by_cases h3 : a = c
            · simp [h3, h, hbp, hcp, hcb, Ne.symm hbp, Ne.symm hcp, Ne.symm hcb]
            · simp [h1, h2, h3]
    · rw [cost_forPop_nil c _ _ _ v s h]
      omega
  | succ cnt ih =>
    intro v s hI h
    have h' : s.get c = true :: List.replicate cnt true := by rw [h, List.replicate_succ]
    obtain ⟨s1, hs1⟩ : ∃ s1 : Stk, s1 = (s.set c (List.replicate cnt true)).set cb
        (true :: (s.set c (List.replicate cnt true)).get cb) := ⟨_, rfl⟩
    have hI1 : I s1 := by rw [hs1]; exact hIb _ _ (hIc _ _ hI)
    obtain ⟨v', hv', he, hc⟩ := hbody { v with go := true } s1 hI1
    obtain ⟨e1, e2⟩ := ih v' (s1.set p (List.replicate j true ++ s1.get p)) (hIp _ _ hI1)
      (by rw [hs1, get_set_ne _ _ _ _ hcp, get_set_ne _ _ _ _ hcb, get_set_self])
    refine ⟨?_, ?_⟩
    · rw [exec_forPop_cons c _ _ _ v s true _ h' hnt', exec_seq, exec_wpush, ← hs1, he, e1]
      refine St_eq _ _ _ _ hv' ?_
      subst hs1
      apply Stk.ext_get
      · simp [set_inp]
      · intro a
        simp only [get_set]
        by_cases h1 : a = p
        · simp [h1, hbp, hcp, hcb, Ne.symm hbp, Ne.symm hcp, Ne.symm hcb, ← List.append_assoc, ← List.replicate_add,
            Nat.succ_mul]
        · by_cases h2 : a = cb
          · simp [h2, hbp, hcp, hcb, Ne.symm hbp, Ne.symm hcp, Ne.symm hcb, List.replicate_succ']
          · by_cases h3 : a = c
            · simp [h3, hbp, hcp, hcb, Ne.symm hbp, Ne.symm hcp, Ne.symm hcb]
            · simp [h1, h2, h3]
    · rw [cost_forPop_cons c _ _ _ v s true _ h' hnt', cost_seq, exec_seq, exec_wpush, cost_wpush, ← hs1, he]
      refine le_trans (Nat.add_le_add e2 (Nat.add_le_add_right (Nat.add_le_add_right hc 1) 1)) ?_
      rw [Nat.succ_mul]
      omega

theorem pa_forC (c cb p : W) (hcb : c ≠ cb) (hcp : c ≠ p) (hbp : cb ≠ p) (body : Pg)
    (j T0 : ℕ) (I : Stk → Prop) (hIc : ∀ s l, I s → I (s.set c l))
    (hIb : ∀ s l, I s → I (s.set cb l)) (hIp : ∀ s l, I s → I (s.set p l))
    (hnt : NoTouch (K.w c) body) (hbody : pa_Push body p j T0 I) (cnt : ℕ)
    (v : Reg) (s : Stk) (hI : I s) (hc : s.get c = List.replicate cnt true) (hb : s.get cb = []) :
    exec (forC c cb body) ⟨v, toFun s⟩ =
        ⟨nrm v, toFun (s.set p (List.replicate (cnt * j) true ++ s.get p))⟩ ∧
      cost (forC c cb body) ⟨v, toFun s⟩ ≤ cnt * (T0 + 4) + 2 := by
  obtain ⟨e1, e2⟩ := pa_forC_loop c cb p hcb hcp hbp body j T0 I hIc hIb hIp hnt hbody cnt v s hI hc
  have hl : (((s.set c []).set cb (List.replicate cnt true ++ s.get cb)).set p
      (List.replicate (cnt * j) true ++ s.get p)).get cb = List.replicate cnt true := by
    rw [get_set_ne _ _ _ _ hbp, get_set_self, hb, List.append_nil]
  obtain ⟨m1, m2⟩ := move_spec cb c (Ne.symm hcb) _ (nrm v) _ hl
  refine ⟨?_, ?_⟩
  · rw [forC, exec_seq, e1, m1]
    refine St_eq _ _ _ _ rfl ?_
    apply Stk.ext_get
    · simp [set_inp]
    · intro a
      simp only [get_set]
      by_cases h1 : a = p
      · simp [h1, hbp, hcp, hcb, Ne.symm hbp, Ne.symm hcp, Ne.symm hcb]
      · by_cases h2 : a = cb
        · simp [h2, hbp, hcp, hcb, Ne.symm hbp, Ne.symm hcp, Ne.symm hcb, hb]
        · by_cases h3 : a = c
          · simp [h3, hbp, hcp, hcb, Ne.symm hbp, Ne.symm hcp, Ne.symm hcb, hb, hc]
          · simp [h1, h2, h3]
  · rw [forC, cost_seq, e1, m2, List.length_replicate]
    have e3 := Nat.mul_add cnt T0 2
    have e4 := Nat.mul_add cnt T0 4
    omega

theorem pa_Push_forC (c cb p : W) (hcb : c ≠ cb) (hcp : c ≠ p) (hbp : cb ≠ p) (body : Pg)
    (j T0 : ℕ) (I : Stk → Prop) (hIc : ∀ s l, I s → I (s.set c l))
    (hIb : ∀ s l, I s → I (s.set cb l)) (hIp : ∀ s l, I s → I (s.set p l))
    (hnt : NoTouch (K.w c) body) (hbody : pa_Push body p j T0 I) (cnt : ℕ) :
    pa_Push (forC c cb body) p (cnt * j) (cnt * (T0 + 4) + 2)
      (fun s => I s ∧ s.get c = List.replicate cnt true ∧ s.get cb = []) := by
  intro v s hs
  obtain ⟨e1, e2⟩ := pa_forC c cb p hcb hcp hbp body j T0 I hIc hIb hIp hnt hbody cnt v s hs.1
    hs.2.1 hs.2.2
  exact ⟨nrm v, rfl, e1, e2⟩

theorem pa_Push_base (p : W) : pa_Push (wpush p tt) p 1 1 (fun _ => True) := by
  intro v s _
  exact ⟨v, rfl, exec_wpush p tt v s, le_of_eq (cost_wpush p tt _)⟩

def pa_Run (P : Pg) (v : Reg) (s : Stk) (v' : Reg) (s' : Stk) (c : ℕ) : Prop :=
  exec P ⟨v, toFun s⟩ = ⟨v', toFun s'⟩ ∧ cost P ⟨v, toFun s⟩ ≤ c

theorem pa_Run_seq {P Q : Pg} {v : Reg} {s : Stk} {v1 : Reg} {s1 : Stk} {c1 : ℕ} {v2 : Reg}
    {s2 : Stk} {c2 : ℕ} (h1 : pa_Run P v s v1 s1 c1) (h2 : pa_Run Q v1 s1 v2 s2 c2) :
    pa_Run (Prog.seq P Q) v s v2 s2 (c1 + c2) := by
  refine ⟨?_, ?_⟩
  · rw [exec_seq, h1.1, h2.1]
  · rw [cost_seq, h1.1]
    have a := h1.2
    have b := h2.2
    omega

def pa_subKB : Pg :=
  Prog.seq (wpush .Kb tt)
    (Prog.seq (wpop .T (fun v _ => v))
      (Prog.seq (wpop .M (fun v o => { v with y := o.isSome }))
        (Prog.seq (Prog.load fun v => { v with ok := v.ok && v.y })
          (Prog.ite (fun v => v.y) (wpush .Mb tt) (Prog.load id)))))

def pa_subKL : Pg := forPop .Kc (fun v _ => v) id pa_subKB

theorem pa_subKB_spec (v : Reg) (s : Stk) :
    exec pa_subKB ⟨v, toFun s⟩ =
        ⟨{ v with y := s.M.head?.isSome, ok := v.ok && s.M.head?.isSome },
          toFun { s with Kb := true :: s.Kb, T := s.T.tail, M := s.M.tail, Mb := if s.M.head?.isSome then true :: s.Mb else s.Mb }⟩ ∧
      cost pa_subKB ⟨v, toFun s⟩ = 6 := by
  cases hM : s.M with
  | nil =>
    refine ⟨?_, ?_⟩
    · simp only [pa_subKB, exec_seq, exec_wpop, exec_wpush, exec_load, exec_ite, Stk.get, Stk.set, hM,
        List.head?_nil, List.tail_nil, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, tt, id]
    · simp only [pa_subKB, exec_seq, exec_wpop, exec_wpush, exec_load, exec_ite, Stk.get, Stk.set, hM,
        cost_seq, cost_wpop, cost_wpush, cost_load, cost_ite,
        List.head?_nil, List.tail_nil, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, tt, id]
  | cons y a =>
    refine ⟨?_, ?_⟩
    · simp only [pa_subKB, exec_seq, exec_wpop, exec_wpush, exec_load, exec_ite, Stk.get, Stk.set, hM,
        List.head?_cons, List.tail_cons, Option.isSome_some, ↓reduceIte, tt, id]
    · simp only [pa_subKB, exec_seq, exec_wpop, exec_wpush, exec_load, exec_ite, Stk.get, Stk.set, hM,
        cost_seq, cost_wpop, cost_wpush, cost_load, cost_ite,
        List.head?_cons, List.tail_cons, Option.isSome_some, ↓reduceIte, tt, id]

theorem pa_subKL_spec (l : List Bool) : ∀ (v : Reg) (s : Stk), s.Kc = l →
    exec pa_subKL ⟨v, toFun s⟩ =
        ⟨nrm { v with ok := v.ok && decide (l.length ≤ s.M.length) },
          toFun { s with Kc := [], Kb := List.replicate l.length true ++ s.Kb, T := s.T.drop l.length, M := s.M.drop l.length, Mb := List.replicate (min l.length s.M.length) true ++ s.Mb }⟩ ∧
      cost pa_subKL ⟨v, toFun s⟩ = 7 * l.length + 1 := by
  have hnt : NoTouch (K.w W.Kc) pa_subKB := by
    simp [pa_subKB, noTouch_seq, noTouch_wpop, noTouch_wpush, noTouch_load, noTouch_ite]
  induction l with
  | nil =>
    intro v s hK
    refine ⟨?_, ?_⟩
    · rw [pa_subKL, exec_forPop_nil .Kc _ _ _ v s hK]
      refine St_eq _ _ _ _ ?_ ?_
      · simp [nrm]
      · cases s
        simp_all
    · rw [pa_subKL, cost_forPop_nil .Kc _ _ _ v s hK]; rfl
  | cons x l ih =>
    intro v s hK
    refine ⟨?_, ?_⟩
    · rw [pa_subKL, exec_forPop_cons .Kc _ _ _ v s x l hK hnt, (pa_subKB_spec _ _).1, ← pa_subKL,
        (ih _ _ rfl).1]
      refine St_eq _ _ _ _ ?_ ?_
      · cases hM : s.M <;> simp [nrm, Stk.get, Stk.set, hM]
      · cases hM : s.M <;>
          simp [Stk.get, Stk.set, hM, List.replicate_succ', Nat.succ_min_succ]
    · rw [pa_subKL, cost_forPop_cons .Kc _ _ _ v s x l hK hnt, (pa_subKB_spec _ _).1,
        (pa_subKB_spec _ _).2, ← pa_subKL, (ih _ _ rfl).2]
      simp only [List.length_cons]
      ring

theorem pa_subK_run (k m t : ℕ) (v : Reg) (s : Stk) (hK : s.Kc = List.replicate k true)
    (hM : s.M = List.replicate m true) (hT : s.T = List.replicate t true) (hKb : s.Kb = [])
    (hMb : s.Mb = []) :
    pa_Run subK v s (nrm { v with ok := v.ok && decide (k ≤ m) })
      { s with T := List.replicate (t - k) true } (11 * k + 3) := by
  have e : subK = Prog.seq pa_subKL (Prog.seq (move .Kb .Kc) (move .Mb .M)) := rfl
  obtain ⟨l1, l2⟩ := pa_subKL_spec _ v s rfl
  have hmin : min k m + (m - k) = m := by omega
  refine ⟨?_, ?_⟩
  · rw [e, exec_seq, l1, exec_seq, (move_spec .Kb .Kc (by decide) _ _ _ rfl).1,
      (move_spec .Mb .M (by decide) _ _ _ rfl).1]
    refine St_eq _ _ _ _ ?_ ?_
    · simp [nrm, hK, hM]
    · simp only [Stk.set, Stk.get]
      cases s
      simp_all
  · rw [e, cost_seq, cost_seq, l1, l2, (move_spec .Kb .Kc (by decide) _ _ _ rfl).1,
      (move_spec .Kb .Kc (by decide) _ _ _ rfl).2, (move_spec .Mb .M (by decide) _ _ _ rfl).2]
    simp [Stk.set, Stk.get, hK, hM, hKb, hMb]
    omega

theorem pa_subD_spec (l : List Bool) : ∀ (v : Reg) (s : Stk), s.D = l →
    pa_Run subD v s (nrm v) { s with D := [], T := s.T.drop l.length } (2 * l.length + 1) := by
  have hnt : NoTouch (K.w W.D) (wpop .T (fun v _ => v)) := by
    simp [noTouch_wpop]
  induction l with
  | nil =>
    intro v s hD
    refine ⟨?_, ?_⟩
    · rw [subD, exec_forPop_nil .D _ _ _ v s hD]
      refine St_eq _ _ _ _ rfl ?_
      cases s
      simp_all
    · rw [subD, cost_forPop_nil .D _ _ _ v s hD]
      omega
  | cons x l ih =>
    intro v s hD
    obtain ⟨i1, i2⟩ := ih { v with go := true } ((s.set .D l).set .T ((s.set .D l).get .T).tail) rfl
    refine ⟨?_, ?_⟩
    · rw [subD, exec_forPop_cons .D _ _ _ v s x l hD hnt, exec_wpop, ← subD, i1]
      refine St_eq _ _ _ _ rfl ?_
      simp [Stk.set, Stk.get]
    · rw [subD, cost_forPop_cons .D _ _ _ v s x l hD hnt, exec_wpop, cost_wpop, ← subD]
      simp only [List.length_cons]
      omega

theorem pa_prodA_run (n m : ℕ) (v : Reg) (s : Stk) (hM : s.M = List.replicate m true)
    (hMb : s.Mb = []) (hN : s.N = List.replicate n true) (hNb : s.Nb = [])
    (hN2 : s.N2 = List.replicate n true) (hN2b : s.N2b = []) :
    pa_Run prodA v s (nrm v) (s.set .P (List.replicate (m * (n * (n * 1))) true ++ s.get .P))
      (m * (n * (n * (1 + 4) + 2 + 4) + 2 + 4) + 2) := by
  have h1 := pa_Push_forC .N2 .N2b .P (by decide) (by decide) (by decide) (wpush .P tt) 1 1
    (fun _ => True) (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h)
    (by simp [noTouch_wpush]) (pa_Push_base .P) n
  have h2 := pa_Push_forC .N .Nb .P (by decide) (by decide) (by decide) _ _ _ _
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h)
    (by simp [noTouch_forC, noTouch_wpush]) h1 n
  exact pa_forC .M .Mb .P (by decide) (by decide) (by decide) _ _ _ _
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h)
    (by simp [noTouch_forC, noTouch_wpush]) h2 m v s ⟨⟨trivial, hN2, hN2b⟩, hN, hNb⟩ hM hMb

theorem pa_copyT_run (t : ℕ) (v : Reg) (s : Stk) (hT : s.T = List.replicate t true)
    (hTb : s.Tb = []) :
    pa_Run copyT v s (nrm v) (s.set .T2 (List.replicate (t * 1) true ++ s.get .T2))
      (t * (1 + 4) + 2) :=
  pa_forC .T .Tb .T2 (by decide) (by decide) (by decide) (wpush .T2 tt) 1 1
    (fun _ => True) (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h)
    (by simp [noTouch_wpush]) (pa_Push_base .T2) t v s trivial hT hTb

theorem pa_prodW_run (t n : ℕ) (v : Reg) (s : Stk) (hT : s.T = List.replicate t true)
    (hTb : s.Tb = []) (hN : s.N = List.replicate n true) (hNb : s.Nb = []) :
    pa_Run prodW v s (nrm v) (s.set .P (List.replicate (t * (n * 1)) true ++ s.get .P))
      (t * (n * (1 + 4) + 2 + 4) + 2) := by
  have h1 := pa_Push_forC .N .Nb .P (by decide) (by decide) (by decide) (wpush .P tt) 1 1
    (fun _ => True) (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h)
    (by simp [noTouch_wpush]) (pa_Push_base .P) n
  exact pa_forC .T .Tb .P (by decide) (by decide) (by decide) _ _ _ _
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h)
    (by simp [noTouch_forC, noTouch_wpush]) h1 t v s ⟨trivial, hN, hNb⟩ hT hTb

theorem pa_bool (ok : Bool) (l : List Bool) (a : ℕ) :
    (ok && decide (a ≤ l.length) && l[a]?.isNone) = (ok && decide (a = l.length)) := by
  cases ok
  · simp
  · rw [Bool.eq_iff_iff]
    simp
    omega

def pa_cmpAL : Pg :=
  forPop .Ab (fun v b => { v with x := b }) id
    (Prog.seq (wpush .A (fun v => v.x))
      (Prog.seq (wpop .P (fun v o => { v with y := o.isSome }))
        (Prog.load fun v => { v with ok := v.ok && v.y })))

theorem pa_cmpAL_spec (l : List Bool) : ∀ (v : Reg) (s : Stk), s.Ab = l →
    exec pa_cmpAL ⟨v, toFun s⟩ =
        ⟨nrm { v with ok := v.ok && decide (l.length ≤ s.P.length) },
          toFun { s with Ab := [], A := l.reverse ++ s.A, P := s.P.drop l.length }⟩ ∧
      cost pa_cmpAL ⟨v, toFun s⟩ = 4 * l.length + 1 := by
  have hnt : NoTouch (K.w W.Ab) (Prog.seq (wpush .A (fun v => v.x))
      (Prog.seq (wpop .P (fun v o => { v with y := o.isSome }))
        (Prog.load fun v => { v with ok := v.ok && v.y }))) := by
    simp [noTouch_seq, noTouch_wpop, noTouch_wpush, noTouch_load]
  induction l with
  | nil =>
    intro v s h
    refine ⟨?_, ?_⟩
    · rw [pa_cmpAL, exec_forPop_nil .Ab _ _ _ v s h]
      refine St_eq _ _ _ _ ?_ ?_
      · simp [nrm]
      · cases s
        simp_all
    · rw [pa_cmpAL, cost_forPop_nil .Ab _ _ _ v s h]; rfl
  | cons x l ih =>
    intro v s h
    refine ⟨?_, ?_⟩
    · rw [pa_cmpAL, exec_forPop_cons .Ab _ _ _ v s x l h hnt, exec_seq, exec_wpush, exec_seq,
        exec_wpop, exec_load, ← pa_cmpAL, (ih _ _ rfl).1]
      refine St_eq _ _ _ _ ?_ ?_
      · cases hP : s.P <;> simp [nrm, Stk.get, Stk.set, hP]
      · simp [Stk.get, Stk.set]
    · rw [pa_cmpAL, cost_forPop_cons .Ab _ _ _ v s x l h hnt, exec_seq, exec_wpush, exec_seq,
        exec_wpop, exec_load, cost_seq, cost_seq, cost_wpush, cost_wpop, cost_load, ← pa_cmpAL,
        (ih _ _ rfl).2]
      simp only [List.length_cons]
      ring

theorem pa_cmpA_run (v : Reg) (s : Stk) :
    pa_Run cmpA v s (nrm { v with ok := v.ok && decide (s.Ab.length = s.P.length) })
      { s with Ab := [], A := s.Ab.reverse ++ s.A, P := [] }
      (4 * s.Ab.length + 2 * s.P.length + 3) := by
  have e : cmpA = Prog.seq pa_cmpAL
      (Prog.seq (wpop .P (fun v o => { v with ok := v.ok && !o.isSome })) (drain .P)) := rfl
  obtain ⟨l1, l2⟩ := pa_cmpAL_spec _ v s rfl
  refine ⟨?_, ?_⟩
  · rw [e, exec_seq, l1, exec_seq, exec_wpop, (drain_spec .P _ _ _ rfl).1]
    refine St_eq _ _ _ _ ?_ ?_
    · simp [nrm, Stk.get]
      exact pa_bool _ _ _
    · simp [Stk.get, Stk.set]
  · rw [e, cost_seq, cost_seq, l1, l2, exec_wpop, cost_wpop, (drain_spec .P _ _ _ rfl).2]
    simp [Stk.set, Stk.get]
    omega

def pa_cmpWL : Pg :=
  forPop .C2b (fun v b => { v with x := b }) id
    (Prog.seq (wpush .C2 (fun v => v.x)) (Prog.seq (wpush .C3 (fun v => v.x))
      (Prog.seq (wpop .P (fun v o => { v with y := o.isSome }))
        (Prog.load fun v => { v with ok := v.ok && v.y }))))

theorem pa_cmpWL_spec (l : List Bool) : ∀ (v : Reg) (s : Stk), s.C2b = l →
    exec pa_cmpWL ⟨v, toFun s⟩ =
        ⟨nrm { v with ok := v.ok && decide (l.length ≤ s.P.length) },
          toFun { s with C2b := [], C2 := l.reverse ++ s.C2, C3 := l.reverse ++ s.C3, P := s.P.drop l.length }⟩ ∧
      cost pa_cmpWL ⟨v, toFun s⟩ = 5 * l.length + 1 := by
  have hnt : NoTouch (K.w W.C2b) (Prog.seq (wpush .C2 (fun v => v.x)) (Prog.seq (wpush .C3 (fun v => v.x))
      (Prog.seq (wpop .P (fun v o => { v with y := o.isSome }))
        (Prog.load fun v => { v with ok := v.ok && v.y })))) := by
    simp [noTouch_seq, noTouch_wpop, noTouch_wpush, noTouch_load]
  induction l with
  | nil =>
    intro v s h
    refine ⟨?_, ?_⟩
    · rw [pa_cmpWL, exec_forPop_nil .C2b _ _ _ v s h]
      refine St_eq _ _ _ _ ?_ ?_
      · simp [nrm]
      · cases s
        simp_all
    · rw [pa_cmpWL, cost_forPop_nil .C2b _ _ _ v s h]; rfl
  | cons x l ih =>
    intro v s h
    refine ⟨?_, ?_⟩
    · rw [pa_cmpWL, exec_forPop_cons .C2b _ _ _ v s x l h hnt, exec_seq, exec_wpush, exec_seq, exec_wpush, exec_seq,
        exec_wpop, exec_load, ← pa_cmpWL, (ih _ _ rfl).1]
      refine St_eq _ _ _ _ ?_ ?_
      · cases hP : s.P <;> simp [nrm, Stk.get, Stk.set, hP]
      · simp [Stk.get, Stk.set]
    · rw [pa_cmpWL, cost_forPop_cons .C2b _ _ _ v s x l h hnt, exec_seq, exec_wpush, exec_seq, exec_wpush, exec_seq,
        exec_wpop, exec_load, cost_seq, cost_seq, cost_seq, cost_wpush, cost_wpush, cost_wpop, cost_load, ← pa_cmpWL,
        (ih _ _ rfl).2]
      simp only [List.length_cons]
      ring

theorem pa_cmpW_run (v : Reg) (s : Stk) :
    pa_Run cmpW v s (nrm { v with ok := v.ok && decide (s.C2b.length = s.P.length) })
      { s with C2b := [], C2 := s.C2b.reverse ++ s.C2, C3 := s.C2b.reverse ++ s.C3, P := [] }
      (5 * s.C2b.length + 2 * s.P.length + 3) := by
  have e : cmpW = Prog.seq pa_cmpWL
      (Prog.seq (wpop .P (fun v o => { v with ok := v.ok && !o.isSome })) (drain .P)) := rfl
  obtain ⟨l1, l2⟩ := pa_cmpWL_spec _ v s rfl
  refine ⟨?_, ?_⟩
  · rw [e, exec_seq, l1, exec_seq, exec_wpop, (drain_spec .P _ _ _ rfl).1]
    refine St_eq _ _ _ _ ?_ ?_
    · simp [nrm, Stk.get]
      exact pa_bool _ _ _
    · simp [Stk.get, Stk.set]
  · rw [e, cost_seq, cost_seq, l1, l2, exec_wpop, cost_wpop, (drain_spec .P _ _ _ rfl).2]
    simp [Stk.set, Stk.get]
    omega

theorem pa_arith (n m k d a w t : ℕ) (ht : t ≤ n + m) :
    11 * k + 3 + (2 * d + 1 + (m * (n * (n * (1 + 4) + 2 + 4) + 2 + 4) + 2 +
      (4 * a + 2 * (m * (n * n)) + 3 +
        (t * (1 + 4) + 2 + (t * (n * (1 + 4) + 2 + 4) + 2 + (5 * w + 2 * (t * n) + 3)))))) ≤
      100 * (n + m + k + d + a + w + 1) ^ 3 := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = n + m + k + d + a + w + 1 := ⟨_, rfl⟩
  rw [← hY]
  have hn : n ≤ Y := by omega
  have hm : m ≤ Y := by omega
  have hk : k ≤ Y := by omega
  have hd : d ≤ Y := by omega
  have ha : a ≤ Y := by omega
  have hw : w ≤ Y := by omega
  have ht' : t ≤ Y := by omega
  have h1 : 1 ≤ Y := by omega
  clear hY ht
  have hmnn : m * (n * n) ≤ Y * (Y * Y) := Nat.mul_le_mul hm (Nat.mul_le_mul hn hn)
  have hmn : m * n ≤ Y * Y := Nat.mul_le_mul hm hn
  have htn : t * n ≤ Y * Y := Nat.mul_le_mul ht' hn
  have hYY : Y * 1 ≤ Y * Y := Nat.mul_le_mul (le_refl Y) h1
  have hYYY : Y * Y * 1 ≤ Y * Y * Y := Nat.mul_le_mul (le_refl (Y * Y)) h1
  nlinarith [hmnn, hmn, htn, hYY, hYYY]

theorem valid_spec (n m k d : ℕ) (ab wb : List Bool) (v : Reg) (s : Stk)
    (hN : s.N = List.replicate n true) (hN2 : s.N2 = List.replicate n true)
    (hT : s.T = List.replicate (n + m) true) (hM : s.M = List.replicate m true)
    (hKc : s.Kc = List.replicate k true) (hD : s.D = List.replicate d true)
    (hAb : s.Ab = ab) (hC2b : s.C2b = wb)
    (hNb : s.Nb = []) (hN2b : s.N2b = []) (hMb : s.Mb = []) (hKb : s.Kb = []) (hTb : s.Tb = [])
    (hT2 : s.T2 = []) (hP : s.P = []) (hA : s.A = []) (hC2 : s.C2 = []) (hC3 : s.C3 = []) :
    exec validP ⟨v, toFun s⟩ =
        ⟨nrm { v with ok := v.ok && decide (k ≤ m) && decide (ab.length = m * n * n) &&
                  decide (wb.length = (n + m - (k + d)) * n) },
          toFun { s with D := [], T := List.replicate (n + m - (k + d)) true,
                                        T2 := List.replicate (n + m - (k + d)) true, Ab := [], A := ab.reverse,
                                        C2b := [], C2 := wb.reverse, C3 := wb.reverse }⟩ ∧
      cost validP ⟨v, toFun s⟩ ≤ 100 * (n + m + k + d + ab.length + wb.length + 1) ^ 3 := by
  obtain ⟨t, ht⟩ : ∃ t, t = n + m - (k + d) := ⟨_, rfl⟩
  have htle : t ≤ n + m := by omega
  rw [← ht]
  have h : pa_Run validP v s _ _ _ :=
    pa_Run_seq (pa_subK_run k m (n + m) v s hKc hM hT hKb hMb)
      (pa_Run_seq (pa_subD_spec (List.replicate d true) _ _ hD)
        (pa_Run_seq (pa_prodA_run n m _ _ hM hMb hN hNb hN2 hN2b)
          (pa_Run_seq (pa_cmpA_run _ _)
            (pa_Run_seq (pa_copyT_run t _ _ (by simp [Stk.get, Stk.set, ht, Nat.sub_sub]) hTb)
              (pa_Run_seq (pa_prodW_run t n _ _ (by simp [Stk.get, Stk.set, ht, Nat.sub_sub]) hTb hN hNb)
                (pa_cmpW_run _ _))))))
  refine ⟨h.1.trans (St_eq _ _ _ _ ?_ ?_), le_trans h.2 ?_⟩
  · simp [nrm, Stk.get, Stk.set, hAb, hC2b, hP, Nat.mul_assoc]
  · simp [Stk.get, Stk.set, hAb, hC2b, hP, hA, hC2, hC3, hT2]
    omega
  · simp only [Stk.get, Stk.set, hAb, hC2b, hP, List.length_append, List.length_replicate,
      List.length_nil, Nat.add_zero, Nat.mul_one]
    exact pa_arith n m k d ab.length wb.length t htle

end

section
open Turing

theorem tp_initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

theorem tp_haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

theorem wf_wpush (a : W) (f : Reg → Bool) : WF (wpush a f) ↔ True := Iff.rfl

theorem wf_wpop (a : W) (f : Reg → Option Bool → Reg) : WF (wpop a f) ↔ True := Iff.rfl

theorem wf_load (f : Reg → Reg) : WF (Prog.load f : Pg) ↔ True := Iff.rfl

theorem wf_seq (p q : Pg) : WF (Prog.seq p q) ↔ WF p ∧ WF q := Iff.rfl

theorem wf_ite (c : Reg → Bool) (p q : Pg) : WF (Prog.ite c p q) ↔ WF p ∧ WF q := Iff.rfl

theorem wf_forPop (a : W) (f : Reg → Bool → Reg) (g : Reg → Reg) (body : Pg) :
    WF (forPop a f g body) ↔ NoTouch (K.w a) body ∧ WF body := by
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨fun v => rfl, h⟩

theorem wf_move (a b : W) : WF (move a b) ↔ K.w b ≠ K.w a := by
  rw [move, wf_forPop, noTouch_wpush, wf_wpush]; simp

theorem wf_drain (a : W) : WF (drain a) ↔ True := by
  rw [drain, wf_forPop, noTouch_load, wf_load]; simp

theorem wf_forC (c cb : W) (body : Pg) :
    WF (forC c cb body) ↔
      ((K.w cb ≠ K.w c ∧ NoTouch (K.w c) body) ∧ WF body) ∧ K.w c ≠ K.w cb := by
  rw [forC, wf_seq, wf_forPop, noTouch_seq, noTouch_wpush, wf_seq, wf_wpush, wf_move]; simp

theorem wf_parseLoop : WF parseLoop := by
  refine ⟨fun v => rfl, ?_, ?_⟩
  · simp [parseBody, noTouch_seq, noTouch_wpush, noTouch_load, noTouch_ite]
  · simp [parseBody, wf_seq, wf_wpush, wf_load, wf_ite]

theorem wf_prog : WF prog := by
  simp only [prog, wf_seq, wf_ite, wf_load, parseP, and_true]
  refine ⟨wf_parseLoop, ?_, ?_, ?_⟩
  · simp [validP, subK, subD, prodA, cmpA, copyT, prodW, cmpW, wf_seq, wf_wpush, wf_wpop, wf_load,
      wf_ite, wf_forPop, wf_move, wf_drain, wf_forC, noTouch_seq, noTouch_wpush, noTouch_wpop,
      noTouch_load, noTouch_ite, noTouch_forPop, noTouch_move, noTouch_drain, noTouch_forC]
  · simp [mainP, phase2, phase3, colP, pairP, cmpRK, cmpRT, loadV, loadI, loadJ, maskP, maskRow,
      dotsP, dotLoop, insertP, reduceP, scanLoop, nzLoop, wf_seq, wf_wpush, wf_wpop, wf_load,
      wf_ite, wf_forPop, wf_move, wf_drain, wf_forC, noTouch_seq, noTouch_wpush, noTouch_wpop,
      noTouch_load, noTouch_ite, noTouch_forPop, noTouch_move, noTouch_drain, noTouch_forC]
  · simp [drainAll, wf_seq, wf_drain]

def finalStmt : TM2.Stmt Γ (Option (Pos prog)) Reg :=
  TM2.Stmt.push K.out (fun v => v.res) (TM2.Stmt.load (fun _ => regInit) TM2.Stmt.halt)

noncomputable def tm397 : FinTM2 where
  K := K
  k₀ := K.inp
  k₁ := K.out
  Γ := Γ
  Λ := Option (Pos prog)
  main := some (entry prog)
  σ := Reg
  initialState := regInit
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := fun l => match l with
    | some a => stmt prog some none a
    | none => finalStmt

theorem toFun_emp : toFun emp = fun _ => [] := by
  funext k
  cases k with
  | inp => rfl
  | out => rfl
  | w a => cases a <;> rfl

def tB (N : ℕ) : ℕ := 400 * (N + 1) ^ 5

def inStk (x w : List Bool) : Stk := { emp with inp := x.map Sum.inl ++ w.map Sum.inr }

theorem tm397_run (x w : List Bool) (v' : Reg)
    (h : exec prog ⟨regInit, toFun (inStk x w)⟩ = ⟨v', toFun emp⟩) :
    (flip bind tm397.step)^[1 + cost prog ⟨regInit, toFun (inStk x w)⟩]
        (some (initList tm397 (x.map Sum.inl ++ w.map Sum.inr))) =
      some (haltList tm397 [v'.res]) := by
  have h0 : initList tm397 (x.map Sum.inl ++ w.map Sum.inr) =
      (⟨some (some (entry prog)), regInit, toFun (inStk x w)⟩ : TM2.Cfg Γ (Option (Pos prog)) Reg) := by
    rw [tp_initList_eq]
    have e : Function.update (fun _ => []) K.inp (x.map Sum.inl ++ w.map Sum.inr) =
        toFun (inStk x w) := by
      rw [← toFun_emp]
      exact update_toFun_inp emp _
    exact congrArg (TM2.Cfg.mk (some (some (entry prog))) regInit) e
  have h1 : (flip bind (TM2.step tm397.m))^[cost prog ⟨regInit, toFun (inStk x w)⟩]
      (some (⟨some (some (entry prog)), regInit, toFun (inStk x w)⟩ :
        TM2.Cfg Γ (Option (Pos prog)) Reg)) =
      some ⟨some none, (exec prog ⟨regInit, toFun (inStk x w)⟩).var,
        (exec prog ⟨regInit, toFun (inStk x w)⟩).stk⟩ :=
    compile_correct (M := tm397.m) prog wf_prog some none (fun a => rfl)
      ⟨regInit, toFun (inStk x w)⟩
  rw [h] at h1
  rw [h0]
  refine iter_add _ 1 _ _ _ _ h1 ?_
  refine (one_step tm397.m none v' (toFun emp) finalStmt _ rfl rfl).trans ?_
  rw [tp_haltList_eq]
  simp only [finalStmt, TM2.stepAux, toFun_emp]
  rfl

end

section
open Turing

theorem tp_cl_nrm (v : Reg) (h1 : v.acc = false) (h2 : v.m0 = false) (h3 : v.m1 = false) :
    cl v = nrm v := by
  cases v
  simp_all [cl, nrm]

theorem tp_ins_length_le (Bl : List (List Bool)) (v : List Bool) :
    (ins Bl v).length ≤ Bl.length + 1 := by
  unfold ins
  split <;> simp

theorem tp_ins_len (L : ℕ) (Bl : List (List Bool)) (v : List Bool)
    (hB : ∀ b ∈ Bl, b.length = L) (hv : v.length = L) : ∀ b ∈ ins Bl v, b.length = L := by
  unfold ins
  split
  · intro b hb
    rcases List.mem_append.mp hb with h | h
    · exact hB b h
    · simp only [List.mem_singleton] at h
      rw [h, rk_reduce_len]; exact hv
  · exact hB

theorem tp_rev_split (n : ℕ) (l r : List Bool) :
    (l.drop n).reverse ++ ((l.take n).reverse ++ r) = l.reverse ++ r := by
  rw [← List.append_assoc, ← List.reverse_append, List.take_append_drop]

theorem tp_p2body (n : ℕ) (Bl : List (List Bool)) (v : Reg) (s : Stk)
    (hN : s.N = List.replicate n true) (hNb : s.Nb = []) (hlen : n ≤ s.C2.length)
    (hVb : s.Vb = []) (hV : s.V = []) (hB : s.B = Bl.flatten)
    (hR : s.R = List.replicate Bl.length true) (hBl : ∀ b ∈ Bl, b.length = n)
    (hRb : s.Rb = []) (hBb : s.Bb = []) :
    exec (Prog.seq loadV insertP) ⟨v, toFun s⟩ =
        ⟨cl v, toFun { s with C2 := s.C2.drop n, C2b := (s.C2.take n).reverse ++ s.C2b, B := (ins Bl (s.C2.take n)).flatten, R := List.replicate (ins Bl (s.C2.take n)).length true }⟩ ∧
      cost (Prog.seq loadV insertP) ⟨v, toFun s⟩ ≤ 9 * n + 3 + 16 * (Bl.length + 1) * (n + 1) := by
  have h1 := loadV_spec n v s hN hNb hlen hVb hV
  have h2 := insert_spec Bl (nrm v)
    { s with C2 := s.C2.drop n, C2b := (s.C2.take n).reverse ++ s.C2b, V := s.C2.take n }
    hB hR (fun b hb => by
      show b.length = (s.C2.take n).length
      rw [List.length_take, min_eq_left hlen]; exact hBl b hb) hRb hBb hVb
  refine ⟨?_, ?_⟩
  · rw [exec_seq, h1.1]
    refine h2.1.trans (St_eq _ _ _ _ rfl ?_)
    cases s
    simp_all
  · rw [cost_seq, h1.1]
    have h3 := h2.2
    have h4 := h1.2
    simp only [List.length_take, min_eq_left hlen] at h3
    omega

def tp_p2loop : Pg :=
  forPop .T (fun v _ => v) id (Prog.seq (wpush .Tb (fun _ => true)) (Prog.seq loadV insertP))

theorem tp_p2loop_nt :
    NoTouch (K.w W.T) (Prog.seq (wpush .Tb (fun _ => true)) (Prog.seq loadV insertP)) := by
  simp [loadV, insertP, reduceP, scanLoop, nzLoop, noTouch_seq, noTouch_wpop, noTouch_wpush,
    noTouch_load, noTouch_forPop, noTouch_move, noTouch_drain, noTouch_forC, noTouch_ite]

theorem tp_p2loop_spec (n : ℕ) : ∀ (j : ℕ) (Bl : List (List Bool)) (v : Reg) (s : Stk),
    s.T = List.replicate j true → s.N = List.replicate n true → s.Nb = [] →
    s.C2.length = j * n → s.V = [] → s.Vb = [] → s.B = Bl.flatten →
    s.R = List.replicate Bl.length true → (∀ b ∈ Bl, b.length = n) → s.Rb = [] → s.Bb = [] →
    v.acc = false → v.m0 = false → v.m1 = false →
    exec tp_p2loop ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with T := [], Tb := List.replicate j true ++ s.Tb, C2 := [], C2b := s.C2.reverse ++ s.C2b, B := ((chunk n j s.C2).foldl ins Bl).flatten, R := List.replicate ((chunk n j s.C2).foldl ins Bl).length true }⟩ ∧
      ∀ rb, Bl.length + j ≤ rb →
        cost tp_p2loop ⟨v, toFun s⟩ ≤ j * (9 * n + 5 + 16 * (rb + 1) * (n + 1)) + 1
  | 0, Bl, v, s, hT, hN, hNb, hC2, hV, hVb, hB, hR, hBl, hRb, hBb, ha, hm0, hm1 => by
    have hC2' : s.C2 = [] := List.length_eq_zero_iff.mp (by simpa using hC2)
    refine ⟨?_, ?_⟩
    · rw [tp_p2loop, exec_forPop_nil .T _ _ _ v s hT]
      refine St_eq _ _ _ _ rfl ?_
      cases s
      simp_all [chunk]
    · intro rb _
      rw [tp_p2loop, cost_forPop_nil .T _ _ _ v s hT]; simp
  | j + 1, Bl, v, s, hT, hN, hNb, hC2, hV, hVb, hB, hR, hBl, hRb, hBb, ha, hm0, hm1 => by
    have hT' : s.get .T = true :: List.replicate j true := by
      simp only [Stk.get, hT, List.replicate_succ]
    have hlen : n ≤ s.C2.length := by rw [hC2, Nat.succ_mul]; omega
    have hb := tp_p2body n Bl { v with go := true }
      { s with T := List.replicate j true, Tb := true :: s.Tb } hN hNb hlen hVb hV hB hR hBl hRb hBb
    have hi := tp_p2loop_spec n j (ins Bl (s.C2.take n)) (cl { v with go := true })
      { s with T := List.replicate j true, Tb := true :: s.Tb, C2 := s.C2.drop n, C2b := (s.C2.take n).reverse ++ s.C2b, B := (ins Bl (s.C2.take n)).flatten, R := List.replicate (ins Bl (s.C2.take n)).length true }
      rfl hN hNb (by
        show (s.C2.drop n).length = j * n
        rw [List.length_drop, hC2, Nat.succ_mul]; omega) hV hVb rfl rfl
      (tp_ins_len n Bl _ hBl (by rw [List.length_take, min_eq_left hlen])) hRb hBb rfl rfl rfl
    refine ⟨?_, ?_⟩
    · rw [tp_p2loop, exec_forPop_cons .T _ _ _ v s true _ hT' tp_p2loop_nt]
      simp only [exec_seq, exec_wpush, Stk.get, Stk.set]
      rw [← tp_p2loop]
      have hb1 := hb.1
      simp only [exec_seq] at hb1
      refine (congrArg (exec tp_p2loop) hb1).trans ?_
      refine hi.1.trans ?_
      refine St_eq _ _ _ _ (by cases v; simp_all [nrm, cl]) ?_
      simp [chunk, tp_rev_split, List.replicate_succ, in_rep]
    · intro rb hrb
      rw [tp_p2loop, cost_forPop_cons .T _ _ _ v s true _ hT' tp_p2loop_nt]
      simp only [exec_seq, exec_wpush, cost_seq, cost_wpush, Stk.get, Stk.set]
      rw [← tp_p2loop]
      have hb1 := hb.1
      have hb2 := hb.2
      simp only [exec_seq, cost_seq] at hb1 hb2
      rw [hb1]
      have h5 := hi.2 rb (by have := tp_ins_length_le Bl (s.C2.take n); omega)
      have hmono : 16 * (Bl.length + 1) * (n + 1) ≤ 16 * (rb + 1) * (n + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      have e : (j + 1) * (9 * n + 5 + 16 * (rb + 1) * (n + 1)) =
          j * (9 * n + 5 + 16 * (rb + 1) * (n + 1)) + (9 * n + 5 + 16 * (rb + 1) * (n + 1)) := by
        ring
      rw [e]
      omega

end

section
open Turing

theorem tp_foldl_ins_length : ∀ (vs : List (List Bool)) (Bl : List (List Bool)),
    (vs.foldl ins Bl).length ≤ Bl.length + vs.length
  | [], Bl => by simp
  | v :: vs, Bl => by
    have h1 := tp_foldl_ins_length vs (ins Bl v)
    have h2 := tp_ins_length_le Bl v
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem tp_foldl_ins_len (L : ℕ) : ∀ (vs : List (List Bool)) (Bl : List (List Bool)),
    (∀ b ∈ Bl, b.length = L) → (∀ v ∈ vs, v.length = L) → ∀ b ∈ vs.foldl ins Bl, b.length = L
  | [], Bl, hB, _ => by simpa using hB
  | v :: vs, Bl, hB, hv => by
    simp only [List.foldl_cons]
    exact tp_foldl_ins_len L vs (ins Bl v) (tp_ins_len L Bl v hB (hv v (by simp)))
      (fun u hu => hv u (by simp [hu]))

theorem tp_drop_rep (r t : ℕ) (h : r ≤ t) : (List.replicate r true).drop t = [] := by
  rw [List.drop_eq_nil_iff, List.length_replicate]; exact h

def Run (p : Pg) (v : Reg) (s : Stk) (v' : Reg) (s' : Stk) (c : ℕ) : Prop :=
  exec p ⟨v, toFun s⟩ = ⟨v', toFun s'⟩ ∧ cost p ⟨v, toFun s⟩ ≤ c

theorem Run.ofEq {p : Pg} {v : Reg} {s : Stk} {v' : Reg} {s' : Stk} {c : ℕ}
    (h : exec p ⟨v, toFun s⟩ = ⟨v', toFun s'⟩ ∧ cost p ⟨v, toFun s⟩ = c) : Run p v s v' s' c :=
  ⟨h.1, le_of_eq h.2⟩

theorem Run.seq {p q : Pg} {v v1 v2 : Reg} {s s1 s2 : Stk} {c1 c2 : ℕ}
    (h1 : Run p v s v1 s1 c1) (h2 : Run q v1 s1 v2 s2 c2) :
    Run (Prog.seq p q) v s v2 s2 (c1 + c2) := by
  refine ⟨?_, ?_⟩
  · rw [exec_seq, h1.1, h2.1]
  · rw [cost_seq, h1.1]
    have := h1.2
    have := h2.2
    omega

theorem Run.conv {p : Pg} {v v' v'' : Reg} {s s' s'' : Stk} {c c' : ℕ}
    (h : Run p v s v' s' c) (hv : v' = v'') (hs : s' = s'') (hc : c ≤ c') :
    Run p v s v'' s'' c' := by
  subst hv hs
  exact ⟨h.1, le_trans h.2 hc⟩

theorem Run.load (f : Reg → Reg) (v : Reg) (s : Stk) : Run (Prog.load f) v s (f v) s 1 :=
  ⟨rfl, le_refl 1⟩

theorem Run.ite_true {c : Reg → Bool} {p q : Pg} {v v' : Reg} {s s' : Stk} {n : ℕ}
    (hc : c v = true) (h : Run p v s v' s' n) : Run (Prog.ite c p q) v s v' s' (n + 1) := by
  refine ⟨?_, ?_⟩
  · simpa [exec_ite, hc] using h.1
  · simpa [cost_ite, hc] using h.2

theorem Run.ite_false {c : Reg → Bool} {p q : Pg} {v v' : Reg} {s s' : Stk} {n : ℕ}
    (hc : c v = false) (h : Run q v s v' s' n) : Run (Prog.ite c p q) v s v' s' (n + 1) := by
  refine ⟨?_, ?_⟩
  · simpa [exec_ite, hc] using h.1
  · simpa [cost_ite, hc] using h.2

theorem Run.move (a b : W) (hab : a ≠ b) (v : Reg) (s : Stk) :
    Run (move a b) v s (nrm v) ((s.set a []).set b ((s.get a).reverse ++ s.get b))
      (2 * (s.get a).length + 1) :=
  Run.ofEq (move_spec a b hab (s.get a) v s rfl)

theorem Run.drain (a : W) (v : Reg) (s : Stk) :
    Run (drain a) v s (nrm v) (s.set a []) (2 * (s.get a).length + 1) :=
  Run.ofEq (drain_spec a (s.get a) v s rfl)

theorem phase2_eq : phase2 = Prog.seq (Prog.seq tp_p2loop (move .Tb .T))
    (Prog.seq (move .C2b .C2) (Prog.seq cmpRT (Prog.seq (drain .R) (drain .B)))) := rfl

theorem phase2_spec (n t : ℕ) (v : Reg) (s : Stk)
    (hT : s.T = List.replicate t true) (hTb : s.Tb = []) (hN : s.N = List.replicate n true)
    (hNb : s.Nb = []) (hC2 : s.C2.length = t * n) (hC2b : s.C2b = []) (hV : s.V = [])
    (hVb : s.Vb = []) (hB : s.B = []) (hR : s.R = []) (hRb : s.Rb = []) (hBb : s.Bb = [])
    (ha : v.acc = false) (hm0 : v.m0 = false) (hm1 : v.m1 = false) :
    Run phase2 v s (nrm { v with res := decide (t ≤ (basisOf (chunk n t s.C2)).length) }) s
      (t * (9 * n + 5 + 16 * (t + 1) * (n + 1)) + 4 * (t * n) + 10 * t + 9) := by
  have h1 := tp_p2loop_spec n t [] v s hT hN hNb hC2 hV hVb (by simpa using hB)
    (by simpa using hR) (by simp) hRb hBb ha hm0 hm1
  have hlenB : (basisOf (chunk n t s.C2)).length ≤ t := by
    have := tp_foldl_ins_length (chunk n t s.C2) []
    rw [rl_chunk_length] at this
    simpa [basisOf] using this
  have hBl : ∀ b ∈ basisOf (chunk n t s.C2), b.length = n :=
    tp_foldl_ins_len n (chunk n t s.C2) [] (by simp) (rl_chunk_mem_length n t s.C2 hC2)
  have hflat := in_flatten_len n (basisOf (chunk n t s.C2)) hBl
  have hmul : (basisOf (chunk n t s.C2)).length * n ≤ t * n := Nat.mul_le_mul_right n hlenB
  have hbo : (chunk n t s.C2).foldl ins [] = basisOf (chunk n t s.C2) := rfl
  rw [phase2_eq]
  refine Run.conv (Run.seq (Run.seq ⟨h1.1, h1.2 t (by simp)⟩ (Run.move .Tb .T (by decide) _ _))
    (Run.seq (Run.move .C2b .C2 (by decide) _ _)
      (Run.seq (cmpRT_spec t _ _ ?_ ?_)
        (Run.seq (Run.drain .R _ _) (Run.drain .B _ _))))) ?_ ?_ ?_
  · simp [Stk.set, Stk.get, hTb]
  · simp [Stk.set, Stk.get, hTb]
  · obtain ⟨go, tag, x, y, u, w, acc, m0, m1, ph, ok, res⟩ := v
    simp only at ha
    subst ha
    simp [nrm, basisOf, Stk.set, Stk.get]
    rfl
  · simp only [Stk.set, Stk.get, hbo, hTb, hC2b, List.append_nil, List.reverse_replicate,
      List.reverse_reverse, List.length_replicate, tp_drop_rep _ _ hlenB]
    cases s
    simp_all
  · simp only [Stk.set, Stk.get, hbo, hTb, hC2b, List.append_nil, List.reverse_replicate,
      List.reverse_reverse, List.length_replicate, tp_drop_rep _ _ hlenB, List.length_reverse,
      hflat, hC2, List.length_nil]
    omega

end

section
open Turing

theorem tp_flatMap_len {α β : Type} (c : ℕ) : ∀ (l : List α) (f : α → List β),
    (∀ a ∈ l, (f a).length = c) → (l.flatMap f).length = l.length * c
  | [], _, _ => by simp
  | a :: l, f, h => by
    have h1 := tp_flatMap_len c l f (fun b hb => h b (by simp [hb]))
    have h2 := h a (by simp)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, h1, h2]
    ring

theorem tp_mask_len (ci cj : List Bool) (h : ci.length = cj.length) :
    (mask ci cj).length = ci.length * ci.length := by
  unfold mask
  rw [tp_flatMap_len (ci.zip cj).length]
  · simp [List.length_zip, h]
  · intro a _; simp

def tp_pairC (n m rb : ℕ) : ℕ :=
  (10 * n + 3) + 11 * (n + 1) ^ 2 + (2 * n + 1) + 10 * (m + 1) * (n * n + 1) +
    (2 * (n * n) + 1) + 16 * (rb + 1) * (m + 1)

theorem tp_pairC_mono (n m r rb : ℕ) (h : r ≤ rb) : tp_pairC n m r ≤ tp_pairC n m rb := by
  unfold tp_pairC
  have : 16 * (r + 1) * (m + 1) ≤ 16 * (rb + 1) * (m + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  omega

theorem tp_pair_spec (n m : ℕ) (Bl : List (List Bool)) (v : Reg) (s : Stk)
    (hN : s.N = List.replicate n true) (hNb : s.Nb = []) (hM : s.M = List.replicate m true)
    (hMb : s.Mb = []) (hC2 : n ≤ s.C2.length) (hCI : s.CI.length = n) (hCI2 : s.CI2 = s.CI)
    (hA : m * (n * n) ≤ s.A.length) (hCJ : s.CJ = []) (hCJ2 : s.CJ2 = []) (hCJ2b : s.CJ2b = [])
    (hCIb : s.CIb = []) (hCI2b : s.CI2b = []) (hZ : s.Z = []) (hZb : s.Zb = []) (hAb : s.Ab = [])
    (hV : s.V = []) (hVb : s.Vb = []) (hB : s.B = Bl.flatten)
    (hR : s.R = List.replicate Bl.length true) (hBl : ∀ b ∈ Bl, b.length = m)
    (hRb : s.Rb = []) (hBb : s.Bb = []) :
    Run pairP v s (cl v)
      { s with C2 := s.C2.drop n, C2b := (s.C2.take n).reverse ++ s.C2b, B := (ins Bl (dots (mask s.CI (s.C2.take n)) m s.A)).flatten, R := List.replicate (ins Bl (dots (mask s.CI (s.C2.take n)) m s.A)).length true }
      (tp_pairC n m Bl.length) := by
  have hml : (mask s.CI (s.C2.take n)).length = n * n := by
    rw [tp_mask_len _ _ (by rw [List.length_take, min_eq_left hC2, hCI]), hCI]
  rw [pairP]
  refine Run.conv (Run.seq (loadJ_spec n _ _ hN hNb hC2 hCJ2b hCJ hCJ2)
    (Run.seq (mask_spec _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      (Run.seq (Run.drain .CJ2 _ _)
        (Run.seq (dots_spec m _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          (Run.seq (Run.drain .Z _ _) (insert_spec Bl _ _ ?_ ?_ ?_ ?_ ?_ ?_)))))) ?_ ?_ ?_
  · exact hCI2
  · rfl
  · show s.CI.length = (s.C2.take n).length
    rw [List.length_take, min_eq_left hC2, hCI]
  · exact hCIb
  · exact hCI2b
  · exact hCJ2b
  · exact hZb
  · exact hZ
  · exact hM
  · show m * (mask s.CI (s.C2.take n)).length ≤ s.A.length
    rw [hml]; exact hA
  · exact hMb
  · exact hZb
  · exact hAb
  · exact hVb
  · exact hV
  · exact hB
  · exact hR
  · intro b hb
    show b.length = (dots (mask s.CI (s.C2.take n)) m s.A).length
    rw [rl_dots_length]; exact hBl b hb
  · exact hRb
  · exact hBb
  · exact hVb
  · cases v
    simp [cl, nrm]
  · simp only [Stk.set, Stk.get]
    cases s
    simp_all
  · simp only [Stk.set, Stk.get, hml, rl_dots_length, List.length_take, min_eq_left hC2, hCI]
    unfold tp_pairC
    omega

def tp_p3in : Pg :=
  forPop .T2 (fun v _ => v) id (Prog.seq (wpush .T2b (fun _ => true)) pairP)

theorem tp_p3in_nt : NoTouch (K.w W.T2) (Prog.seq (wpush .T2b (fun _ => true)) pairP) := by
  simp [pairP, loadJ, maskP, maskRow, dotsP, dotLoop, insertP, reduceP, scanLoop, nzLoop,
    noTouch_seq, noTouch_wpop, noTouch_wpush, noTouch_load, noTouch_forPop, noTouch_move,
    noTouch_drain, noTouch_forC, noTouch_ite]

theorem tp_p3in_spec (n m : ℕ) : ∀ (j : ℕ) (Bl : List (List Bool)) (v : Reg) (s : Stk),
    s.T2 = List.replicate j true → s.N = List.replicate n true → s.Nb = [] →
    s.M = List.replicate m true → s.Mb = [] → s.C2.length = j * n → s.CI.length = n →
    s.CI2 = s.CI → m * (n * n) ≤ s.A.length → s.CJ = [] → s.CJ2 = [] → s.CJ2b = [] →
    s.CIb = [] → s.CI2b = [] → s.Z = [] → s.Zb = [] → s.Ab = [] → s.V = [] → s.Vb = [] →
    s.B = Bl.flatten → s.R = List.replicate Bl.length true → (∀ b ∈ Bl, b.length = m) →
    s.Rb = [] → s.Bb = [] → v.acc = false → v.m0 = false → v.m1 = false →
    exec tp_p3in ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with T2 := [], T2b := List.replicate j true ++ s.T2b, C2 := [], C2b := s.C2.reverse ++ s.C2b, B := (((chunk n j s.C2).map (fun cj => dots (mask s.CI cj) m s.A)).foldl ins Bl).flatten, R := List.replicate (((chunk n j s.C2).map (fun cj => dots (mask s.CI cj) m s.A)).foldl ins Bl).length true }⟩ ∧
      ∀ rb, Bl.length + j ≤ rb → cost tp_p3in ⟨v, toFun s⟩ ≤ j * (tp_pairC n m rb + 2) + 1
  | 0, Bl, v, s, hT2, hN, hNb, hM, hMb, hC2, hCI, hCI2, hA, hCJ, hCJ2, hCJ2b, hCIb, hCI2b, hZ, hZb,
      hAb, hV, hVb, hB, hR, hBl, hRb, hBb, ha, hm0, hm1 => by
    have hC2' : s.C2 = [] := List.length_eq_zero_iff.mp (by simpa using hC2)
    refine ⟨?_, ?_⟩
    · rw [tp_p3in, exec_forPop_nil .T2 _ _ _ v s hT2]
      refine St_eq _ _ _ _ rfl ?_
      cases s
      simp_all [chunk]
    · intro rb _
      rw [tp_p3in, cost_forPop_nil .T2 _ _ _ v s hT2]; simp
  | j + 1, Bl, v, s, hT2, hN, hNb, hM, hMb, hC2, hCI, hCI2, hA, hCJ, hCJ2, hCJ2b, hCIb, hCI2b, hZ,
      hZb, hAb, hV, hVb, hB, hR, hBl, hRb, hBb, ha, hm0, hm1 => by
    have hT' : s.get .T2 = true :: List.replicate j true := by
      simp only [Stk.get, hT2, List.replicate_succ]
    have hlen : n ≤ s.C2.length := by rw [hC2, Nat.succ_mul]; omega
    have hb := tp_pair_spec n m Bl { v with go := true }
      { s with T2 := List.replicate j true, T2b := true :: s.T2b } hN hNb hM hMb hlen hCI hCI2 hA
      hCJ hCJ2 hCJ2b hCIb hCI2b hZ hZb hAb hV hVb hB hR hBl hRb hBb
    have hi := tp_p3in_spec n m j (ins Bl (dots (mask s.CI (s.C2.take n)) m s.A))
      (cl { v with go := true })
      { s with T2 := List.replicate j true, T2b := true :: s.T2b, C2 := s.C2.drop n, C2b := (s.C2.take n).reverse ++ s.C2b, B := (ins Bl (dots (mask s.CI (s.C2.take n)) m s.A)).flatten, R := List.replicate (ins Bl (dots (mask s.CI (s.C2.take n)) m s.A)).length true }
      rfl hN hNb hM hMb (by
        show (s.C2.drop n).length = j * n
        rw [List.length_drop, hC2, Nat.succ_mul]; omega) hCI hCI2 hA hCJ hCJ2 hCJ2b hCIb hCI2b hZ
      hZb hAb hV hVb rfl rfl (tp_ins_len m Bl _ hBl (rl_dots_length _ _ _)) hRb hBb rfl rfl rfl
    refine ⟨?_, ?_⟩
    · rw [tp_p3in, exec_forPop_cons .T2 _ _ _ v s true _ hT' tp_p3in_nt]
      simp only [exec_seq, exec_wpush, Stk.get, Stk.set]
      rw [← tp_p3in]
      refine (congrArg (exec tp_p3in) hb.1).trans ?_
      refine hi.1.trans ?_
      refine St_eq _ _ _ _ (by cases v; simp_all [nrm, cl]) ?_
      simp [chunk, tp_rev_split, List.replicate_succ, in_rep]
    · intro rb hrb
      rw [tp_p3in, cost_forPop_cons .T2 _ _ _ v s true _ hT' tp_p3in_nt]
      simp only [exec_seq, exec_wpush, cost_seq, cost_wpush, Stk.get, Stk.set]
      rw [← tp_p3in]
      have hb1 := hb.1
      have hb2 := hb.2
      dsimp only at hb1 hb2
      rw [hb1]
      have h5 := hi.2 rb (by
        have := tp_ins_length_le Bl (dots (mask s.CI (s.C2.take n)) m s.A); omega)
      have hmono := tp_pairC_mono n m Bl.length rb (by omega)
      have e : (j + 1) * (tp_pairC n m rb + 2) =
          j * (tp_pairC n m rb + 2) + (tp_pairC n m rb + 2) := by ring
      rw [e]
      omega

end

section
open Turing

theorem colP_eq : colP = Prog.seq loadI (Prog.seq (Prog.seq tp_p3in (move .T2b .T2))
    (Prog.seq (move .C2b .C2) (Prog.seq (drain .CI) (drain .CI2)))) := rfl

def tp_colC (n m t rb : ℕ) : ℕ :=
  (9 * n + 3) + (t * (tp_pairC n m rb + 2) + 1) + (2 * t + 1) + (2 * (t * n) + 1) + (2 * n + 1) +
    (2 * n + 1)

theorem tp_colC_mono (n m t r rb : ℕ) (h : r ≤ rb) : tp_colC n m t r ≤ tp_colC n m t rb := by
  unfold tp_colC
  have : t * (tp_pairC n m r + 2) ≤ t * (tp_pairC n m rb + 2) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (tp_pairC_mono n m r rb h) 2)
  omega

theorem tp_col_spec (n m t : ℕ) (Bl : List (List Bool)) (v : Reg) (s : Stk) (rb : ℕ)
    (hrb : Bl.length + t ≤ rb)
    (hT2 : s.T2 = List.replicate t true) (hT2b : s.T2b = [])
    (hN : s.N = List.replicate n true) (hNb : s.Nb = [])
    (hM : s.M = List.replicate m true) (hMb : s.Mb = []) (hC3 : n ≤ s.C3.length)
    (hC2 : s.C2.length = t * n) (hC2b : s.C2b = []) (hCI : s.CI = []) (hCI2 : s.CI2 = [])
    (hA : m * (n * n) ≤ s.A.length) (hCJ : s.CJ = []) (hCJ2 : s.CJ2 = []) (hCJ2b : s.CJ2b = [])
    (hCIb : s.CIb = []) (hCI2b : s.CI2b = []) (hZ : s.Z = []) (hZb : s.Zb = []) (hAb : s.Ab = [])
    (hV : s.V = []) (hVb : s.Vb = []) (hB : s.B = Bl.flatten)
    (hR : s.R = List.replicate Bl.length true) (hBl : ∀ b ∈ Bl, b.length = m)
    (hRb : s.Rb = []) (hBb : s.Bb = [])
    (ha : v.acc = false) (hm0 : v.m0 = false) (hm1 : v.m1 = false) :
    Run colP v s (nrm v)
      { s with C3 := s.C3.drop n, B := (((chunk n t s.C2).map (fun cj => dots (mask (s.C3.take n) cj) m s.A)).foldl ins Bl).flatten, R := List.replicate (((chunk n t s.C2).map (fun cj => dots (mask (s.C3.take n) cj) m s.A)).foldl ins Bl).length true }
      (tp_colC n m t rb) := by
  have h1 := loadI_spec n v s hN hNb hC3 hCIb hCI hCI2
  have h2 := tp_p3in_spec n m t Bl (nrm v)
    { s with C3 := s.C3.drop n, CI := s.C3.take n, CI2 := s.C3.take n }
    hT2 hN hNb hM hMb hC2 (by
      show (s.C3.take n).length = n
      rw [List.length_take, min_eq_left hC3]) rfl hA hCJ hCJ2 hCJ2b hCIb hCI2b hZ hZb hAb hV hVb
    hB hR hBl hRb hBb ha hm0 hm1
  rw [colP_eq]
  refine Run.conv (Run.seq h1 (Run.seq (Run.seq ⟨h2.1, h2.2 rb hrb⟩ (Run.move .T2b .T2 (by decide) _ _))
    (Run.seq (Run.move .C2b .C2 (by decide) _ _)
      (Run.seq (Run.drain .CI _ _) (Run.drain .CI2 _ _))))) ?_ ?_ ?_
  · cases v
    simp [nrm]
  · simp only [Stk.set, Stk.get, hT2b, hC2b, List.append_nil, List.reverse_replicate,
      List.reverse_reverse]
    cases s
    simp_all
  · simp only [Stk.set, Stk.get, hT2b, hC2b, List.append_nil, List.reverse_replicate,
      List.reverse_reverse, List.length_replicate, List.length_reverse, hC2, List.length_take,
      min_eq_left hC3]
    unfold tp_colC
    omega

def tp_p3out : Pg :=
  forPop .T (fun v _ => v) id (Prog.seq (wpush .Tb (fun _ => true)) colP)

theorem tp_p3out_nt : NoTouch (K.w W.T) (Prog.seq (wpush .Tb (fun _ => true)) colP) := by
  simp [colP, pairP, loadI, loadJ, maskP, maskRow, dotsP, dotLoop, insertP, reduceP, scanLoop,
    nzLoop, noTouch_seq, noTouch_wpop, noTouch_wpush, noTouch_load, noTouch_forPop, noTouch_move,
    noTouch_drain, noTouch_forC, noTouch_ite]

theorem phase3_eq : phase3 = Prog.seq (Prog.seq tp_p3out (move .Tb .T)) cmpRK := rfl

theorem tp_p3out_spec (n m t : ℕ) : ∀ (i : ℕ) (Bl : List (List Bool)) (v : Reg) (s : Stk),
    s.T = List.replicate i true → s.C3.length = i * n →
    s.T2 = List.replicate t true → s.T2b = [] →
    s.N = List.replicate n true → s.Nb = [] →
    s.M = List.replicate m true → s.Mb = [] →
    s.C2.length = t * n → s.C2b = [] → s.CI = [] → s.CI2 = [] →
    m * (n * n) ≤ s.A.length → s.CJ = [] → s.CJ2 = [] → s.CJ2b = [] →
    s.CIb = [] → s.CI2b = [] → s.Z = [] → s.Zb = [] → s.Ab = [] →
    s.V = [] → s.Vb = [] → s.B = Bl.flatten →
    s.R = List.replicate Bl.length true → (∀ b ∈ Bl, b.length = m) →
    s.Rb = [] → s.Bb = [] → v.acc = false → v.m0 = false → v.m1 = false →
    exec tp_p3out ⟨v, toFun s⟩ =
        ⟨nrm v, toFun { s with T := [], Tb := List.replicate i true ++ s.Tb, C3 := [], B := (((chunk n i s.C3).flatMap (fun ci => (chunk n t s.C2).map (fun cj => dots (mask ci cj) m s.A))).foldl ins Bl).flatten, R := List.replicate (((chunk n i s.C3).flatMap (fun ci => (chunk n t s.C2).map (fun cj => dots (mask ci cj) m s.A))).foldl ins Bl).length true }⟩ ∧
      ∀ rb, Bl.length + i * t ≤ rb → cost tp_p3out ⟨v, toFun s⟩ ≤ i * (tp_colC n m t rb + 2) + 1
  | 0, Bl, v, s, hT, hC3, hT2, hT2b, hN, hNb, hM, hMb, hC2, hC2b, hCI, hCI2, hA, hCJ, hCJ2, hCJ2b,
      hCIb, hCI2b, hZ, hZb, hAb, hV, hVb, hB, hR, hBl, hRb, hBb, ha, hm0, hm1 => by
    have hC3' : s.C3 = [] := List.length_eq_zero_iff.mp (by simpa using hC3)
    refine ⟨?_, ?_⟩
    · rw [tp_p3out, exec_forPop_nil .T _ _ _ v s hT]
      refine St_eq _ _ _ _ rfl ?_
      cases s
      simp_all [chunk]
    · intro rb _
      rw [tp_p3out, cost_forPop_nil .T _ _ _ v s hT]; simp
  | i + 1, Bl, v, s, hT, hC3, hT2, hT2b, hN, hNb, hM, hMb, hC2, hC2b, hCI, hCI2, hA, hCJ, hCJ2,
      hCJ2b, hCIb, hCI2b, hZ, hZb, hAb, hV, hVb, hB, hR, hBl, hRb, hBb, ha, hm0, hm1 => by
    have hT' : s.get .T = true :: List.replicate i true := by
      simp only [Stk.get, hT, List.replicate_succ]
    have hlen : n ≤ s.C3.length := by rw [hC3, Nat.succ_mul]; omega
    have hvl : ∀ u ∈ (chunk n t s.C2).map (fun cj => dots (mask (s.C3.take n) cj) m s.A),
        u.length = m := by
      intro u hu
      obtain ⟨cj, -, rfl⟩ := List.mem_map.mp hu
      exact rl_dots_length _ _ _
    have hgrow := tp_foldl_ins_length
      ((chunk n t s.C2).map (fun cj => dots (mask (s.C3.take n) cj) m s.A)) Bl
    rw [List.length_map, rl_chunk_length] at hgrow
    refine ⟨?_, ?_⟩
    · have hb := tp_col_spec n m t Bl { v with go := true }
        { s with T := List.replicate i true, Tb := true :: s.Tb } (Bl.length + t) (le_refl _)
        hT2 hT2b hN hNb hM hMb hlen hC2 hC2b hCI hCI2 hA hCJ hCJ2 hCJ2b hCIb hCI2b hZ hZb hAb hV
        hVb hB hR hBl hRb hBb ha hm0 hm1
      have hi := tp_p3out_spec n m t i
        (((chunk n t s.C2).map (fun cj => dots (mask (s.C3.take n) cj) m s.A)).foldl ins Bl)
        (nrm { v with go := true })
        { s with T := List.replicate i true, Tb := true :: s.Tb, C3 := s.C3.drop n, B := (((chunk n t s.C2).map (fun cj => dots (mask (s.C3.take n) cj) m s.A)).foldl ins Bl).flatten, R := List.replicate (((chunk n t s.C2).map (fun cj => dots (mask (s.C3.take n) cj) m s.A)).foldl ins Bl).length true }
        rfl (by
          show (s.C3.drop n).length = i * n
          rw [List.length_drop, hC3, Nat.succ_mul]; omega) hT2 hT2b hN hNb hM hMb hC2 hC2b hCI
        hCI2 hA hCJ hCJ2 hCJ2b hCIb hCI2b hZ hZb hAb hV hVb rfl rfl
        (tp_foldl_ins_len m _ Bl hBl hvl) hRb hBb ha hm0 hm1
      rw [tp_p3out, exec_forPop_cons .T _ _ _ v s true _ hT' tp_p3out_nt]
      simp only [exec_seq, exec_wpush, Stk.get, Stk.set]
      rw [← tp_p3out]
      refine (congrArg (exec tp_p3out) hb.1).trans ?_
      refine hi.1.trans ?_
      refine St_eq _ _ _ _ (by cases v; simp [nrm]) ?_
      simp [chunk, List.replicate_succ, in_rep, List.foldl_append]
    · intro rb hrb
      have hrb' : Bl.length + i * t + t ≤ rb := by
        rw [Nat.succ_mul] at hrb; omega
      have hb := tp_col_spec n m t Bl { v with go := true }
        { s with T := List.replicate i true, Tb := true :: s.Tb } rb (by omega)
        hT2 hT2b hN hNb hM hMb hlen hC2 hC2b hCI hCI2 hA hCJ hCJ2 hCJ2b hCIb hCI2b hZ hZb hAb hV
        hVb hB hR hBl hRb hBb ha hm0 hm1
      have hi := tp_p3out_spec n m t i
        (((chunk n t s.C2).map (fun cj => dots (mask (s.C3.take n) cj) m s.A)).foldl ins Bl)
        (nrm { v with go := true })
        { s with T := List.replicate i true, Tb := true :: s.Tb, C3 := s.C3.drop n, B := (((chunk n t s.C2).map (fun cj => dots (mask (s.C3.take n) cj) m s.A)).foldl ins Bl).flatten, R := List.replicate (((chunk n t s.C2).map (fun cj => dots (mask (s.C3.take n) cj) m s.A)).foldl ins Bl).length true }
        rfl (by
          show (s.C3.drop n).length = i * n
          rw [List.length_drop, hC3, Nat.succ_mul]; omega) hT2 hT2b hN hNb hM hMb hC2 hC2b hCI
        hCI2 hA hCJ hCJ2 hCJ2b hCIb hCI2b hZ hZb hAb hV hVb rfl rfl
        (tp_foldl_ins_len m _ Bl hBl hvl) hRb hBb ha hm0 hm1
      rw [tp_p3out, cost_forPop_cons .T _ _ _ v s true _ hT' tp_p3out_nt]
      simp only [exec_seq, exec_wpush, cost_seq, cost_wpush, Stk.get, Stk.set]
      rw [← tp_p3out]
      have hb1 := hb.1
      have hb2 := hb.2
      dsimp only at hb1 hb2
      rw [hb1]
      have h5 := hi.2 rb (by omega)
      have e : (i + 1) * (tp_colC n m t rb + 2) =
          i * (tp_colC n m t rb + 2) + (tp_colC n m t rb + 2) := by ring
      rw [e]
      omega

end

section
open Turing

def tp_polar (n m t : ℕ) (c3 c2 a : List Bool) : List (List Bool) :=
  (chunk n t c3).flatMap (fun ci => (chunk n t c2).map (fun cj => dots (mask ci cj) m a))

theorem tp_polar_length (n m t : ℕ) (c3 c2 a : List Bool) :
    (tp_polar n m t c3 c2 a).length = t * t := by
  unfold tp_polar
  rw [tp_flatMap_len t, rl_chunk_length]
  intro ci _
  rw [List.length_map, rl_chunk_length]

def tp_c3 (n m t : ℕ) : ℕ :=
  t * (tp_colC n m t (t * t) + 2) + 1 + (2 * t + 1) + (3 * (t * t) + 3)

theorem phase3_spec (n m t : ℕ) (v : Reg) (s : Stk)
    (hT : s.T = List.replicate t true) (hTb : s.Tb = []) (hC3 : s.C3.length = t * n)
    (hT2 : s.T2 = List.replicate t true) (hT2b : s.T2b = [])
    (hN : s.N = List.replicate n true) (hNb : s.Nb = [])
    (hM : s.M = List.replicate m true) (hMb : s.Mb = [])
    (hC2 : s.C2.length = t * n) (hC2b : s.C2b = []) (hCI : s.CI = []) (hCI2 : s.CI2 = [])
    (hA : m * (n * n) ≤ s.A.length) (hCJ : s.CJ = []) (hCJ2 : s.CJ2 = []) (hCJ2b : s.CJ2b = [])
    (hCIb : s.CIb = []) (hCI2b : s.CI2b = []) (hZ : s.Z = []) (hZb : s.Zb = []) (hAb : s.Ab = [])
    (hV : s.V = []) (hVb : s.Vb = []) (hB : s.B = []) (hR : s.R = [])
    (hRb : s.Rb = []) (hBb : s.Bb = [])
    (ha : v.acc = false) (hm0 : v.m0 = false) (hm1 : v.m1 = false) :
    Run phase3 v s
      (nrm { v with res := v.res && decide ((basisOf (tp_polar n m t s.C3 s.C2 s.A)).length ≤ s.Kc.length) })
      { s with C3 := [], B := (basisOf (tp_polar n m t s.C3 s.C2 s.A)).flatten, Kc := s.Kc.drop (basisOf (tp_polar n m t s.C3 s.C2 s.A)).length }
      (tp_c3 n m t) := by
  have h1 := tp_p3out_spec n m t t [] v s hT hC3 hT2 hT2b hN hNb hM hMb hC2 hC2b hCI hCI2 hA hCJ
    hCJ2 hCJ2b hCIb hCI2b hZ hZb hAb hV hVb (by simpa using hB) (by simpa using hR) (by simp)
    hRb hBb ha hm0 hm1
  have hlen : (basisOf (tp_polar n m t s.C3 s.C2 s.A)).length ≤ t * t := by
    have := tp_foldl_ins_length (tp_polar n m t s.C3 s.C2 s.A) []
    rw [tp_polar_length] at this
    simpa [basisOf] using this
  have hbo : ((chunk n t s.C3).flatMap (fun ci => (chunk n t s.C2).map
      (fun cj => dots (mask ci cj) m s.A))).foldl ins [] =
      basisOf (tp_polar n m t s.C3 s.C2 s.A) := rfl
  rw [phase3_eq]
  refine Run.conv (Run.seq (Run.seq ⟨h1.1, h1.2 (t * t) (by simp)⟩
    (Run.move .Tb .T (by decide) _ _)) (cmpRK_spec _ _)) ?_ ?_ ?_
  · obtain ⟨go, tag, x, y, u, w, acc, m0, m1, ph, ok, res⟩ := v
    simp only at ha
    subst ha
    simp [nrm, Stk.set, Stk.get, hbo]
  · simp only [Stk.set, Stk.get, hbo, hTb, List.append_nil, List.reverse_replicate,
      List.length_replicate]
    cases s
    simp_all
  · simp only [Stk.set, Stk.get, hbo, hTb, List.append_nil, List.reverse_replicate,
      List.length_replicate]
    unfold tp_c3
    omega

def tp_c2 (n t : ℕ) : ℕ := t * (9 * n + 5 + 16 * (t + 1) * (n + 1)) + 4 * (t * n) + 10 * t + 9

theorem main_spec (n m t : ℕ) (v : Reg) (s : Stk)
    (hT : s.T = List.replicate t true) (hTb : s.Tb = []) (hC3 : s.C3.length = t * n)
    (hT2 : s.T2 = List.replicate t true) (hT2b : s.T2b = [])
    (hN : s.N = List.replicate n true) (hNb : s.Nb = [])
    (hM : s.M = List.replicate m true) (hMb : s.Mb = [])
    (hC2 : s.C2.length = t * n) (hC2b : s.C2b = []) (hCI : s.CI = []) (hCI2 : s.CI2 = [])
    (hA : m * (n * n) ≤ s.A.length) (hCJ : s.CJ = []) (hCJ2 : s.CJ2 = []) (hCJ2b : s.CJ2b = [])
    (hCIb : s.CIb = []) (hCI2b : s.CI2b = []) (hZ : s.Z = []) (hZb : s.Zb = []) (hAb : s.Ab = [])
    (hV : s.V = []) (hVb : s.Vb = []) (hB : s.B = []) (hR : s.R = [])
    (hRb : s.Rb = []) (hBb : s.Bb = [])
    (ha : v.acc = false) (hm0 : v.m0 = false) (hm1 : v.m1 = false) :
    Run mainP v s
      (nrm { v with res := decide (t ≤ (basisOf (chunk n t s.C2)).length) && decide ((basisOf (tp_polar n m t s.C3 s.C2 s.A)).length ≤ s.Kc.length) })
      { s with C3 := [], B := (basisOf (tp_polar n m t s.C3 s.C2 s.A)).flatten, Kc := s.Kc.drop (basisOf (tp_polar n m t s.C3 s.C2 s.A)).length }
      (tp_c2 n t + tp_c3 n m t) := by
  have h2 := phase2_spec n t v s hT hTb hN hNb hC2 hC2b hV hVb hB hR hRb hBb ha hm0 hm1
  have h3 := phase3_spec n m t (nrm { v with res := decide (t ≤ (basisOf (chunk n t s.C2)).length) })
    s hT hTb hC3 hT2 hT2b hN hNb hM hMb hC2 hC2b hCI hCI2 hA hCJ hCJ2 hCJ2b hCIb hCI2b hZ hZb hAb
    hV hVb hB hR hRb hBb ha hm0 hm1
  rw [mainP]
  refine Run.conv (Run.seq h2 h3) ?_ rfl (le_refl _)
  cases v
  simp [nrm]

end

section
open Turing

theorem tp_arith_pair (n m rb Y : ℕ) (hn : n + 1 ≤ Y) (hm : m + 1 ≤ Y) (hrb : rb + 1 ≤ Y * Y) :
    tp_pairC n m rb ≤ 60 * Y ^ 3 := by
  unfold tp_pairC
  have hY : 1 ≤ Y := by omega
  have hnn : n * n + 1 ≤ Y * Y := by nlinarith
  have h1 : 10 * (m + 1) * (n * n + 1) ≤ 10 * Y * (Y * Y) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 10 hm) hnn
  have h2 : 16 * (rb + 1) * (m + 1) ≤ 16 * (Y * Y) * Y :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 16 hrb) hm
  have h3 : 11 * (n + 1) ^ 2 ≤ 11 * Y ^ 2 := Nat.mul_le_mul_left 11 (Nat.pow_le_pow_left hn 2)
  have h4 : Y ≤ Y * Y := Nat.le_mul_self Y
  have h5 : Y * Y ≤ Y * Y * Y := Nat.le_mul_of_pos_right _ hY
  nlinarith

theorem tp_arith_col (n m t rb Y : ℕ) (hn : n + 1 ≤ Y) (hm : m + 1 ≤ Y) (ht : t + 1 ≤ Y)
    (hrb : rb + 1 ≤ Y * Y) : tp_colC n m t rb ≤ 90 * Y ^ 4 := by
  unfold tp_colC
  have hp := tp_arith_pair n m rb Y hn hm hrb
  have hY : 1 ≤ Y := by omega
  have h1 : t * (tp_pairC n m rb + 2) ≤ Y * (60 * Y ^ 3 + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : t * n ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
  have h4 : Y ≤ Y * Y := Nat.le_mul_self Y
  have h5 : Y * Y ≤ Y * Y * Y := Nat.le_mul_of_pos_right _ hY
  have h6 : Y * Y * Y ≤ Y * Y * Y * Y := Nat.le_mul_of_pos_right _ hY
  nlinarith

theorem tp_arith_c3 (n m t Y : ℕ) (hn : n + 1 ≤ Y) (hm : m + 1 ≤ Y) (ht : t + 1 ≤ Y) :
    tp_c3 n m t ≤ 100 * Y ^ 5 := by
  unfold tp_c3
  have hY : 1 ≤ Y := by omega
  have htt : t * t + 1 ≤ Y * Y := by nlinarith
  have hc := tp_arith_col n m t (t * t) Y hn hm ht htt
  have h1 : t * (tp_colC n m t (t * t) + 2) ≤ Y * (90 * Y ^ 4 + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : Y ≤ Y * Y := Nat.le_mul_self Y
  have h5 : Y * Y ≤ Y * Y * Y := Nat.le_mul_of_pos_right _ hY
  have h6 : Y * Y * Y ≤ Y * Y * Y * Y := Nat.le_mul_of_pos_right _ hY
  have h7 : Y * Y * Y * Y ≤ Y * Y * Y * Y * Y := Nat.le_mul_of_pos_right _ hY
  nlinarith

theorem tp_arith_c2 (n t Y : ℕ) (hn : n + 1 ≤ Y) (ht : t + 1 ≤ Y) : tp_c2 n t ≤ 60 * Y ^ 3 := by
  unfold tp_c2
  have hY : 1 ≤ Y := by omega
  have h1 : 16 * (t + 1) * (n + 1) ≤ 16 * Y * Y := Nat.mul_le_mul (Nat.mul_le_mul_left 16 ht) hn
  have h2 : t * (9 * n + 5 + 16 * (t + 1) * (n + 1)) ≤ Y * (9 * Y + 5 + 16 * Y * Y) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : t * n ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
  have h4 : Y ≤ Y * Y := Nat.le_mul_self Y
  have h5 : Y * Y ≤ Y * Y * Y := Nat.le_mul_of_pos_right _ hY
  nlinarith

end

section
open Turing

def sizeAll (s : Stk) : ℕ :=
  s.N.length + s.Nb.length + s.N2.length + s.N2b.length + s.M.length + s.Mb.length + s.Kc.length + s.Kb.length + s.D.length + s.T.length + s.Tb.length + s.T2.length + s.T2b.length + s.P.length + s.A.length + s.Ab.length + s.C2.length + s.C2b.length + s.C3.length + s.CI.length + s.CIb.length + s.CI2.length + s.CI2b.length + s.CJ.length + s.CJ2.length + s.CJ2b.length + s.Z.length + s.Zb.length + s.V.length + s.Vb.length + s.B.length + s.Bb.length + s.R.length + s.Rb.length

theorem drainAll_spec (v : Reg) (s : Stk) :
    Run drainAll v s (nrm v) { emp with inp := s.inp } (2 * sizeAll s + 34) := by
  simp only [drainAll, List.foldr]
  refine Run.conv (Run.seq (Run.drain .N _ _)
    (Run.seq (Run.drain .Nb _ _)
    (Run.seq (Run.drain .N2 _ _)
    (Run.seq (Run.drain .N2b _ _)
    (Run.seq (Run.drain .M _ _)
    (Run.seq (Run.drain .Mb _ _)
    (Run.seq (Run.drain .Kc _ _)
    (Run.seq (Run.drain .Kb _ _)
    (Run.seq (Run.drain .D _ _)
    (Run.seq (Run.drain .T _ _)
    (Run.seq (Run.drain .Tb _ _)
    (Run.seq (Run.drain .T2 _ _)
    (Run.seq (Run.drain .T2b _ _)
    (Run.seq (Run.drain .P _ _)
    (Run.seq (Run.drain .A _ _)
    (Run.seq (Run.drain .Ab _ _)
    (Run.seq (Run.drain .C2 _ _)
    (Run.seq (Run.drain .C2b _ _)
    (Run.seq (Run.drain .C3 _ _)
    (Run.seq (Run.drain .CI _ _)
    (Run.seq (Run.drain .CIb _ _)
    (Run.seq (Run.drain .CI2 _ _)
    (Run.seq (Run.drain .CI2b _ _)
    (Run.seq (Run.drain .CJ _ _)
    (Run.seq (Run.drain .CJ2 _ _)
    (Run.seq (Run.drain .CJ2b _ _)
    (Run.seq (Run.drain .Z _ _)
    (Run.seq (Run.drain .Zb _ _)
    (Run.seq (Run.drain .V _ _)
    (Run.seq (Run.drain .Vb _ _)
    (Run.seq (Run.drain .B _ _)
    (Run.seq (Run.drain .Bb _ _)
    (Run.seq (Run.drain .R _ _)
    (Run.drain .Rb _ _)))))))))))))))))))))))))))))))))) ?_ ?_ ?_
  · cases v
    simp [nrm]
  · simp only [Stk.set]
    rfl
  · simp only [Stk.set, Stk.get]
    unfold sizeAll
    omega

end

section
open Turing

theorem tp_polar_len (n m t : ℕ) (c3 c2 a : List Bool) :
    ∀ u ∈ tp_polar n m t c3 c2 a, u.length = m := by
  intro u hu
  unfold tp_polar at hu
  obtain ⟨ci, -, h⟩ := List.mem_flatMap.mp hu
  obtain ⟨cj, -, rfl⟩ := List.mem_map.mp h
  exact rl_dots_length _ _ _

def tp_s1 (n m k d : ℕ) (ab w : List Bool) : Stk :=
  { emp with N := List.replicate n true, N2 := List.replicate n true, T := List.replicate (n + m) true, M := List.replicate m true, Kc := List.replicate k true, D := List.replicate d true, Ab := ab, C2b := w.reverse }

def tp_s2 (n m k d : ℕ) (ab w : List Bool) : Stk :=
  { tp_s1 n m k d ab w with D := [], T := List.replicate (n + m - (k + d)) true, T2 := List.replicate (n + m - (k + d)) true, Ab := [], A := ab.reverse, C2b := [], C2 := w.reverse.reverse, C3 := w.reverse.reverse }

theorem tp_run_false (n m k d : ℕ) (ab w : List Bool) (v : Reg) (hokv : v.ok = false) :
    Run (Prog.seq (Prog.ite (fun v => v.ok) mainP (Prog.load id)) drainAll) v
      (tp_s2 n m k d ab w) (nrm v) emp
      (2 + (2 * (2 * n + m + k + 2 * (n + m - (k + d)) + ab.length + 2 * w.length) + 34)) := by
  refine Run.conv (Run.seq (Run.ite_false hokv (Run.load id _ _)) (drainAll_spec _ _)) rfl rfl ?_
  simp only [sizeAll, tp_s2, tp_s1, emp, List.length_replicate, List.length_reverse,
    List.length_nil]
  omega

theorem tp_run_true (n m k d : ℕ) (ab w : List Bool) (v : Reg)
    (hab : ab.length = m * n * n) (hw : w.length = (n + m - (k + d)) * n)
    (hokv : v.ok = true) (ha : v.acc = false) (hm0 : v.m0 = false) (hm1 : v.m1 = false) :
    Run (Prog.seq (Prog.ite (fun v => v.ok) mainP (Prog.load id)) drainAll) v
      (tp_s2 n m k d ab w)
      (nrm (nrm { v with res := decide (n + m - (k + d) ≤ (basisOf (chunk n (n + m - (k + d)) w)).length) && decide ((basisOf (tp_polar n m (n + m - (k + d)) w w ab.reverse)).length ≤ k) }))
      emp
      ((tp_c2 n (n + m - (k + d)) + tp_c3 n m (n + m - (k + d)) + 1) +
        (2 * (2 * n + m + k + 2 * (n + m - (k + d)) + ab.length + w.length +
          (n + m - (k + d)) * (n + m - (k + d)) * m) + 34)) := by
  have hmn := main_spec n m (n + m - (k + d)) v (tp_s2 n m k d ab w) rfl rfl
    (by simp [tp_s2, hw]) rfl rfl rfl rfl rfl rfl (by simp [tp_s2, hw]) rfl rfl rfl
    (by simp [tp_s2, hab, Nat.mul_assoc]) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    ha hm0 hm1
  have hbl : ∀ b ∈ basisOf (tp_polar n m (n + m - (k + d)) w w ab.reverse), b.length = m :=
    tp_foldl_ins_len m _ [] (by simp) (tp_polar_len n m _ w w ab.reverse)
  have hfl := in_flatten_len m _ hbl
  have hln : (basisOf (tp_polar n m (n + m - (k + d)) w w ab.reverse)).length ≤
      (n + m - (k + d)) * (n + m - (k + d)) := by
    have := tp_foldl_ins_length (tp_polar n m (n + m - (k + d)) w w ab.reverse) []
    rw [tp_polar_length] at this
    simpa [basisOf] using this
  have hmul := Nat.mul_le_mul_right m hln
  refine Run.conv (Run.seq (Run.ite_true hokv hmn) (drainAll_spec _ _)) ?_ rfl ?_
  · simp [tp_s2, tp_s1]
  · simp only [sizeAll, tp_s2, tp_s1, emp, List.length_replicate, List.length_reverse,
      List.length_nil, List.reverse_reverse, List.length_drop, hfl]
    omega

theorem tp_verify_some (x w : List Bool) (n m k d : ℕ) (a : List Bool)
    (hp : parse x = some (n, m, k, d, a)) :
    verifyFn (x, w) = (decide (k ≤ m) && decide (a.length = m * n * n) &&
      decide (w.length = (n + m - (k + d)) * n) &&
      decide (n + m - (k + d) ≤ (basisOf (chunk n (n + m - (k + d)) w)).length) &&
      decide ((basisOf (tp_polar n m (n + m - (k + d)) w w a)).length ≤ k)) := by
  unfold verifyFn
  simp only [hp]
  rfl

theorem tp_verify_none (x w : List Bool) (hp : parse x = none) : verifyFn (x, w) = false := by
  simp [verifyFn, hp]

theorem tp_arith_total (n m k d la lw t N V c2 c3 Y1 : ℕ) (hN : n + m + k + d + la + lw ≤ N)
    (ht : t ≤ n + m) (hY1 : Y1 ≤ N + 1) (h2 : c2 ≤ 60 * (N + 1) ^ 3)
    (h3 : c3 ≤ 100 * (N + 1) ^ 5) (hV : V ≤ 100 * Y1 ^ 3) :
    1 + ((8 * N + 2) + (V + ((c2 + c3 + 1) +
      (2 * (2 * n + m + k + 2 * t + la + lw + t * t * m) + 34)))) ≤ 400 * (N + 1) ^ 5 := by
  have hY : 1 ≤ N + 1 := by omega
  have hV' : V ≤ 100 * (N + 1) ^ 3 := le_trans hV (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hY1 3))
  have htt : t * t * m ≤ (N + 1) * (N + 1) * (N + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  have h4 : N + 1 ≤ (N + 1) * (N + 1) := Nat.le_mul_self _
  have h5 : (N + 1) * (N + 1) ≤ (N + 1) * (N + 1) * (N + 1) := Nat.le_mul_of_pos_right _ hY
  have h6 : (N + 1) * (N + 1) * (N + 1) ≤ (N + 1) * (N + 1) * (N + 1) * (N + 1) :=
    Nat.le_mul_of_pos_right _ hY
  have h7 : (N + 1) * (N + 1) * (N + 1) * (N + 1) ≤ (N + 1) * (N + 1) * (N + 1) * (N + 1) * (N + 1) :=
    Nat.le_mul_of_pos_right _ hY
  nlinarith

end

section
open Turing

theorem tp_arith_false (n m k d la lw t N V Y1 : ℕ) (hN : n + m + k + d + la + lw ≤ N)
    (ht : t ≤ n + m) (hY1 : Y1 ≤ N + 1) (hV : V ≤ 100 * Y1 ^ 3) :
    1 + ((8 * N + 2) + (V + (2 + (2 * (2 * n + m + k + 2 * t + la + 2 * lw) + 34)))) ≤
      400 * (N + 1) ^ 5 := by
  have hY : 1 ≤ N + 1 := by omega
  have hV' : V ≤ 100 * (N + 1) ^ 3 := le_trans hV (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hY1 3))
  have h4 : N + 1 ≤ (N + 1) * (N + 1) := Nat.le_mul_self _
  have h5 : (N + 1) * (N + 1) ≤ (N + 1) * (N + 1) * (N + 1) := Nat.le_mul_of_pos_right _ hY
  have h6 : (N + 1) * (N + 1) * (N + 1) ≤ (N + 1) * (N + 1) * (N + 1) * (N + 1) :=
    Nat.le_mul_of_pos_right _ hY
  have h7 : (N + 1) * (N + 1) * (N + 1) * (N + 1) ≤ (N + 1) * (N + 1) * (N + 1) * (N + 1) * (N + 1) :=
    Nat.le_mul_of_pos_right _ hY
  nlinarith

theorem prog_spec (x w : List Bool) : ∃ v' : Reg,
    exec prog ⟨regInit, toFun (inStk x w)⟩ = ⟨v', toFun emp⟩ ∧ v'.res = verifyFn (x, w) ∧
      1 + cost prog ⟨regInit, toFun (inStk x w)⟩ ≤ tB (x.length + w.length) := by
  obtain ⟨n, m, k, d, ab, ph, ok, hexec, hok1, hok0, hsize, hcost⟩ := parse_spec x w
  have hp : Run parseP regInit (inStk x w) { regInit with ph := ph, ok := ok }
      (tp_s1 n m k d ab w) (8 * (x.length + w.length) + 2) := ⟨hexec, hcost⟩
  have hv : Run validP { regInit with ph := ph, ok := ok } (tp_s1 n m k d ab w)
      (nrm { regInit with ph := ph, ok := ok && decide (k ≤ m) && decide (ab.length = m * n * n) && decide (w.reverse.length = (n + m - (k + d)) * n) })
      (tp_s2 n m k d ab w) (100 * (n + m + k + d + ab.length + w.reverse.length + 1) ^ 3) :=
    valid_spec n m k d ab w.reverse _ (tp_s1 n m k d ab w) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl
  have hY1 : n + m + k + d + ab.length + w.reverse.length + 1 ≤ x.length + w.length + 1 := by
    rw [List.length_reverse]; omega
  have ht : n + m - (k + d) ≤ n + m := Nat.sub_le _ _
  cases hokk : (ok && decide (k ≤ m) && decide (ab.length = m * n * n) &&
      decide (w.reverse.length = (n + m - (k + d)) * n))
  · have hr := tp_run_false n m k d ab w
      (nrm { regInit with ph := ph, ok := ok && decide (k ≤ m) && decide (ab.length = m * n * n) && decide (w.reverse.length = (n + m - (k + d)) * n) })
      hokk
    have hall := Run.seq hp (Run.seq hv hr)
    refine ⟨_, hall.1, ?_, ?_⟩
    · cases hok : ok
      · rw [tp_verify_none x w (hok0 hok)]; rfl
      · rw [tp_verify_some x w n m k d ab.reverse (hok1 hok)]
        rw [hok] at hokk
        simp only [Bool.true_and, List.length_reverse] at hokk
        simp only [List.length_reverse, hokk, Bool.false_and]
        rfl
    · refine le_trans (Nat.add_le_add_left hall.2 1) ?_
      unfold tB
      exact tp_arith_false n m k d ab.length w.length (n + m - (k + d)) (x.length + w.length) _ _
        (by omega) ht hY1 (le_refl _)
  · have hokk' := hokk
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_reverse] at hokk'
    obtain ⟨⟨⟨hok, hkm⟩, hab⟩, hw⟩ := hokk'
    have hr := tp_run_true n m k d ab w
      (nrm { regInit with ph := ph, ok := ok && decide (k ≤ m) && decide (ab.length = m * n * n) && decide (w.reverse.length = (n + m - (k + d)) * n) })
      hab hw hokk rfl rfl rfl
    have hall := Run.seq hp (Run.seq hv hr)
    refine ⟨_, hall.1, ?_, ?_⟩
    · rw [tp_verify_some x w n m k d ab.reverse (hok1 hok)]
      simp only [List.length_reverse, hkm, hab, hw, decide_true, Bool.true_and]
      rfl
    · refine le_trans (Nat.add_le_add_left hall.2 1) ?_
      unfold tB
      exact tp_arith_total n m k d ab.length w.length (n + m - (k + d)) (x.length + w.length) _ _ _ _
        (by omega) ht hY1
        (tp_arith_c2 n (n + m - (k + d)) _ (by omega) (by omega))
        (tp_arith_c3 n m (n + m - (k + d)) _ (by omega) (by omega) (by omega)) (le_refl _)

end

section
open Turing

theorem tp_map_refl {α : Type} (l : List α) : List.map (Equiv.refl α).invFun l = l :=
  List.map_id l

theorem tp_evals (z : List Bool × List Bool) (l1 : List (Bool ⊕ Bool)) (l2 : List Bool)
    (h1 : l1 = z.1.map Sum.inl ++ z.2.map Sum.inr) (h2 : l2 = [verifyFn z]) :
    (flip bind tm397.step)^[1 + cost prog ⟨regInit, toFun (inStk z.1 z.2)⟩]
        (some (initList tm397 l1)) = Option.map (haltList tm397) (some l2) := by
  subst h1 h2
  obtain ⟨v', e1, e2, -⟩ := prog_spec z.1 z.2
  have e := tm397_run z.1 z.2 v' e1
  rw [e2] at e
  exact e

noncomputable def comp397 :
    TM2ComputableInTime PEqualNP.Library.encodePair Computability.encodeBool verifyFn where
  tm := tm397
  inputAlphabet := Equiv.refl (Bool ⊕ Bool)
  outputAlphabet := Equiv.refl Bool
  time := tB
  outputsFun := fun z =>
    { steps := 1 + cost prog ⟨regInit, toFun (inStk z.1 z.2)⟩
      evals_in_steps := tp_evals z _ _ (tp_map_refl _) (tp_map_refl _)
      steps_le_m := by
        obtain ⟨v', -, -, h3⟩ := prog_spec z.1 z.2
        simpa [PEqualNP.Library.encodePair] using h3 }

theorem machine_exists : ∃ (P : Polynomial ℕ)
    (M : Turing.TM2ComputableInTime PEqualNP.Library.encodePair Computability.encodeBool verifyFn),
    (∀ j, Finite (M.tm.Γ j)) ∧ (∀ b, M.time b ≤ P.eval b) := by
  refine ⟨Polynomial.C 400 * (Polynomial.X + 1) ^ 5, comp397, ?_, ?_⟩
  · intro j
    cases j with
    | inp => exact inferInstanceAs (Finite (Bool ⊕ Bool))
    | out => exact inferInstanceAs (Finite Bool)
    | w a => exact inferInstanceAs (Finite Bool)
  · intro b
    simp [comp397, tB]

end

end PEqualNP.Outside.L_pcx_397_aux

theorem PEqualNP.Outside.L_pcx_397 : (let F := ZMod 2
let header := fun n : ℕ => List.replicate n true ++ [false]
let pack := fun (n m k d : ℕ) (A : Fin m → Fin n → Fin n → Bool) =>
  header n ++ header m ++ header k ++ header d ++
    (List.finRange m).flatMap (fun e => (List.finRange n).flatMap
      (fun i => (List.finRange n).map (fun j => A e i j)))
let quad := fun (n m : ℕ) (A : Fin m → Fin n → Fin n → Bool)
    (x : Fin n → F) (e : Fin m) =>
  Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
    if A e i j then x i * x j else 0))
let relation : Set (List Bool × List Bool) := {z | ∃ (n m k d : ℕ)
    (A : Fin m → Fin n → Fin n → Bool),
  k ≤ m ∧ pack n m k d A = z.1 ∧
    let t := n+m-(k+d)
    let Q := quad n m A
    ∃ cols : Fin t → (Fin n → F),
      (List.finRange t).flatMap (fun i => (List.finRange n).map
        (fun j => decide (cols i j = 1))) = z.2 ∧
      Module.finrank F (Submodule.span F (Set.range cols)) = t ∧
      Module.finrank F (Submodule.span F (Set.range (fun ij : Fin t × Fin t =>
        Q (cols ij.1 + cols ij.2) - Q (cols ij.1) - Q (cols ij.2) + Q 0))) ≤ k}
∃ (verify : (List Bool × List Bool) → Bool) (P : Polynomial ℕ)
  (M : Turing.TM2ComputableInTime PEqualNP.Library.encodePair Computability.encodeBool verify),
  (∀ j, Finite (M.tm.Γ j)) ∧ (∀ b, M.time b ≤ P.eval b) ∧
  (∀ z, verify z = true ↔ z ∈ relation) ∧
  ∀ x w : List Bool, (x,w) ∈ relation → w.length ≤ x.length^2) := by
  obtain ⟨P, M, h1, h2⟩ := PEqualNP.Outside.L_pcx_397_aux.machine_exists
  exact ⟨PEqualNP.Outside.L_pcx_397_aux.verifyFn, P, M, h1, h2,
    PEqualNP.Outside.L_pcx_397_aux.verifyFn_iff, PEqualNP.Outside.L_pcx_397_aux.rel_len⟩
