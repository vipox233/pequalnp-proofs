import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25639
abbrev F := ZMod 2
abbrev W (k : Nat) := Fin k → F
def ix {k : Nat} (hk : 0<k) (n : Nat) : Fin k := ⟨n%k, Nat.mod_lt _ hk⟩
def rot {k : Nat} (hk : 0<k) (s : Nat) : W k →ₗ[F] W k where
  toFun x i := x (ix hk (i.val+k-s%k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def mix {k : Nat} (hk : 0<k) (s : Nat) : W k →ₗ[F] W k where
  toFun x i := x i+x (ix hk (i.val+s))+x (ix hk (i.val+k-s%k))
  map_add' x y := by funext i; simp only [Pi.add_apply]; abel
  map_smul' c x := by ext i; simp [Pi.smul_apply, mul_add]
def qstep {k : Nat} (hk : 0<k) (x : W k) (i : Fin k) :=
  x i+(1+x (ix hk (i.val+1)))*x (ix hk (i.val+2))
def output {k : Nat} (hk : 0<k) (row col c₁ c₂ key : W k) : W k × W k :=
  (qstep hk (mix hk 1 (rot hk 1 key + row)) + key+c₁,
   qstep hk (mix hk 2 (rot hk 3 key + col)) + rot hk 4 key+c₂)
def obs {D : Type*} [AddCommGroup D] [Module F D] {k : Nat} (hk : 0<k)
    (s t : Nat) (L : D →ₗ[F] W k) (i : Nat) : D →ₗ[F] F :=
  (LinearMap.proj (ix hk i)).comp ((mix hk s).comp ((rot hk t).comp L))
def Compat {A : Type*} [Zero A] (a b : A) : Prop := a=0 ∨ b=0 ∨ a=b

theorem doubleF : ∀ x : F, x+x=0 := by decide +kernel
theorem dichF : ∀ x : F, x=0 ∨ x=1 := by decide +kernel

theorem compat_iff {D : Type*} [AddCommGroup D] [Module F D] (a b : D →ₗ[F] F) :
    Compat a b ↔ ∀ u v, a u*b v+a v*b u=0 := by
  constructor
  · rintro (rfl|rfl|rfl) u v
    · simp
    · simp
    · simpa only [mul_comm (a v) (a u)] using doubleF (a u*a v)
  · intro h
    by_cases hz : a=0
    · exact Or.inl hz
    · have ex : ∃ u, a u ≠ 0 := by
        by_contra! HH
        apply hz
        ext u
        exact HH u
      obtain ⟨u,hu⟩ := ex
      have hone := (dichF (a u)).resolve_left hu
      rcases dichF (b u) with h0|h1
      · right; left; ext v
        simpa [hone,h0] using h u v
      · right; right; ext v
        have hh : b v + a v = 0 := by simpa [hone,h1] using h u v
        calc a v = (b v+b v)+a v := by rw [doubleF,zero_add]
             _ = b v := by rw [add_assoc,hh,add_zero]

def FlatAlong {k : Nat} {D : Type*} [AddCommGroup D] [Module F D]
    (o : W k → W k × W k) (L : D →ₗ[F] W k) (base : W k) :=
  ∃ f : D →ₗ[F] (W k × W k), ∀ u, o (base+L u)=o base+f u

theorem flatDiff {k : Nat} {D : Type*} [AddCommGroup D] [Module F D]
    (o : W k → W k × W k) (L : D →ₗ[F] W k) (base : W k) :
    FlatAlong o L base ↔ ∀ u v,
      o (base+L u+L v) - o (base+L u) - o (base+L v) + o base = 0 := by
  constructor
  · rintro ⟨f,hf⟩ u v
    rw [add_assoc, ← map_add, hf, hf, hf, map_add]
    abel
  · intro h
    let d := fun u => o (base+L u)-o base
    have hd : ∀ u v, d (u+v)=d u+d v := by
      intro u v
      dsimp [d]
      rw [map_add, ← add_assoc]
      have hh := h u v
      abel_nf at hh ⊢
      exact sub_eq_zero.mp (by linear_combination hh)
    refine ⟨{ toFun := d, map_add' := hd, map_smul' := ?_ }, ?_⟩
    · intro c u
      rcases dichF c with rfl|rfl <;> simp [d]
    · intro u
      change _ = o base+(o (base+L u)-o base)
      abel

theorem coordPolar {k : Nat} (hk : 0<k) (s t : Nat) (r c : W k)
    (M : W k →ₗ[F] W k) (b u v : W k) (i : Fin k) :
    let H := fun x => qstep hk (mix hk s (rot hk t x+r)) i + M x i + c i
    H (b+u+v)-H (b+u)-H (b+v)+H b =
      (mix hk s (rot hk t u)) (ix hk (i.val+1)) * (mix hk s (rot hk t v)) (ix hk (i.val+2)) +
      (mix hk s (rot hk t v)) (ix hk (i.val+1)) * (mix hk s (rot hk t u)) (ix hk (i.val+2)) := by
  dsimp only
  simp only [qstep,map_add,Pi.add_apply]
  ring

theorem criterion {k : Nat} (hk : 0<k) {D : Type*} [AddCommGroup D] [Module F D]
    (L : D →ₗ[F] W k) (row col c₁ c₂ base : W k) :
    FlatAlong (output hk row col c₁ c₂) L base ↔
    (∀ i : Fin k, Compat (obs hk 1 1 L (i.val+1)) (obs hk 1 1 L (i.val+2))) ∧
    (∀ i : Fin k, Compat (obs hk 2 3 L (i.val+1)) (obs hk 2 3 L (i.val+2))) := by
  rw [flatDiff]
  constructor
  · intro h
    constructor
    · intro i
      apply (compat_iff _ _).mpr
      intro u v
      have h' := congrArg (fun z : W k × W k => z.1 i) (h u v)
      exact (coordPolar hk 1 1 row c₁ LinearMap.id base (L u) (L v) i).symm.trans h'
    · intro i
      apply (compat_iff _ _).mpr
      intro u v
      have h' := congrArg (fun z : W k × W k => z.2 i) (h u v)
      exact (coordPolar hk 2 3 col c₂ (rot hk 4) base (L u) (L v) i).symm.trans h'
  · rintro ⟨h1,h2⟩ u v
    apply Prod.ext
    · funext i
      exact (coordPolar hk 1 1 row c₁ LinearMap.id base (L u) (L v) i).trans ((compat_iff _ _).mp (h1 i) u v)
    · funext i
      exact (coordPolar hk 2 3 col c₂ (rot hk 4) base (L u) (L v) i).trans ((compat_iff _ _).mp (h2 i) u v)



def Period {A : Type*} (k : Nat) (a : Nat → A) := ∀ i, a (i+k) = a i

theorem per_iter {A : Type*} {a : Nat → A} {k : Nat} (h : Period k a)
    (s q : Nat) : a (s+q*k) = a s := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, ← Nat.add_assoc, h, ih]

theorem per_reduce {A : Type*} {a : Nat → A} {k : Nat} (h : Period k a)
    (n d : Nat) : a (n+d) = a (n%k+d) := by
  have eq : n+d = (n%k+d) + (n/k)*k := by
    have := Nat.mod_add_div n k
    rw [Nat.mul_comm (n/k) k]
    omega
  rw [eq, per_iter h]

def Adj {A : Type*} [Zero A] (a : Nat → A) : Prop :=
  ∀ i, a i = 0 ∨ a (i+1) = 0 ∨ a i = a (i+1)

def start {A : Type*} [Zero A] (a : Nat → A) (i : Nat) :=
  a (i+1) ≠ 0 ∧ a i ≠ a (i+1)

theorem starts_close {A : Type*} [AddCommGroup A] (char : ∀ z : A, z + z = 0)
    (a : Nat → A) (ha : Adj a)
    (hb : Adj (fun i => a i + a (i+1) + a (i+2))) (i j : Nat)
    (si : start a i) (sj : start a j) (h1 : i ≤ j+2) (h2 : j ≤ i+2) :
    a (i+1) = a (j+1) := by
  have fwd : ∀ t d : Nat, start a t → start a (t+d) → d ≤ 2 →
      a (t+1) = a (t+d+1) := by
    intro t d st su hd
    obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    · rfl
    · rcases ha (t+1) with h | h | h
      · exact (st.1 h).elim
      · exact (su.1 h).elim
      · exact h
    · have z0 : a t = 0 := (ha t).resolve_right (by
          rintro (h | h)
          · exact st.1 h
          · exact st.2 h)
      have z2 : a (t+2) = 0 := (ha (t+2)).resolve_right (by
          rintro (h | h)
          · exact su.1 h
          · exact su.2 h)
      have opp := hb t
      simp only [z0, z2, zero_add, add_zero] at opp
      rcases opp with h | h | h
      · exact (st.1 h).elim
      · calc
          a (t+1) = a (t+1) + (a (t+2+1) + a (t+2+1)) := by rw [char, add_zero]
          _ = (a (t+1) + a (t+2+1)) + a (t+2+1) := (add_assoc _ _ _).symm
          _ = a (t+2+1) := by rw [show a (t+1) + a (t+2+1) = 0 from h, zero_add]
      · have z : a (t+2+1) = 0 := add_left_cancel (show a (t+1) + a (t+2+1) = a (t+1) + 0 by simpa using h.symm)
        exact (su.1 z).elim
  by_cases hij : i ≤ j
  · have he : i+(j-i)=j := by omega
    simpa only [he] using fwd i (j-i) si (by rw [he]; exact sj) (by omega)
  · have he : j+(i-j)=i := by omega
    symm
    simpa only [he] using fwd j (i-j) sj (by rw [he]; exact si) (by omega)

noncomputable def labels {A : Type*} [Zero A] (k : Nat) (a : Nat → A) : Finset A := by
  classical
  exact ((Finset.range k).image a).erase 0

theorem label_mem {A : Type*} [Zero A] {a : Nat → A} {k : Nat} {x : A} :
    x ∈ labels k a ↔ x ≠ 0 ∧ ∃ i < k, a i = x := by
  classical
  simp [labels]

theorem findStart {A : Type*} [Zero A] {a : Nat → A} {k : Nat} (per : Period k a)
    (x : A) (hx : x ∈ labels k a) (hvar : ∃ j < k, a j ≠ x) :
    ∃ r < k, start a r ∧ a (r+1) = x := by
  obtain ⟨nz,t,ht,atval⟩ := label_mem.mp hx
  obtain ⟨bad,hbad,ne⟩ := hvar
  by_contra h
  have back : ∀ i, a (i+1) = x → a i = x := by
    intro i hit
    by_contra other
    have hk : 0 < k := by omega
    have hi : a (i%k) ≠ x := fun h => other ((per_reduce per i 0).trans h)
    have hh : a (i%k+1) = x := (per_reduce per i 1).symm.trans hit
    exact h ⟨i%k, Nat.mod_lt _ hk, ⟨fun h0 => nz (hh.symm.trans h0), fun he => hi (he.trans hh)⟩, hh⟩
  have iter : ∀ n, a (bad+n) = x → a bad = x := by
    intro n
    induction n with
    | zero => simpa
    | succ n ih => exact fun hv => ih (back (bad+n) hv)
  have he : bad+(t+k-bad) = t+k := by omega
  exact ne (iter (t+k-bad) (by rw [he, per, atval]))

theorem label_budget {A : Type*} [AddCommGroup A] (char : ∀ z : A, z+z=0)
    (k : Nat) (big : 5 ≤ k) (a : Nat → A) (per : Period k a) (ha : Adj a)
    (hb : Adj (fun i => a i + a (i+1) + a (i+2))) :
    (labels k a).card ≤ k/3 := by
  classical
  by_cases small : (labels k a).card ≤ 1
  · omega
  have rep : ∀ x : ↥(labels k a), ∃ r < k, start a r ∧ a (r+1) = x.val := by
    intro x
    apply findStart per x.val x.property
    by_contra h
    have sub : labels k a ⊆ {x.val} := by
      intro y hy
      obtain ⟨_,i,hi,eq⟩ := label_mem.mp hy
      have hz : a i = x.val := by_contra (fun ne => h ⟨i,hi,ne⟩)
      simpa using eq.symm.trans hz
    have hc := Finset.card_le_card sub
    simp only [Finset.card_singleton] at hc
    omega
  choose r hr hs hv using rep
  let alloc := fun p : ↥(labels k a) × Fin 3 =>
    (⟨(r p.1 + p.2.val)%k, Nat.mod_lt _ (by omega)⟩ : Fin k)
  have inj : Function.Injective alloc := by
    rintro ⟨x,t⟩ ⟨y,u⟩ heq
    have eq : (r x+t.val)%k = (r y+u.val)%k := congrArg Fin.val heq
    let z := (r x+t.val)%k + k
    have lift : ∀ (v : ↥(labels k a)) (d : Fin 3), (r v+d.val)%k+k = z →
        ∃ j, j+d.val=z ∧ start a j ∧ a (j+1)=v.val := by
      intro v d e
      by_cases hlt : r v+d.val<k
      · rw [Nat.mod_eq_of_lt hlt] at e
        have bump : a (r v+k+1) = a (r v+1) := by rw [show r v+k+1=r v+1+k by omega, per]
        refine ⟨r v+k, by omega, ?_, bump.trans (hv v)⟩
        exact ⟨by rw [bump]; exact (hs v).1, by rw [per, bump]; exact (hs v).2⟩
      · have less : r v+d.val-k<k := by have := hr v; have := d.isLt; omega
        rw [Nat.mod_eq_sub_mod (by omega : k ≤ r v+d.val), Nat.mod_eq_of_lt less] at e
        exact ⟨r v, by omega, hs v, hv v⟩
    obtain ⟨i,hi,si,vi⟩ := lift x t rfl
    obtain ⟨j,hj,sj,vj⟩ := lift y u (by dsimp [z]; rw [eq])
    have lab := starts_close char a ha hb i j si sj (by have := u.isLt; omega) (by have := t.isLt; omega)
    have xy : x=y := Subtype.ext (vi.symm.trans (lab.trans vj))
    subst y
    have tu : t=u := by
      apply Fin.ext
      have hmod : ∀ d : Nat, d<3 → (r x+d)%k = if r x+d<k then r x+d else r x+d-k := by
        intro d hd
        split
        next h => exact Nat.mod_eq_of_lt h
        next h => rw [Nat.mod_eq_sub_mod (by omega : k ≤ r x+d), Nat.mod_eq_of_lt (by have := hr x; omega)]
      rw [hmod t.val t.isLt,hmod u.val u.isLt] at eq
      split at eq <;> split at eq <;> omega
    subst u
    rfl
  have card := Fintype.card_le_of_injective alloc inj
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at card
  omega

def readAt {k : Nat} (hk : 0<k) (x : W k) (n : Nat) := x (ix hk n)
theorem at_per {k : Nat} (hk : 0<k) (x : W k) : Period k (readAt hk x) := by
  intro n
  simp [readAt,ix]

theorem idx_add {k : Nat} (hk : 0<k) (n d : Nat) :
    ix hk ((n%k)+d) = ix hk (n+d) := by
  apply Fin.ext
  exact Nat.mod_add_mod n k d

theorem ret {k : Nat} (hk : 0<k) (n s : Nat) :
    (((n+s)%k+k-s%k)%k) = n%k := by
  have hn := Nat.mod_lt n hk
  have hs := Nat.mod_lt s hk
  rw [Nat.add_mod n s]
  by_cases hc : n%k+s%k<k
  · rw [Nat.mod_eq_of_lt hc, show n%k+s%k+k-s%k=n%k+k by omega]
    simp
  · have hh : n%k+s%k-k<k := by omega
    rw [Nat.mod_eq_sub_mod (by omega : k ≤ n%k+s%k), Nat.mod_eq_of_lt hh,
      show n%k+s%k-k+k-s%k=n%k by omega, Nat.mod_eq_of_lt hn]

theorem rotAt {k : Nat} (hk : 0<k) (s : Nat) (x : W k) (n : Nat) :
    readAt hk (rot hk s x) (n+s) = readAt hk x n := by
  change x (ix hk ((n+s)%k+k-s%k))=x (ix hk n)
  apply congrArg x
  apply Fin.ext
  exact ret hk n s

theorem mixAt {k : Nat} (hk : 0<k) (s : Nat) (x : W k) (n : Nat) :
    readAt hk (mix hk s x) (n+s) =
      readAt hk x (n+s) + readAt hk x (n+s+s) + readAt hk x n := by
  change _+x (ix hk ((n+s)%k+s))+x (ix hk ((n+s)%k+k-s%k)) = _
  rw [idx_add]
  have hh : ix hk ((n+s)%k+k-s%k) = ix hk n := Fin.ext (ret hk n s)
  rw [hh]
  rfl

def trace {k : Nat} (hk : 0<k) : W k →ₗ[F] W k where
  toFun x i := readAt hk x i.val+readAt hk x (i.val+1)+readAt hk x (i.val+2)
  map_add' x y := by funext i; simp only [readAt,Pi.add_apply]; abel
  map_smul' c x := by ext i; simp [readAt,Pi.smul_apply,mul_add]

theorem traceAt {k : Nat} (hk : 0<k) (x : W k) (n : Nat) :
    readAt hk (trace hk x) n = readAt hk x n+readAt hk x (n+1)+readAt hk x (n+2) := by
  change x (ix hk (n%k))+x (ix hk (n%k+1))+x (ix hk (n%k+2)) = _
  rw [idx_add,idx_add]
  simp [ix,readAt]

theorem rowAt {k : Nat} (hk : 0<k) (x : W k) (n : Nat) :
    readAt hk (mix hk 1 (rot hk 1 x)) (n+2) = readAt hk (trace hk x) n := by
  rw [traceAt, mixAt hk 1 _ (n+1), rotAt hk 1 x (n+1), rotAt hk 1 x (n+2), rotAt hk 1 x n]
  abel

theorem columnAt {k : Nat} (hk : 0<k) (x : W k) (n : Nat) :
    readAt hk (mix hk 2 (rot hk 3 x)) (n+5) =
      readAt hk (trace hk x) n+readAt hk (trace hk x) (n+1)+readAt hk (trace hk x) (n+2) := by
  rw [mixAt hk 2 _ (n+3), rotAt hk 3 x (n+2),rotAt hk 3 x (n+4),rotAt hk 3 x n]
  simp only [traceAt]
  have h1 := doubleF (readAt hk x (n+1))
  have h2 := doubleF (readAt hk x (n+2))
  have h3 := doubleF (readAt hk x (n+3))
  linear_combination -h1-h2-h3

theorem traceInj {k : Nat} (hk : 0<k) (hmod : k%3 ≠ 0) :
    Function.Injective (trace hk) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hzero : trace hk x = 0 := hx
  let u := readAt hk x
  have eq : ∀ n, u n + u (n+1) + u (n+2) = 0 := by
    intro n
    rw [← traceAt, hzero]
    rfl
  have p3 : Period 3 u := by
    intro n
    have h := eq n
    have h' := eq (n+1)
    linear_combination h'-h
  have shift : ∀ n, u (n+(k%3)) = u n := by
    intro n
    have z := per_reduce p3 k n
    rw [Nat.add_comm k n, Nat.add_comm (k%3) n] at z
    exact z.symm.trans (at_per hk x n)
  have p1 : ∀ n, u (n+1)=u n := by
    have bound := Nat.mod_lt k (by decide : 0<3)
    rcases (show k%3=1 ∨ k%3=2 by omega) with e|e
    · simpa only [e] using shift
    · intro n
      have he := shift (n+1)
      rw [e] at he
      exact he.symm.trans (p3 n)
  funext i
  have h := eq i.val
  rw [show u (i.val+2)=u (i.val+1) from p1 (i.val+1),p1, doubleF,zero_add] at h
  change x i = 0
  have hi : ix hk i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa [u,readAt,hi] using h

noncomputable def traceEquiv {k : Nat} (hk : 0<k) (hmod : k%3 ≠ 0) : W k ≃ₗ[F] W k :=
  LinearEquiv.ofBijective (trace hk) ⟨traceInj hk hmod, Finite.surjective_of_injective (traceInj hk hmod)⟩

def rowForm {k : Nat} (hk : 0<k) {D : Type*} [AddCommGroup D] [Module F D]
    (L : D →ₗ[F] W k) (n : Nat) : D →ₗ[F] F :=
  (LinearMap.proj (ix hk n)).comp ((trace hk).comp L)

theorem shiftedAdj {A : Type*} [Zero A] {k : Nat} (hk : 0<k) (f : Nat → A)
    (per : Period k f) (s : Nat) (hs : 1 ≤ s) (hs' : s ≤ k+1) :
    (∀ i : Fin k, Compat (f (i.val+1)) (f (i.val+2))) ↔ Adj (fun n => f (n+s)) := by
  constructor
  · intro h n
    have h' := h (ix hk (n+s-1))
    change Compat (f ((n+s-1)%k+1)) (f ((n+s-1)%k+2)) at h'
    rw [← per_reduce per _ 1,← per_reduce per _ 2,
      show n+s-1+1=n+s by omega, show n+s-1+2=n+1+s by omega] at h'
    exact h'
  · intro h i
    have h' := h (i.val+k+1-s)
    change Compat (f (i.val+k+1-s+s)) (f (i.val+k+1-s+1+s)) at h'
    rw [show i.val+k+1-s+s=i.val+1+k by omega,show i.val+k+1-s+1+s=i.val+2+k by omega, per, per] at h'
    exact h'

theorem translatedCriterion {k : Nat} (hk : 0<k) (big : 5≤k) {D : Type*}
    [AddCommGroup D] [Module F D] (L : D →ₗ[F] W k) (row col c₁ c₂ base : W k) :
    FlatAlong (output hk row col c₁ c₂) L base ↔
      Adj (rowForm hk L) ∧ Adj (fun n => rowForm hk L n+rowForm hk L (n+1)+rowForm hk L (n+2)) := by
  have per : ∀ s t, Period k (obs hk s t L) := by
    intro s t n
    have ixper : ix hk (n+k) = ix hk n := Fin.ext (Nat.add_mod_right n k)
    unfold obs
    rw [ixper]
  have r : (fun n => obs hk 1 1 L (n+2)) = rowForm hk L := by
    funext n
    ext u
    exact rowAt hk (L u) n
  have c : (fun n => obs hk 2 3 L (n+5)) =
      (fun n => rowForm hk L n+rowForm hk L (n+1)+rowForm hk L (n+2)) := by
    funext n
    ext u
    exact columnAt hk (L u) n
  rw [criterion, shiftedAdj hk _ (per 1 1) 2 (by decide) (by omega),
    shiftedAdj hk _ (per 2 3) 5 (by decide) (by omega),r,c]

theorem twiceMap {D : Type*} [AddCommGroup D] [Module F D] (a : D →ₗ[F] F) : a+a=0 := by
  ext u
  exact doubleF _

theorem upperDim {k : Nat} (hk : 0<k) (big : 5≤k) (hmod : k%3≠0)
    (U : Submodule F (W k)) (row col c₁ c₂ base : W k)
    (hf : FlatAlong (output hk row col c₁ c₂) U.subtype base) :
    Module.finrank F U ≤ k/3 := by
  classical
  let a := rowForm hk U.subtype
  let I := ↥(labels k a)
  let ev : U →ₗ[F] (I → F) :=
    {toFun := fun u j => j.val u
     map_add' := fun u v => by funext j; exact map_add j.val u v
     map_smul' := fun s u => by funext j; exact map_smul j.val s u}
  have inj : Function.Injective ev := by
    intro u v heq
    apply Subtype.ext
    apply traceInj hk hmod
    funext i
    have hix : ix hk i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    suffices hev : a i.val u=a i.val v by
      change (trace hk u.val) (ix hk i.val)=(trace hk v.val) (ix hk i.val) at hev
      simpa only [hix] using hev
    by_cases z : a i.val=0
    · rw [z];rfl
    · have j : a i.val ∈ labels k a := label_mem.mpr ⟨z,i.val,i.isLt,rfl⟩
      exact congrFun heq ⟨a i.val,j⟩
  have rank := LinearMap.finrank_le_finrank_of_injective inj
  have dim : Module.finrank F (I→F)=(labels k a).card := by
    rw [Module.finrank_fintype_fun_eq_card]; exact Fintype.card_coe _
  have per : Period k a := by
    intro n
    have ixper : ix hk (n+k) = ix hk n := Fin.ext (Nat.add_mod_right n k)
    change rowForm hk U.subtype (n+k) = rowForm hk U.subtype n
    unfold rowForm
    rw [ixper]
  have crit := (translatedCriterion hk big U.subtype row col c₁ c₂ base).mp hf
  rw [dim] at rank
  exact rank.trans (label_budget twiceMap k big a per crit.1 crit.2)


def blockTag (k r : Nat) : Nat := if r < 3*(k/3) then if r%3=2 then 0 else r/3+1 else 1

def tag (k n : Nat) : Nat := blockTag k (n%k)

theorem modSmall {k r d : Nat} (big : 5 ≤ k) (hr : r<k) (hd : d≤3) :
    (r+d)%k = if r+d<k then r+d else r+d-k := by
  split
  next h => exact Nat.mod_eq_of_lt h
  next h => rw [Nat.mod_eq_sub_mod (by omega : k≤r+d), Nat.mod_eq_of_lt (by omega)]

theorem tagPlus {k : Nat} (big : 5 ≤ k) (n d : Nat) (hd : d≤3) :
    tag k (n+d) = blockTag k (if n%k+d<k then n%k+d else n%k+d-k) := by
  unfold tag
  rw [← Nat.mod_add_mod n k d, modSmall big (Nat.mod_lt _ (by omega)) hd]

theorem tag_adj {k : Nat} (big : 5≤k) (n : Nat) :
    tag k n = 0 ∨ tag k (n+1) = 0 ∨ tag k n = tag k (n+1) := by
  rw [tagPlus big n 1 (by decide)]
  unfold tag blockTag
  have h := Nat.mod_lt n (show 0<k by omega)
  split_ifs <;> omega

theorem tag_zeroPair {k : Nat} (big : 5≤k) (n : Nat) (h : tag k (n+1)=0) :
    tag k n ≠ 0 ∧ tag k (n+2) ≠ 0 := by
  rw [tagPlus big n 1 (by decide)] at h
  rw [tagPlus big n 2 (by decide)]
  unfold tag blockTag at *
  have bound := Nat.mod_lt n (show 0<k by omega)
  split_ifs at * <;> omega

theorem tag_afterZero {k : Nat} (big : 5≤k) (n : Nat) (h : tag k n=0) :
    tag k (n+1)=tag k (n+2) := by
  rw [tagPlus big n 1 (by decide),tagPlus big n 2 (by decide)]
  unfold tag blockTag at *
  have bound := Nat.mod_lt n (show 0<k by omega)
  split_ifs at * <;> omega

theorem tag_beforeZero {k : Nat} (big : 5≤k) (n : Nat) (h : tag k (n+2)=0) :
    tag k n=tag k (n+1) := by
  rw [tagPlus big n 2 (by decide)] at h
  rw [tagPlus big n 1 (by decide)]
  unfold tag blockTag at *
  have bound := Nat.mod_lt n (show 0<k by omega)
  split_ifs at * <;> omega

theorem tag_sample {k : Nat} (big : 5≤k) (i : Fin (k/3)) :
    tag k (3*i.val) = i.val+1 := by
  have h := i.isLt
  have hk : 3*i.val<k := by omega
  unfold tag blockTag
  rw [Nat.mod_eq_of_lt hk, if_pos (by omega)]
  have hm : 3*i.val % 3=0 := by omega
  have hd : 3*i.val/3=i.val := by omega
  simp [hm,hd]

def patternVal {A : Type*} [Zero A] {k : Nat} (u : Fin (k/3) → A) (n : Nat) : A :=
  if h : tag k n = 0 then 0 else if h' : tag k n-1<k/3 then u ⟨tag k n-1,h'⟩ else 0

theorem pat_same {A : Type*} [Zero A] {k : Nat} (u : Fin (k/3) → A) {t v : Nat}
    (h : tag k t=tag k v) : patternVal u t=patternVal u v := by simp [patternVal,h]

theorem pat_zero {A : Type*} [Zero A] {k : Nat} (u : Fin (k/3) → A) {t : Nat}
    (h : tag k t=0) : patternVal u t=0 := by simp [patternVal,h]

theorem pattern_compatible {A : Type*} [AddCommGroup A] (char : ∀ v:A, v+v=0) {k : Nat}
    (big : 5≤k) (u : Fin (k/3) → A) (n : Nat) :
    let a := patternVal u
    (a n=0 ∨ a (n+1)=0 ∨ a n=a (n+1)) ∧
    (a n+a (n+1)+a (n+2)=0 ∨ a (n+1)+a (n+2)+a (n+3)=0 ∨
      a n+a (n+1)+a (n+2)=a (n+1)+a (n+2)+a (n+3)) := by
  dsimp only
  constructor
  · rcases tag_adj big n with h|h|h
    · exact Or.inl (pat_zero u h)
    · exact Or.inr (Or.inl (pat_zero u h))
    · exact Or.inr (Or.inr (pat_same u h))
  · by_cases h1 : tag k (n+1)=0
    · right; left
      rw [pat_zero u h1, ← pat_same u (tag_afterZero big (n+1) h1),zero_add,char]
    · by_cases h2 : tag k (n+2)=0
      · left
        rw [pat_zero u h2, ← pat_same u (tag_beforeZero big n h2),add_zero,char]
      · have e := ((tag_adj big (n+1)).resolve_left h1).resolve_left h2
        have e' := pat_same u e
        rw [← e', add_assoc (patternVal u n), char, add_zero, zero_add]
        rcases tag_adj big n with h|h|h
        · exact Or.inl (pat_zero u h)
        · exact (h1 h).elim
        · rcases tag_adj big (n+2) with q|q|q
          · exact (h2 q).elim
          · exact Or.inr (Or.inl (pat_zero u q))
          · exact Or.inr (Or.inr (pat_same u (h.trans (e.trans q))))


def design {k : Nat} (hk : 0<k) : W (k/3) →ₗ[F] W k where
  toFun u i := patternVal u i.val
  map_add' u v := by
    funext i
    change patternVal (u+v) i.val=patternVal u i.val+patternVal v i.val
    unfold patternVal
    split_ifs <;> simp
  map_smul' c u := by
    funext i
    change patternVal (c • u) i.val=c • patternVal u i.val
    unfold patternVal
    split_ifs <;> simp

theorem designAt {k : Nat} (hk : 0<k) (u : W (k/3)) (n : Nat) :
    readAt hk (design hk u) n = patternVal u n := by
  change patternVal u (n%k) = _
  apply pat_same
  simp [tag]

theorem designInj {k : Nat} (hk : 0<k) (big : 5≤k) : Function.Injective (design hk) := by
  intro u v eq
  funext i
  have h := congrArg (fun w => readAt hk w (3*i.val)) eq
  change readAt hk (design hk u) _ = readAt hk (design hk v) _ at h
  rw [designAt,designAt] at h
  simpa [patternVal, tag_sample big i, i.isLt] using h

def projections (k : Nat) (i : Fin (k/3)) : W (k/3) →ₗ[F] F := LinearMap.proj i

theorem pat_eval {k : Nat} (u : W (k/3)) (n : Nat) :
    (patternVal (projections k) n) u = patternVal u n := by
  unfold patternVal
  split_ifs <;> rfl

theorem lowerDim {k : Nat} (hk : 0<k) (big : 5≤k) (hmod : k%3≠0) (row col c₁ c₂ : W k) :
    ∃ U : Submodule F (W k), Module.finrank F U=k/3 ∧
      ∀ base, FlatAlong (output hk row col c₁ c₂) U.subtype base := by
  classical
  let e := traceEquiv hk hmod
  let L := e.symm.toLinearMap.comp (design hk)
  have inj : Function.Injective L := e.symm.injective.comp (designInj hk big)
  refine ⟨LinearMap.range L, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj inj, Module.finrank_fin_fun]
  · intro base
    have form : rowForm hk L = fun n => patternVal (projections k) n := by
      funext n
      apply LinearMap.ext
      intro u
      change readAt hk (e (e.symm (design hk u))) n = _
      rw [e.apply_symm_apply, designAt, pat_eval]
    have hf : FlatAlong (output hk row col c₁ c₂) L base := by
      apply (translatedCriterion hk big L row col c₁ c₂ base).mpr
      rw [form]
      exact ⟨fun n => (pattern_compatible twiceMap big (projections k) n).1,
        fun n => (pattern_compatible twiceMap big (projections k) n).2⟩
    obtain ⟨f,hf⟩ := hf
    let E := LinearEquiv.ofInjective L inj
    refine ⟨f.comp E.symm.toLinearMap, ?_⟩
    intro v
    have hv : L (E.symm v) = v.val := congrArg Subtype.val (E.apply_symm_apply v)
    have h := hf (E.symm v)
    rw [hv] at h
    exact h

end PEqualNP.Outside.L_meta_25639

open PEqualNP.Outside.L_meta_25639 in
theorem PEqualNP.Outside.L_meta_25639 : ∀ (k : Nat) (hk : 0 < k), 5 ≤ k → k % 3 ≠ 0 →
  let W := Fin k → ZMod 2
  let ix := fun i : Nat => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : Nat) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (d : Nat) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  ∀ row col c₁ c₂ : W,
    let out := fun (key : W) =>
      ((step (mix 1 (rot 1 key + row)) + key + c₁,
        step (mix 2 (rot 3 key + col)) + rot 4 key + c₂) : W × W)
    let flat := fun (U : Submodule (ZMod 2) W) (base : W) =>
      ∃ f : U →ₗ[ZMod 2] (W × W), ∀ u : U, out (base + u.val) = out base + f u
    (∀ (U : Submodule (ZMod 2) W) (base : W), flat U base →
      Module.finrank (ZMod 2) U ≤ k / 3) ∧
    ∃ U : Submodule (ZMod 2) W, Module.finrank (ZMod 2) U = k / 3 ∧ ∀ base, flat U base := by
  intro k hk big hmod
  dsimp only
  intro row col c₁ c₂
  change (∀ (U : Submodule F (W k)) (base : W k), FlatAlong (output hk row col c₁ c₂) U.subtype base →
      Module.finrank F U ≤ k/3) ∧ ∃ U : Submodule F (W k), Module.finrank F U = k/3 ∧
        ∀ base, FlatAlong (output hk row col c₁ c₂) U.subtype base
  exact ⟨fun U base hf => upperDim hk big hmod U row col c₁ c₂ base hf, lowerDim hk big hmod row col c₁ c₂⟩
