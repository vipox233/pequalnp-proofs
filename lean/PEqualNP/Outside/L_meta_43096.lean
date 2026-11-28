import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43096

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276677352 * 2 ^ 32 + 4276668608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x022898dc06371e52#64 ++ 0x08045131b80c6e3c#64 ++ 0x0679f9fc0e7f3e7d#64 ++ 0x580cf3f3f81cfe7c#64 : BitVec 256),
   (0x18924228308a6a84#64 ++ 0x00312484506114d5#64 ++ 0x399e4638718ffffb#64 ++ 0xfc733c8c70e31fff#64 : BitVec 256),
   (0xc145854581518518#64 ++ 0x01828b0a8b02a30a#64 ++ 0xc1e787c781f1c7f7#64 ++ 0xeb83cf0f8f03e38f#64 : BitVec 256),
   (0x6c07e806da01f060#64 ++ 0x12d80fd00db403e0#64 ++ 0xfe07f807fe01f86f#64 ++ 0xb7fc0ff00ffc03f0#64 : BitVec 256),
   (0xb7f800036dec0000#64 ++ 0x276ff00006dbd800#64 ++ 0xfff80007fffe005f#64 ++ 0x3ffff0000ffffc00#64 : BitVec 256),
   (0xffff77b000000000#64 ++ 0x47fffeef60000000#64 ++ 0xfffffff80000003f#64 ++ 0xc7fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [12, 8]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679f9fc0e7f3e7d 0x580cf3f3f81cfe7c

def z1 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x399e4638718ffffb 0xfc733c8c70e31fff

def z2 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe07f807fe01f86f 0xb7fc0ff00ffc03f0

def z3 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff80007fffe005f 0x3ffff0000ffffc00

def z4 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e787c781f1c7f7 0xeb83cf0f8f03e38f

def z5 : W := mkw 0xc36d159000000000 0x0186da2b20000000 0xc7fffff80000003f 0xc38ffffff0000000

def z6 : W := mkw 0x36b800026cac0000 0x266d700004d95800 0x3e7800047e7e005d 0x1c7cf00008fcfc00

def z7 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff80000003f 0xc7fffffff0000000

def z8 : W := mkw 0xbffa422b7dee6a84 0x277ff48456fbdcd5 0xfffe463fffffffff 0xfffffc8c7fffffff

def z9 : W := mkw 0xf7fd8547edfd8518 0x27effb0a8fdbfb0a 0xffff87c7ffffc7ff 0xffffff0f8fffff8f

def z10 : W := mkw 0x0000000b7dee6a84 0x2000000016fbdcd5 0x00000007ffffffc0 0x380000000fffffff

def z11 : W := mkw 0x0802422810026a84 0x00100484502004d5 0x380646387001ffeb 0xf4700c8c70e003ff

def z12 : W := mkw 0x93f800036dec0000 0x2527f00006dbd800 0x01f80007fffe0050 0x3803f0000ffffc00

def z13 : W := mkw 0x8140000000000000 0x0102800000000000 0xc1e0000000000017 0x0383c00000000000

def z14 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x000000040e7f3e40 0x18000000081cfe7c

def z15 : W := mkw 0x022898d406351452 0x08045131a80c6a28 0x0661b9c40e700004 0x000cc373881ce000

def z16 : W := mkw 0x1090000020880000 0x0021200000411000 0x3980000071800002 0x2473000000e30000

def z17 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e787c780700037 0xc383cf0f8f00e000

def z18 : W := mkw 0x000088049201f060 0x10000110092403e0 0x000000000001f800 0x00000000000003f0

def z19 : W := mkw 0x00008047edfd8518 0x200001008fdbfb0a 0x00000007ffffc7c0 0x380000000fffff8f

def z20 : W := mkw 0x1892422030886084 0x00312484406110c1 0x398606007180c182 0xa4730c0c00e30183

def z21 : W := mkw 0x93f810d925fe0e12 0x2d27f021b24bfc1c 0x01f801f801fe0610 0x4803f003f003fc0c

def z22 : W := mkw 0xf5d58547e9d98518 0x27ebab0a8fd3b30a 0xf9e787c7f1f1c7f7 0xeff3cf0f8fe3e38f

def z23 : W := mkw 0x0228189806261a42 0x08045031300c4c34 0x061878380e0e3808 0x100c30f0701c1c70

def z24 : W := mkw 0xc145050181408108 0x01828a0a03028102 0xc18606038180c182 0xa3830c0c07030183

def z25 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xf8060007fe01f842 0xb7f00c000ffc03f0

def z26 : W := mkw 0xb7f8000000000000 0x076ff00000000000 0xfff800000000001f 0x07fff00000000000

def z27 : W := mkw 0x00000008308a6a84 0x00000000106114d5 0x00184038718ffff9 0x7800308070e31fff

def z28 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfffe0607ffffc7ff 0xfffffc0c0fffff8f

def z29 : W := mkw 0x262898de4e371e52 0x0a4c5131bc9c6e3c 0xfe79f9fffe7f3e7f 0x7ffcf3f3fffcfe7c

def z30 : W := mkw 0x0228109000000000 0x0004502120000000 0x0679f9f80000003d 0x400cf3f3f0000000

def z31 : W := mkw 0xc36d9ddd87779f5a 0x0986db3bbb0eef3e 0xc7ffffff8fffffff 0xfb8fffffff1fffff

def z32 : W := mkw 0xfffff7f7edfd8518 0x67ffffefefdbfb0a 0xffffffffffffc7ff 0xffffffffffffff8f

def z33 : W := mkw 0xc145050101400000 0x01828a0a02028000 0xc1e787c781f00077 0xeb83cf0f8f03e000

def z34 : W := mkw 0xffff77b36dec0000 0x67fffeef66dbd800 0xfffffffffffe007f 0xfffffffffffffc00

def z35 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x006181c40e7f3e75 0x5800c303881cfe7c

def z36 : W := mkw 0xffffffb402011040 0x47ffffff68040220 0xfffffffc0e01387f 0xd7fffffff81c0270

def z37 : W := mkw 0x4a2f77b000000000 0x40945eef60000000 0x067ffff80000003d 0xc00cfffff0000000

def z38 : W := mkw 0xb5d0000369c80000 0x276ba00006d39000 0xf9800003f1800002 0x27f3000007e30000

def z39 : W := mkw 0x7c97622000000000 0x02f92ec440000000 0xff9ffe380000003f 0xc7ff3ffc70000000

def z40 : W := mkw 0x00000008308a6a84 0x00000000106114d5 0x00000000718fffc0 0x3800000000e31fff

def z41 : W := mkw 0x0228000004240000 0x0004500000084800 0x067800040e7e005d 0x180cf000081cfc00

def z42 : W := mkw 0x0000804400110410 0x0000010088002208 0x006181c400710675 0x4800c3038800e20c

def z43 : W := mkw 0x480777b000000000 0x40900eef60000000 0x0007fff800000020 0xc0000ffff0000000

def z44 : W := mkw 0x7c97ea26da01f060 0x12f92fd44db403e0 0xff9ffe3ffe01f87f 0xf7ff3ffc7ffc03f0

def z45 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x0601f8040e7f3e6d 0x180c03f0081cfe7c

def z46 : W := mkw 0x0228109004240000 0x0004502120084800 0x0679f9fc0e7e007d 0x580cf3f3f81cfc00

def z47 : W := mkw 0x8140804581518518 0x010281008b02a30a 0xc1e0000781f1c7d7 0x2b83c0000f03e38f

def z48 : W := mkw 0x6e2fe806de25f060 0x12dc5fd00dbc4be0 0xfe7ff807fe7ff87f 0xbffcfff00ffcfff0

def z49 : W := mkw 0x0228000000000000 0x0004500000000000 0x067800000000001d 0x000cf00000000000

def z50 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc186060781f1c7c2 0xab830c0c0f03e38f

def z51 : W := mkw 0xb5d000036dec0000 0x276ba00006dbd800 0xf9800007fffe0042 0x3ff300000ffffc00

def z52 : W := mkw 0x8140054101500518 0x0102800a8202a00a 0x006001c000700000 0x0000c0038000e000

def z53 : W := mkw 0x93f817b8208a0a84 0x4527f02f70411415 0x01f807f8018e0790 0x4803f00ff0031c0f

def z54 : W := mkw 0x0000804581518518 0x000001008b02a30a 0x006181c781f1c7f5 0x6800c3038f03e38f

def z55 : W := mkw 0x93f8000125ec0000 0x2527f000024bd800 0x39f8000071fe005b 0x3c73f00000e3fc00

def z56 : W := mkw 0x4807f8dc9213fe72 0x18900ff1b92427fc 0x0007f9f80001fe20 0xc0000ff3f00003fc

def z57 : W := mkw 0x6e2ff8dede37fe72 0x1adc5ff1bdbc6ffc 0xfe7ff9fffe7ffe7f 0xfffcfff3fffcfffc

def z58 : W := mkw 0x93f817f804360e12 0x4d27f02ff0086c1c 0x01f807f8007e0610 0x4803f00ff000fc0c

def z59 : W := mkw 0x1090000020880000 0x0021200000411000 0x39980000718e005b 0x3c73300000e31c00

def z60 : W := mkw 0xe76da807cf659060 0x37cedb500f9ecb20 0xc661b8078e700004 0x038cc3700f1ce000

def z61 : W := mkw 0x4005804581518518 0x00800b008b02a30a 0xc007800781f1c7e7 0xab800f000f03e38f

def z62 : W := mkw 0xfffffffede37fe72 0x5ffffffffdbc6ffc 0xfffffffffe7ffe7f 0xfffffffffffcfffc

def z63 : W := mkw 0x0000000000000000 0x0000000000000000 0x018606000181c7f3 0xe8030c0c0003038f

def z64 : W := mkw 0xdbff77b000000000 0x45b7feef60000000 0x01fffff800000030 0xc003fffff0000000

def z65 : W := mkw 0x0000884c36bf7ed6 0x08000110986d7efd 0x000000047fffffc0 0x3800000008ffffff

def z66 : W := mkw 0x1abadafc36bf7ed6 0x083575b5f86d7efd 0x3ffffffc7fffffff 0xfc7ffffff8ffffff

def z67 : W := mkw 0x0802422810026a84 0x00100484502004d5 0x000646380001ffa0 0xc0000c8c700003ff

def z68 : W := mkw 0xa76800034d640000 0x274ed000069ac800 0xc66000078e700004 0x038cc0000f1ce000

def z69 : W := mkw 0x1892422000000000 0x0031248440000000 0x399e46380000003b 0xc4733c8c70000000

def z70 : W := mkw 0xffffffb7ffedf060 0x77ffffff6fffdbe0 0xfffffffffffff87f 0xfffffffffffffff0

def z71 : W := mkw 0x0000880402011040 0x0000011008040220 0x0601f8040e01386d 0x100c03f0081c0270

def z72 : W := mkw 0x10900228208a0a84 0x0021200450411415 0x01980638018e0790 0x4803300c70031c0f

def z73 : W := mkw 0x7c97ea2efa8bfae4 0x12f92fd45df517f5 0xff9ffe3fff8fffff 0xffff3ffc7fff1fff

def z74 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfe780007fe7e000c 0x17fcf0000ffcfc00

def z75 : W := mkw 0x2c0268025a007060 0x125804d004b400e0 0x3e0078007e003808 0x147c00f000fc0070

def z76 : W := mkw 0x0000884402111450 0x0000011088042228 0x0661f9c40e713e7d 0x580cc3f3881ce27c

def z77 : W := mkw 0x10900228308a6a84 0x00212004506114d5 0x01980638718fffd0 0x7803300c70e31fff

def z78 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xffe7bfc000000006 0x87ffcf7f80000000

def z79 : W := mkw 0x4807672000000000 0x40900ece40000000 0x0006060000000000 0x80000c0c00000000

def z80 : W := mkw 0x000098dc02131e52 0x08000131b804263c 0x0001f9f800013e20 0x400003f3f000027c

def z81 : W := mkw 0xffff77b8308a6a84 0x47fffeef706114d5 0xfffffff8718fffff 0xfffffffff0e31fff

def z82 : W := mkw 0x3eba72b000000000 0x467d74e560000000 0x3e18783800000008 0x047c30f070000000

def z83 : W := mkw 0xe76d359000000000 0x47ceda6b20000000 0xc661b9c000000004 0x038cc37380000000

def z84 : W := mkw 0x4807600000000000 0x00900ec000000000 0x0007f80000000020 0x80000ff000000000

def z85 : W := mkw 0x7ebfe806feadf060 0x36fd7fd00dfd5be0 0xfe1ff807fe0ff86f 0xb7fc3ff00ffc1ff0

def z86 : W := mkw 0x4807f7f480118518 0x40900fefe900230a 0x0007fff80001c7a0 0xc0000ffff000038f

def z87 : W := mkw 0x836815d905760f1a 0x0906d02bb20aec1e 0x01f807f801fe0790 0x4803f00ff003fc0f

def z88 : W := mkw 0xa76898df4f771e52 0x2f4ed131be9eee3c 0xc679f9ff8e7f3e7d 0x5b8cf3f3ff1cfe7c

def z89 : W := mkw 0x589777b000000000 0x40b12eef60000000 0x399ffff80000003b 0xc4733ffff0000000

def z90 : W := mkw 0xb7f800034d640000 0x276ff000069ac800 0xfff800078e70001f 0x07fff0000f1ce000

def z91 : W := mkw 0x6c07ed46da11f578 0x12d80fda8db423ea 0xfe07ffc7fe01ffef 0xf7fc0fff8ffc03ff

def z92 : W := mkw 0xd9d74721b1c8e18c 0x01b3ae8e436391c3 0xf9860603f180c182 0xa7f30c0c07e30183

def z93 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x38184038700e3808 0x1470308070e01c70

def z94 : W := mkw 0xd9d7c76db1dbef9c 0x01b3af8edb63b7df 0xf9ffc7fff1ffffff 0xfff3ff8fffe3ffff

def z95 : W := mkw 0x4005854480118518 0x00800b0a8900230a 0x000787c00001c7a0 0xc0000f0f8000038f

def z96 : W := mkw 0x022890d400110410 0x00045121a8002208 0x0679f9fc0071067d 0x480cf3f3f800e20c

def z97 : W := mkw 0x1892422800020a00 0x0031248450000414 0x399e4638000f3e7b 0xdc733c8c70001e7c

def z98 : W := mkw 0x6c076002d800e020 0x12d80ec005b001c0 0xf8060003f000c002 0xa7f00c0007e00180

def z99 : W := mkw 0x93f817b000000000 0x4527f02f60000000 0x07f9fff80000003d 0x400ff3fff0000000

def z100 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x398646387181ffa2 0xe4730c8c70e303ff

def z101 : W := mkw 0xffff77b34d640000 0x67fffeef669ac800 0xffffffff8e70003f 0xc7ffffffff1ce000

def z102 : W := mkw 0xffffe807ffedf060 0x37ffffd00fffdbe0 0xfffff807fffff87f 0xbffffff00ffffff0

def z103 : W := mkw 0x080272b000000000 0x401004e560000000 0x0000783800000000 0x000000f070000000

def z104 : W := mkw 0x64052002c8008020 0x12c80a4005900100 0xc000000380000000 0x0380000007000000

def z105 : W := mkw 0xc145054181508518 0x01828a0a8302a10a 0xc1e607c381f0c792 0xeb83cc0f8703e18f

def z106 : W := mkw 0x3490000268880000 0x2669200004d11000 0x3800000070000000 0x0470000000e00000

def z107 : W := mkw 0x0000884ede37fe72 0x180001109dbc6ffc 0x00000007fe7ffe40 0x380000000ffcfffc

def z108 : W := mkw 0x4005854480118518 0x00800b0a8900230a 0x006787c40071c7f5 0xc800cf0f8800e38f

def z109 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0079f9f8007f3e30 0x4800f3f3f000fe7c

def z110 : W := mkw 0x000000036dec0000 0x2000000006dbd800 0x00000007fffe0040 0x380000000ffffc00

def z111 : W := mkw 0x4807e8049201f060 0x10900fd0092403e0 0x0007f8000001f820 0x80000ff0000003f0

def z112 : W := mkw 0x2c02600000000000 0x025804c000000000 0x3e00780000000008 0x047c00f000000000

def z113 : W := mkw 0x4005000080008000 0x00800a0001000100 0xc00600038000c002 0xa3800c0007000180

def z114 : W := mkw 0xfffff7f581518518 0x47ffffefeb02a30a 0xffffffff81f1c7ff 0xefffffffff03e38f

def z115 : W := mkw 0x0228000804260a00 0x0004500010084c14 0x0678403c0e7f3e7d 0x580cf080781cfe7c

def z116 : W := mkw 0x0000804581518518 0x000001008b02a30a 0x0000000781f1c7c0 0x280000000f03e38f

def z117 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfe79f9f80000000c 0x07fcf3f3f0000000

def z118 : W := mkw 0x0000804db1dbef9c 0x000001009b63b7df 0x00000007f1ffffc0 0x380000000fe3ffff

def z119 : W := mkw 0xc36d95d581518518 0x0186db2bab02a30a 0xc7ffffff81f1c7ff 0xeb8fffffff03e38f

def z120 : W := mkw 0x1aba52b000000000 0x003574a560000000 0x3ffffff80000003f 0xc47ffffff0000000

def z121 : W := mkw 0xb7f810936dec0000 0x276ff02126dbd800 0xfff9f9fffffe007f 0x7ffff3f3fffffc00

def z122 : W := mkw 0x2c0268025a007060 0x125804d004b400e0 0x3e0678007e01f86b 0xb47c0cf000fc03f0

def z123 : W := mkw 0x2400000248000000 0x0248000004900000 0xfe000007fe00004f 0x37fc00000ffc0000

def z124 : W := mkw 0x2e2af8de5e377e72 0x1a5c55f1bcbc6efc 0x3e79f9fc7e7f3e7d 0x5c7cf3f3f8fcfe7c

def z125 : W := mkw 0x1892422020880000 0x0031248440411000 0x399e4638718e007b 0xfc733c8c70e31c00

def z126 : W := mkw 0xb7f888076fed1040 0x276ff1100edfda20 0xfff9f807ffff387f 0x3ffff3f00ffffe70

def z127 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xc607f8078e01f824 0x838c0ff00f1c03f0

def z128 : W := mkw 0xc145050000000000 0x01828a0a00000000 0xc1e787c000000037 0xc383cf0f80000000

def z129 : W := mkw 0xffffffbefa8bfae4 0x57ffffff7df517f5 0xffffffffff8fffff 0xffffffffffff1fff

def z130 : W := mkw 0xfffff7fdb1dbef9c 0x47ffffeffb63b7df 0xfffffffff1ffffff 0xffffffffffe3ffff

def z131 : W := mkw 0x36b800026cac0000 0x266d700004d95800 0x3e1800007e0e0008 0x147c300000fc1c00

def z132 : W := mkw 0x000098dc06371e52 0x08000131b80c6e3c 0x0001f9fc0e7f3e60 0x580003f3f81cfe7c

def z133 : W := mkw 0xc145050181408108 0x01828a0a03028102 0xc18606038181c7f3 0xeb830c0c0703038f

def z134 : W := mkw 0xbffa42237dec6084 0x277ff48446fbd8c1 0xfffe0607fffec1df 0xbffffc0c0ffffd83

def z135 : W := mkw 0x0802422010006084 0x00100484402000c1 0x000606000000c180 0x80000c0c00000183

def z136 : W := mkw 0x1aba52f834be6e96 0x083574a5f0697cdd 0x39fe47f871fffffb 0xfc73fc8ff0e3ffff

def z137 : W := mkw 0x7c976222f888e0a4 0x12f92ec445f111c1 0xf9860603f180c182 0xa7f30c0c07e30183

def z138 : W := mkw 0x3eba422a7cae6a84 0x267d748454f95cd5 0x3f9e46387f8ffffb 0xfc7f3c8c70ff1fff

def z139 : W := mkw 0x0802400010006000 0x00100480002000c0 0x380640007001f86b 0xb4700c8000e003f0

def z140 : W := mkw 0x1892422030886084 0x00312484406110c1 0x398606007181c7f3 0xec730c0c00e3038f

def z141 : W := mkw 0x0228109000000000 0x0004502120000000 0x0618783800000008 0x000c30f070000000

def z142 : W := mkw 0x8368000105640000 0x2506d000020ac800 0x0060000000700000 0x0000c0000000e000

def z143 : W := mkw 0xef6fe807df65f060 0x37dedfd00fbecbe0 0xfe67f807fe71f86f 0xb7fccff00ffce3f0

def z144 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc06181c781f1c7c4 0x2b80c3038f03e38f

def z145 : W := mkw 0x8140054101500518 0x0102800a8202a00a 0x01e607c001f1c7f3 0xe803cc0f8003e38f

def z146 : W := mkw 0x022898d406351452 0x08045131a80c6a28 0x0661b9c40e710675 0x480cc373881ce20c

def z147 : W := mkw 0x3c926a2a7a8a7ae4 0x127924d454f514f5 0x3f9e7e387f8ffffb 0xfc7f3cfc70ff1fff

def z148 : W := mkw 0xffff77b26cac0000 0x67fffeef64d95800 0xfffffff87e0e003f 0xd7fffffff0fc1c00

def z149 : W := mkw 0x0000004804360e12 0x0800000090086c1c 0x00000000007e0600 0x080000000000fc0c

def z150 : W := mkw 0xfdd7ef26da01f060 0x57fbafde4db403e0 0xff87fe07fe01f86f 0xb7ff0ffc0ffc03f0

def z151 : W := mkw 0x4005359000000000 0x40800a6b20000000 0x0001b9c000000000 0x0000037380000000

def z152 : W := mkw 0xef6f77b000000000 0x47dedeef60000000 0xc667fff800000024 0xc38ccffff0000000

def z153 : W := mkw 0x0000000800020a00 0x0000000010000414 0x00000000000f3e40 0x1800000000001e7c

def z154 : W := mkw 0x12b812f824be0e96 0x08257025f0497c1d 0x01f807f801fe0790 0x4803f00ff003fc0f

def z155 : W := mkw 0x8140854501510518 0x0102810a8a02a20a 0x01e187c401f107f5 0x4803c30f8803e20f

def z156 : W := mkw 0x022800036dec0000 0x2004500006dbd800 0x06780007fffe005d 0x380cf0000ffffc00

def z157 : W := mkw 0xffff77b125ec0000 0x67fffeef624bd800 0xfffffff801fe003f 0xcffffffff003fc00

def z158 : W := mkw 0x36b800026cac0000 0x266d700004d95800 0x3f9800007f8e005b 0x3c7f300000ff1c00

def z159 : W := mkw 0x262800024c240000 0x024c500004984800 0xfe780007fe7e005f 0x3ffcf0000ffcfc00

def z160 : W := mkw 0xef6ffd96da01f060 0x57dedffb2db403e0 0xfe67f9c7fe01f86f 0xb7fccff38ffc03f0

def z161 : W := mkw 0xe545ad47cb519578 0x13ca8b5a8f96a32a 0xc661b9c78e700004 0x038cc3738f1ce000

def z162 : W := mkw 0x8140054101500518 0x0102800a8202a00a 0x01e007c001f00790 0x4803c00f8003e00f

def z163 : W := mkw 0xffff77b030886084 0x47fffeef606110c1 0xfffffff87180c1bf 0xe7fffffff0e30183

def z164 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679f9fc0e7e380c 0x100cf3f3f81cfc70

def z165 : W := mkw 0x93f8054125fc0518 0x2527f00a824bf80a 0x01f807c001fe0790 0x4803f00f8003fc0f

def z166 : W := mkw 0x8140000101400000 0x0102800002028000 0xc1e0000781f00057 0x2b83c0000f03e000

def z167 : W := mkw 0xfffffffc06371e52 0x4ffffffff80c6e3c 0xfffffffc0e7f3e7f 0xdffffffff81cfe7c

def z168 : W := mkw 0x12b89afc26bf1ed6 0x08257135f84d7e3d 0x07f9fffc0fff3ffd 0x580ff3fff81ffe7f

def z169 : W := mkw 0x4005800480018000 0x00800b0009000300 0xc00780078001c067 0xa3800f000f000380

def z170 : W := mkw 0xed47ed47db51f578 0x13da8fda8fb6a3ea 0xffe7ffc7fff1ffff 0xffffcfff8fffe3ff

def z171 : W := mkw 0x240000036dec0000 0x2248000006dbd800 0xfe000007fffe004f 0x3ffc00000ffffc00

def z172 : W := mkw 0x93f817b000000000 0x4527f02f60000000 0x01f807f800000010 0x4003f00ff0000000

def z173 : W := mkw 0x4005854581518518 0x00800b0a8b02a30a 0x000787c781f1c7e0 0xe8000f0f8f03e38f

def z174 : W := mkw 0xfdd7672000000000 0x47fbaece40000000 0xf986060000000002 0x87f30c0c00000000

def z175 : W := mkw 0x00008806da01f060 0x100001100db403e0 0x00000007fe01f840 0x300000000ffc03f0

def z176 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z177 : W := mkw 0x1aba5ab836ae7ac6 0x083574b5706d5cf5 0x3e1878387e0e3808 0x147c30f070fc1c70

def z178 : W := mkw 0x6405a806ca019060 0x12c80b500d940320 0xc601b8078e000004 0x038c03700f1c0000

def z179 : W := mkw 0x0802400010006000 0x00100480002000c0 0x398646007181fffb 0xfc730c8c00e303ff

def z180 : W := mkw 0xb7f817b36dec0000 0x676ff02f66dbd800 0xfff807fffffe005f 0x7ffff00ffffffc00

def z181 : W := mkw 0x0000000800020a00 0x0000000010000414 0x0000403800013e20 0x400000807000027c

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x0186060000000033 0xc0030c0c00000000

def z183 : W := mkw 0x0228109800020a00 0x0004502130000414 0x0679f9f8000f3e7d 0x580cf3f3f0001e7c

def z184 : W := mkw 0x662db8d6ce359472 0x1acc5b71ad9c6b28 0xc661b9c78e700004 0x038cc3738f1ce000

def z185 : W := mkw 0x480760009000e020 0x10900ec0012001c0 0x000600000000c000 0x80000c0000000180

def z186 : W := mkw 0x0000884c02131e52 0x080001109804263c 0x0000000000013e00 0x000000000000027c

def z187 : W := mkw 0x6c076002d800e020 0x12d80ec005b001c0 0xfe07f803f000c02f 0xa7fc0ff007e00180

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x000606000001c7a0 0xc0000c0c0000038f

def z189 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0x3e07f8007e01f828 0x947c0ff000fc03f0

def z190 : W := mkw 0xed47ed07db41f168 0x13da8fda0fb683e2 0xff87fe07ff81f9ef 0xb7ff0ffc0fff03f3

def z191 : W := mkw 0x000098dc02131e52 0x08000131b804263c 0x0061f9fc00713e75 0x4800c3f3f800e27c

def z192 : W := mkw 0x7c97ea26fa89f0e4 0x12f92fd44df513e1 0xff87fe07ff81f9ef 0xb7ff0ffc0fff03f3

def z193 : W := mkw 0x10900228208a0a84 0x0021200450411415 0x01984638018f3ff9 0x5803308c70031e7f

def z194 : W := mkw 0x6405200000000000 0x02c80a4000000000 0xc601b80000000004 0x038c037000000000

def z195 : W := mkw 0x4005000000000000 0x00800a0000000000 0xc007800000000027 0x83800f0000000000

def z196 : W := mkw 0xc36d9dd58775955a 0x0986db3bab0eeb2a 0xc661b9c78e700004 0x038cc3738f1ce000

def z197 : W := mkw 0x022810d804360e12 0x08045021b0086c1c 0x007801f8007e0610 0x4800f003f000fc0c

def z198 : W := mkw 0xfdd7672030886084 0x47fbaece406110c1 0xf98606007180c182 0xa7f30c0c00e30183

def z199 : W := mkw 0xffff77f101500518 0x47fffeefe202a00a 0xfffffff801f007bf 0xcffffffff003e00f

def z200 : W := mkw 0xffffffb6da01f060 0x57ffffff6db403e0 0xfffffffffe01f87f 0xf7fffffffffc03f0

def z201 : W := mkw 0x4a2ffffc06371e52 0x48945ffff80c6e3c 0x067ffffc0e7f3e7d 0xd80cfffff81cfe7c

def z202 : W := mkw 0xf7fd05036dec0000 0x27effa0a06dbd800 0xffff87c7fffe007f 0xffffff0f8ffffc00

def z203 : W := mkw 0x0000000800020a00 0x0000000010000414 0x00184038000f3e79 0x5800308070001e7c

def z204 : W := mkw 0xffff77b248000000 0x47fffeef64900000 0xfffffffffe00007f 0xf7fffffffffc0000

def z205 : W := mkw 0x93f8000125ec0000 0x2527f000024bd800 0x01f8000001fe0010 0x0803f0000003fc00

def z206 : W := mkw 0xb7f8884f6fff1e52 0x2f6ff1109edffe3c 0xfff80007ffff3e5f 0x3ffff0000ffffe7c

def z207 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0661b9c40e7f3e44 0x180cc373881cfe7c

def z208 : W := mkw 0xd9d7c76581518518 0x01b3af8ecb02a30a 0xf9ffc7ff81f1c7ff 0xeff3ff8fff03e38f

def z209 : W := mkw 0x93f8000125ec0000 0x2527f000024bd800 0xc1f8000781fe0057 0x2b83f0000f03fc00

def z210 : W := mkw 0xa76800034d640000 0x274ed000069ac800 0xc67800078e7e005d 0x1b8cf0000f1cfc00

def z211 : W := mkw 0xc145050181408108 0x01828a0a03028102 0xc1e6060781f0c1d7 0xab83cc0c0f03e183

def z212 : W := mkw 0x2400000000000000 0x0248000000000000 0xfe0000000000000f 0x07fc000000000000

def z213 : W := mkw 0xffff77b101400000 0x47fffeef62028000 0xffffffff81f0007f 0xefffffffff03e000

def z214 : W := mkw 0x662db8dece379e72 0x1acc5b71bd9c6f3c 0xc679f9ff8e7f3e7d 0x5b8cf3f3ff1cfe7c

def z215 : W := mkw 0xd1d58545a1d98518 0x01a3ab0a8b43b30a 0xf9ff87c7f1ffc7ff 0xfff3ff0f8fe3ff8f

def z216 : W := mkw 0xffff77b8308a6a84 0x47fffeef706114d5 0xfffffff8700e383f 0xd7fffffff0e01c70

def z217 : W := mkw 0xd3fd8545a5fd8518 0x25a7fb0a8b4bfb0a 0xc1ff87c781ffc7f7 0xeb83ff0f8f03ff8f

def z218 : W := mkw 0x36b898de6ebf1e52 0x2e6d7131bcdd7e3c 0x3e79f9fc7e7f3e7d 0x5c7cf3f3f8fcfe7c

def z219 : W := mkw 0x0000000000000000 0x0000000000000000 0x018606000180c182 0xa0030c0c00030183

def z220 : W := mkw 0xc145850581418108 0x01828b0a0b028302 0xc18786078181c1e7 0xa3830f0c0f030383

def z221 : W := mkw 0x4005854480118518 0x00800b0a8900230a 0x018787c00181c7f3 0xe8030f0f8003038f

def z222 : W := mkw 0xe76d359000000000 0x47ceda6b20000000 0xc7e7bfc000000037 0xc38fcf7f80000000

def z223 : W := mkw 0xffffe806da01f060 0x17ffffd00db403e0 0xfffff807fe01f87f 0xb7fffff00ffc03f0

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018403800000039 0x4000308070000000

def z225 : W := mkw 0xa76800034d640000 0x274ed000069ac800 0xfe600007fe70004f 0x37fcc0000ffce000

def z226 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc06181c780700004 0x0380c3038f00e000

def z227 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0x01e787c001f1c7b0 0xc803cf0f8003e38f

def z228 : W := mkw 0x422d98dc86379e52 0x08845b31b90c6f3c 0xc67ff9ff8e7ffe7f 0xfb8cfff3ff1cfffc

def z229 : W := mkw 0x1892dafc329b7ed6 0x083125b5f86536fd 0x399ffff8718ffffb 0xfc733ffff0e31fff

def z230 : W := mkw 0x1090000000000000 0x0021200000000000 0x399800000000001b 0x0473300000000000

def z231 : W := mkw 0xed47ed47db51f578 0x13da8fda8fb6a3ea 0xfe67f9c7fe71f86f 0xb7fccff38ffce3f0

def z232 : W := mkw 0x6c07e80402011040 0x02d80fd008040220 0xfe07f8040e01386f 0x97fc0ff0081c0270

def z233 : W := mkw 0x4807c0049001e000 0x00900f80092003c0 0xf807c007f001f86f 0xb7f00f800fe003f0

def z234 : W := mkw 0xef6f759000000000 0x47dedeeb20000000 0xfe67f9c00000002f 0x87fccff380000000

def z235 : W := mkw 0x262800024c240000 0x264c500004984800 0x060000000e000000 0x000c0000001c0000

def z236 : W := mkw 0xffff600000000000 0x07fffec000000000 0xfffff8000000003f 0x87fffff000000000

def z237 : W := mkw 0x99d2476931da6f9c 0x0133a48ed263b4df 0x39fe47f871fffffb 0xfc73fc8ff0e3ffff

def z238 : W := mkw 0x0000109000000000 0x0000002120000000 0x0001f9f800000020 0x400003f3f0000000

def z239 : W := mkw 0xc145854d81538f18 0x01828b0a9b02a71e 0xc1ffc7ff81ffffff 0xfb83ff8fff03ffff

def z240 : W := mkw 0x240028024a001060 0x1248005004940020 0x060038000e000000 0x000c0070001c0000

def z241 : W := mkw 0xed47e547d951e538 0x13da8fca8fb2a3ca 0xf9e787c7f1f1c7f7 0xeff3cf0f8fe3e38f

def z242 : W := mkw 0x0000880402011040 0x0000011008040220 0x0001f80000013820 0x000003f000000270

def z243 : W := mkw 0x0000000810026a84 0x00000000102004d5 0x000000000001ff80 0x00000000000003ff

def z244 : W := mkw 0x5897c22cb08bea84 0x00b12f84596117d5 0xf99fc63ff18fffff 0xfff33f8c7fe31fff

def z245 : W := mkw 0x1892422010006000 0x00312484402000c0 0x399e46387001f87b 0xf4733c8c70e003f0

def z246 : W := mkw 0xffffea2fffeffae4 0x37ffffd45fffdff5 0xfffffe3fffffffff 0xfffffffc7fffffff

def z247 : W := mkw 0x3eba7ab25a007060 0x567d74f564b400e0 0x3e1878387e003808 0x147c30f070fc0070

def z248 : W := mkw 0x0000804480118518 0x000001008900230a 0x000000000001c780 0x000000000000038f

def z249 : W := mkw 0xc1458d4583519558 0x01828b1a8b06a32a 0xc7e7ffc78ff1ffff 0xfb8fcfff8f1fe3ff

def z250 : W := mkw 0x4807fffc02131e52 0x48900ffff804263c 0x0007fff800013e20 0xc0000ffff000027c

def z251 : W := mkw 0x3eba72b26cac0000 0x667d74e564d95800 0x3e1878387e0e0008 0x147c30f070fc1c00

def z252 : W := mkw 0x7ebffafefebffef6 0x1afd7ff5fdfd7ffd 0xffffffffffffffff 0xffffffffffffffff

def z253 : W := mkw 0xffff77b004240000 0x47fffeef60084800 0xfffffffc0e7e007f 0xdffffffff81cfc00

def z254 : W := mkw 0xf7fd8547edfd8518 0x27effb0a8fdbfb0a 0xfff981c7fffe005f 0x3ffff3038ffffc00

def z255 : W := mkw 0xb7f8000125ec0000 0x276ff000024bd800 0xfff8000001fe001f 0x0ffff0000003fc00

def z256 : W := mkw 0xfdd76722d800e020 0x57fbaece45b001c0 0xf9860603f000c002 0xa7f30c0c07e00180

def z257 : W := mkw 0x10900008308a6a84 0x00212000106114d5 0x39980000718fffdb 0x3c73300000e31fff

def z258 : W := mkw 0xbffa72b36dec0000 0x677ff4e566dbd800 0xfff8783ffffe005f 0x3ffff0f07ffffc00

def z259 : W := mkw 0x1090022000000000 0x0021200440000000 0x0198063800000010 0x4003300c70000000

def z260 : W := mkw 0x589777b8308a6a84 0x40b12eef706114d5 0x399ffff8718ffffb 0xfc733ffff0e31fff

def z261 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x399e0638718ec792 0xec733c0c70e31d8f

def z262 : W := mkw 0xe5458547c9518518 0x03ca8b0a8f92a30a 0xffe787c7fff1c7ff 0xffffcf0f8fffe38f

def z263 : W := mkw 0x022818d806361e52 0x08045031b00c6c3c 0x067879f80e7e3e18 0x580cf0f3f01cfc7c

def z264 : W := mkw 0x1892422810026a84 0x00312484502004d5 0x399e46380001ffbb 0xc4733c8c700003ff

def z265 : W := mkw 0x3eba72b000000000 0x467d74e560000000 0x3f9e7e380000003b 0xc47f3cfc70000000

def z266 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x381e4038700ff86b 0xb4703c8070e01ff0

def z267 : W := mkw 0x2c02e806da01f060 0x125805d00db403e0 0x3e007807fe01f848 0x347c00f00ffc03f0

def z268 : W := mkw 0xfdd7672000000000 0x47fbaece40000000 0xf99e46380000003b 0xc7f33c8c70000000

def z269 : W := mkw 0x0802400010006000 0x00100480002000c0 0x380600007000c002 0xa4700c0000e00180

def z270 : W := mkw 0xfdd7ef6ffbdbfffc 0x13fbafdedff7b7ff 0xffffffffffffffff 0xffffffffffffffff

def z271 : W := mkw 0xbffa42236dec0000 0x277ff48446dbd800 0xfffe463ffffe007f 0xfffffc8c7ffffc00

def z272 : W := mkw 0x36b8000000000000 0x066d700000000000 0x3e18000000000008 0x047c300000000000

def z273 : W := mkw 0x4005050000000000 0x00800a0a00000000 0x000787c000000020 0xc0000f0f80000000

def z274 : W := mkw 0xb7f88047edfd8518 0x276ff1008fdbfb0a 0xfff80007ffffc7df 0x3ffff0000fffff8f

def z275 : W := mkw 0x0000000004240000 0x0000000000084800 0x000000040e7e0040 0x18000000081cfc00

def z276 : W := mkw 0x6c07e806ca019060 0x12d80fd00d940320 0xfe07f8078e00002f 0x87fc0ff00f1c0000

def z277 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xf807f803f001f822 0xa7f00ff007e003f0

def z278 : W := mkw 0x240088064a011040 0x024801100c940220 0xfe01f807fe01386f 0x37fc03f00ffc0270

def z279 : W := mkw 0x4a2ff8dc9637fe72 0x18945ff1b92c6ffc 0x067ff9fc0e7ffe7d 0xd80cfff3f81cfffc

def z280 : W := mkw 0xe545250000000000 0x47ca8a4a00000000 0xc000000000000000 0x0380000000000000

def z281 : W := mkw 0x1aba422834ae6a84 0x0035748450695cd5 0x3ffe463c7fffffff 0xfc7ffc8c78ffffff

def z282 : W := mkw 0xb5d0000369c80000 0x276ba00006d39000 0xf9e00007f1f00057 0x2ff3c0000fe3e000

def z283 : W := mkw 0x6405a806ca019060 0x12c80b500d940320 0xfe01b807fe00004f 0x37fc03700ffc0000

def z284 : W := mkw 0x0228000004240000 0x0004500000084800 0x061800000e0e0008 0x100c3000001c1c00

def z285 : W := mkw 0xe76dbdd406351452 0x4fcedb7ba80c6a28 0xc661b9c40e700004 0x038cc373881ce000

def z286 : W := mkw 0xffff67236dec0000 0x67fffece46dbd800 0xfffe0607fffe005f 0xbffffc0c0ffffc00

def z287 : W := mkw 0xa768000000000000 0x074ed00000000000 0xc660000000000004 0x038cc00000000000

def z288 : W := mkw 0x0000054000100518 0x0000000a8000200a 0x000007c000000780 0x4000000f8000000f

def z289 : W := mkw 0x022890dc04370e12 0x08045121b8086e1c 0x007981fc007f0675 0x4800f303f800fe0c

def z290 : W := mkw 0x6c07f8deda13fe72 0x1ad80ff1bdb427fc 0xfe07f9fffe01fe6f 0xf7fc0ff3fffc03fc

def z291 : W := mkw 0xfffffffc02131e52 0x4ffffffff804263c 0xfffffff800013e3f 0xc7fffffff000027c

def z292 : W := mkw 0x0000804400110410 0x0000010088002208 0x0000000400710640 0x080000000800e20c

def z293 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x38184038700f3e79 0x5c70308070e01e7c

def z294 : W := mkw 0x1892422030886084 0x00312484406110c1 0x399e46387180c1bb 0xe4733c8c70e30183

def z295 : W := mkw 0x10900228208a0a84 0x0021200450411415 0x00180038000e0000 0x0000300070001c00

def z296 : W := mkw 0x1892c26db1dbef9c 0x00312584db63b7df 0x399e463ff1fffffb 0xfc733c8c7fe3ffff

def z297 : W := mkw 0x0000000800020a00 0x0000000010000414 0x019e4638018ffffb 0xf8033c8c70031fff

def z298 : W := mkw 0x1892422b7dee6a84 0x2031248456fbdcd5 0x399e463ffffffffb 0xfc733c8c7fffffff

def z299 : W := mkw 0x6c07e807ffedf060 0x32d80fd00fffdbe0 0xfe07f807fffff86f 0xbffc0ff00ffffff0

def z300 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xf9f80003f1fe0012 0x2ff3f00007e3fc00

def z301 : W := mkw 0xb7f8000369c80000 0x276ff00006d39000 0xfff80003f180001f 0x27fff00007e30000

def z302 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xff87fe07ff81ffff 0xffff0ffc0fff03ff

def z303 : W := mkw 0xfffff7b480018000 0x47ffffef69000300 0xffffffff8001c07f 0xe7ffffffff000380

def z304 : W := mkw 0x0000000000000000 0x0000000000000000 0x0601f8000000002d 0x000c03f000000000

def z305 : W := mkw 0x6c076802da00f060 0x12d80ed005b401e0 0xfe067803fe00f80a 0xb7fc0cf007fc01f0

def z306 : W := mkw 0xd9d74729b1caeb8c 0x01b3ae8e536395d7 0xf99e463bf18ffffb 0xfff33c8c77e31fff

def z307 : W := mkw 0xbffa4228308a6a84 0x077ff484506114d5 0xfffe4638718fffff 0xfffffc8c70e31fff

def z308 : W := mkw 0xfdd7672181408108 0x47fbaece43028102 0xf98606038180c182 0xa7f30c0c07030183

def z309 : W := mkw 0xdbffdffdb7ffffde 0x09b7ffbffb6fffff 0xffffffffffffffff 0xffffffffffffffff

def z310 : W := mkw 0xb7f898df6fff1e52 0x2f6ff131bedffe3c 0xfff9f9ffffff3e7f 0x7ffff3f3fffffe7c

def z311 : W := mkw 0xffffffb6ca019060 0x57ffffff6d940320 0xffffffff8e00003f 0xc7ffffffff1c0000

def z312 : W := mkw 0x12b898dc26bf1e52 0x08257131b84d7e3c 0x3ff9f9fc7fff3e7f 0x7c7ff3f3f8fffe7c

def z313 : W := mkw 0xf7fd35936dec0000 0x67effa6b26dbd800 0xfff9b9c7fffe005f 0x3ffff3738ffffc00

def z314 : W := mkw 0xe76db5d581518518 0x47cedb6bab02a30a 0xc7e7bfc781f1c7f7 0xeb8fcf7f8f03e38f

def z315 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000780000047 0x238000000f000000

def z316 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000010671 0x480000000000020c

def z317 : W := mkw 0x6e2ff8dc06371e52 0x0adc5ff1b80c6e3c 0xfe7ff9fc0e7f3e7f 0xdffcfff3f81cfe7c

def z318 : W := mkw 0xc36d95dd85778f1a 0x0986db2bbb0aef1e 0xc1ff87ff81ffc7f7 0xeb83ff0fff03ff8f

def z319 : W := mkw 0x1892c26c309b6e94 0x00312584d86136dd 0x39ffc7fc71ffffff 0xfc73ff8ff8e3ffff

def z320 : W := mkw 0xb7f805436dfc0518 0x276ff00a86dbf80a 0xfff807c7fffe07df 0x7ffff00f8ffffc0f

def z321 : W := mkw 0x022898d406351452 0x08045131a80c6a28 0x0679f9fc0e70003d 0x400cf3f3f81ce000

def z322 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0x3ff800007ffe0018 0x1c7ff00000fffc00

def z323 : W := mkw 0x3eba72b000000000 0x467d74e560000000 0x3e79f9f80000003d 0x447cf3f3f0000000

def z324 : W := mkw 0xd9d7472000000000 0x01b3ae8e40000000 0xf9ffc7f80000003f 0xc7f3ff8ff0000000

def z325 : W := mkw 0x36b800036dec0000 0x266d700006dbd800 0x3e180007fffe0048 0x3c7c30000ffffc00

def z326 : W := mkw 0xbffa68037fec7060 0x377ff4d006ffd8e0 0xfff87807fffe385f 0x3ffff0f00ffffc70

def z327 : W := mkw 0x64058006c8018000 0x02c80b000d900300 0xfe078007fe01c06f 0xb7fc0f000ffc0380

def z328 : W := mkw 0x0000000800020a00 0x0000000010000414 0x00184038000e3808 0x1000308070001c70

def z329 : W := mkw 0x0000880efa8bfae4 0x100001101df517f5 0x00000007ff8fffc0 0x380000000fff1fff

def z330 : W := mkw 0x0000804581518518 0x000001008b02a30a 0x0000000780700000 0x000000000f00e000

def z331 : W := mkw 0xf5d50503e9c88108 0x27ebaa0a07d39102 0xf9860603f180c182 0xa7f30c0c07e30183

def z332 : W := mkw 0x4005804480118410 0x00800b0089002308 0xc06781c78071c677 0xeb80cf038f00e38c

def z333 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc18787c38181c7a2 0xe3830f0f8703038f

def z334 : W := mkw 0x7ebf77b000000000 0x46fd7eef60000000 0x3e1ffff800000028 0xc47c3ffff0000000

def z335 : W := mkw 0xffff77bb7dee6a84 0x67fffeef76fbdcd5 0xffffffffffffffff 0xffffffffffffffff

def z336 : W := mkw 0x814000036dec0000 0x2102800006dbd800 0xc1e00007fffe0057 0x3b83c0000ffffc00

def z337 : W := mkw 0x91d0076921da0f9c 0x0123a00ed243b41f 0x01f807f801fe0790 0x4803f00ff003fc0f

def z338 : W := mkw 0x6c07e846da11f470 0x12d80fd08db423e8 0xfe67f9c7fe71fe7f 0xfffccff38ffce3fc

def z339 : W := mkw 0x2c02e8065a017060 0x125805d00cb402e0 0x3e01f8047e01386d 0x147c03f008fc0270

def z340 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180000001800053 0x2803000000030000

def z341 : W := mkw 0x109000036dec0000 0x2021200006dbd800 0x39980007fffe005b 0x3c7330000ffffc00

def z342 : W := mkw 0x8140000101400000 0x0102800002028000 0xc180000381800002 0x2383000007030000

def z343 : W := mkw 0x0228109000000000 0x0004502120000000 0x007801f800000010 0x4000f003f0000000

def z344 : W := mkw 0x3eba7ab806261a42 0x4e7d74f5700c4c34 0x3e1878380e0e3808 0x147c30f0701c1c70

def z345 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000181c7c0 0x280000000003038f

def z346 : W := mkw 0x6405a806da01f060 0x12c80b500db403e0 0xc601b807fe01f844 0x338c03700ffc03f0

def z347 : W := mkw 0x40058806da01f060 0x10800b100db403e0 0xc0078007fe01f867 0xb3800f000ffc03f0

def z348 : W := mkw 0xf7fd37b000000000 0x47effa6f60000000 0xc7f9bff800000014 0x438ff37ff0000000

def z349 : W := mkw 0xc145050181408108 0x01828a0a03028102 0xc1e787c38180c1b7 0xe383cf0f87030183

def z350 : W := mkw 0xffff77b2d800e020 0x57fffeef65b001c0 0xfffffffbf000c03f 0xe7fffffff7e00180

def z351 : W := mkw 0xb7f8189b6fee1a42 0x2f6ff03136dfdc34 0xfff8783ffffe385f 0x3ffff0f07ffffc70

def z352 : W := mkw 0x18924228208a0a84 0x0031248450411415 0x399e4638018e07bb 0xcc733c8c70031c0f

def z353 : W := mkw 0xffff77b181408108 0x47fffeef63028102 0xfffffffb8180c1bf 0xe7fffffff7030183

def z354 : W := mkw 0x24008806da01f060 0x124801100db403e0 0xfe000007fe01f84f 0x37fc00000ffc03f0

def z355 : W := mkw 0x1892ca2c328b7ac4 0x00312594586516f5 0x3f9ffe3c7f8fffff 0xfc7f3ffc78ff1fff

def z356 : W := mkw 0x0000880402011040 0x0000011008040220 0x000000040e013840 0x10000000081c0270

def z357 : W := mkw 0xbffa40037dec6000 0x277ff48006fbd8c0 0xfffe4007fffff87f 0xbffffc800ffffff0

def z358 : W := mkw 0xffffed47fffdf578 0x37ffffda8ffffbea 0xffffffc7ffffffff 0xffffffff8fffffff

def z359 : W := mkw 0x6c07e80eda03fa60 0x12d80fd01db407f4 0xfe1ff83ffe0ffe7f 0xfffc3ff07ffc1ffc

def z360 : W := mkw 0x0000080806261a42 0x08000010100c4c34 0x000000000e0e3800 0x10000000001c1c70

def z361 : W := mkw 0x0802400000000000 0x0010048000000000 0x380640000000002b 0x84700c8000000000

def z362 : W := mkw 0x022898dd87779f5a 0x08045131bb0eef3e 0x0679f9ff8ffffffd 0x780cf3f3ff1fffff

def z363 : W := mkw 0x6c0768025a007060 0x12d80ed004b400e0 0xfe07f8007e00382f 0x97fc0ff000fc0070

def z364 : W := mkw 0x6c07600000000000 0x02d80ec000000000 0xfe07f8000000002f 0x87fc0ff000000000

def z365 : W := mkw 0xfffff8dffffffe72 0x3ffffff1bffffffc 0xfffff9fffffffe7f 0xfffffff3fffffffc

def z366 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc06787c78071c7a4 0xc380cf0f8f00e38f

def z367 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x07fffffc0fffffff 0xf80ffffff81fffff

def z368 : W := mkw 0xb7f898d76ffd1452 0x2f6ff131aedffa28 0xfff9b9c7fffe005f 0x3ffff3738ffffc00

def z369 : W := mkw 0x0000000181408108 0x0000000003028102 0x000000038180c180 0x2000000007030183

def z370 : W := mkw 0x91d0000121c80000 0x0123a00002439000 0xf9f80007f1fe005f 0x3ff3f0000fe3fc00

def z371 : W := mkw 0x1abadafc36bf7ed6 0x083575b5f86d7efd 0x3e79f9fc7e7f3e7d 0x5c7cf3f3f8fcfe7c

def z372 : W := mkw 0xd3fd17b000000000 0x45a7fa2f60000000 0xc1ff87f800000037 0xc383ff0ff0000000

def z373 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x39984038718e385b 0x3c73308070e31c70

def z374 : W := mkw 0xfdd777b000000000 0x47fbaeef60000000 0xf987fff800000022 0xc7f30ffff0000000

def z375 : W := mkw 0xffffffff6fff1e52 0x6ffffffffedffe3c 0xffffffffffff3e7f 0xfffffffffffffe7c

def z376 : W := mkw 0x0228189806261a42 0x08045031300c4c34 0x0679f9f80e0e383d 0x500cf3f3f01c1c70

def z377 : W := mkw 0xb7f800026cac0000 0x276ff00004d95800 0xfff800007e0e001f 0x17fff00000fc1c00

def z378 : W := mkw 0x0000080002001040 0x0000001000040020 0x060078000e003808 0x100c00f0001c0070

def z379 : W := mkw 0x6e2f709000000000 0x02dc5ee120000000 0xfe7ff9f80000003f 0xc7fcfff3f0000000

def z380 : W := mkw 0xb5d0000000000000 0x076ba00000000000 0xf980000000000002 0x07f3000000000000

def z381 : W := mkw 0x6c07e84ede37fe72 0x1ad80fd09dbc6ffc 0xfe07f807fe7ffe6f 0xbffc0ff00ffcfffc

def z382 : W := mkw 0xfdd76728308a6a84 0x47fbaece506114d5 0xf99e4638718ffffb 0xfff33c8c70e31fff

def z383 : W := mkw 0xed47e807db41f060 0x13da8fd00fb683e0 0xffe7f807fff1f87f 0xbfffcff00fffe3f0

def z384 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e787c781f0c186 0xa383cf0f8f03e183

def z385 : W := mkw 0x1aba5ab836ae7ac6 0x083574b5706d5cf5 0x3f9e7e387f8ffffb 0xfc7f3cfc70ff1fff

def z386 : W := mkw 0xb7f8109000000000 0x076ff02120000000 0xfff9f9f80000003f 0x47fff3f3f0000000

def z387 : W := mkw 0xc947c5459151e518 0x01928f8a8b22a3ca 0xf9e7c7c7f1f1ffff 0xfff3cf8f8fe3e3ff

def z388 : W := mkw 0x0000000010006000 0x00000000002000c0 0x000000007001f840 0x3000000000e003f0

def z389 : W := mkw 0xfffffff7db51f578 0x57ffffffefb6a3ea 0xfffffffffff1ffff 0xffffffffffffe3ff

def z390 : W := mkw 0x10900228208a0a84 0x0021200450411415 0x019e0638018fc7f3 0xe8033c0c70031f8f

def z391 : W := mkw 0x7c97622af88aeaa4 0x12f92ec455f115d5 0xf99e463bf18ffffb 0xfff33c8c77e31fff

def z392 : W := mkw 0xc36d854585758518 0x0186db0a8b0aeb0a 0xc7ff87c78fffc7ff 0xfb8fff0f8f1fff8f

def z393 : W := mkw 0x0802422000000000 0x0010048440000000 0x0006463800000020 0xc0000c8c70000000

def z394 : W := mkw 0x08024008308a6a84 0x00100480106114d5 0x38064000718fffeb 0xbc700c8000e31fff

def z395 : W := mkw 0x6c07e847db51f578 0x12d80fd08fb6a3ea 0xfe07f807fff1ffef 0xbffc0ff00fffe3ff

def z396 : W := mkw 0x0000800400010000 0x0000010008000200 0x0001800400010065 0x0000030008000200

def z397 : W := mkw 0xffff77b369c80000 0x67fffeef66d39000 0xfffffffbf180003f 0xe7fffffff7e30000

def z398 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xff9e7e380000000a 0x87ff3cfc70000000

def z399 : W := mkw 0xfdd7672000000000 0x47fbaece40000000 0xff87fe000000002f 0x87ff0ffc00000000

def z400 : W := mkw 0x0000000369c80000 0x2000000006d39000 0x00000003f1800000 0x2000000007e30000

def z401 : W := mkw 0xffff77b810026a84 0x47fffeef702004d5 0xfffffff80001ffbf 0xc7fffffff00003ff

def z402 : W := mkw 0x000017b000000000 0x4000002f60000000 0x000007f800000000 0x4000000ff0000000

def z403 : W := mkw 0x6c07600248000000 0x02d80ec004900000 0xfe07f807fe00006f 0xb7fc0ff00ffc0000

def z404 : W := mkw 0x6405a806ca019060 0x12c80b500d940320 0xc601f8078e01386d 0x138c03f00f1c0270

def z405 : W := mkw 0x0228109000000000 0x0004502120000000 0x0661b9c000000004 0x000cc37380000000

def z406 : W := mkw 0x0000000101400000 0x0000000002028000 0x0000000781f00040 0x280000000f03e000

def z407 : W := mkw 0x1892422000000000 0x0031248440000000 0x3986060000000002 0x84730c0c00000000

def z408 : W := mkw 0x0228189806261a42 0x08045031300c4c34 0x0678783c0e7e385d 0x180cf0f0781cfc70

def z409 : W := mkw 0xbffa72b000000000 0x477ff4e560000000 0xfff878380000001f 0x07fff0f070000000

def z410 : W := mkw 0x4005880482019040 0x00800b1009040320 0xc607f8078e01f86f 0xb38c0ff00f1c03f0

def z411 : W := mkw 0xc145050000000000 0x01828a0a00000000 0xc06181c000000004 0x0380c30380000000

def z412 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xc7f800078ffe0014 0x0b8ff0000f1ffc00

def z413 : W := mkw 0x022810d804360e12 0x08045021b0086c1c 0x067801fc0e7e065d 0x580cf003f81cfc0c

def z414 : W := mkw 0xb7f898dc06371e52 0x0f6ff131b80c6e3c 0xfff9f9fc0e7f3e7f 0x5ffff3f3f81cfe7c

def z415 : W := mkw 0x0228884c06371e52 0x08045110980c6e3c 0x067800040e7f3e5d 0x180cf000081cfe7c

def z416 : W := mkw 0xd9d74728308a6a84 0x01b3ae8e506114d5 0xf9ffc7f8718fffff 0xfff3ff8ff0e31fff

def z417 : W := mkw 0x8140000101400000 0x0102800002028000 0xc060000780700004 0x0380c0000f00e000

def z418 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xffe00007fff00006 0x27ffc0000fffe000

def z419 : W := mkw 0x08024228308a6a84 0x00100484506114d5 0x00064638718fffe0 0xf8000c8c70e31fff

def z420 : W := mkw 0x3eba72b8308a6a84 0x467d74e5706114d5 0x3e187838700e3808 0x147c30f070e01c70

def z421 : W := mkw 0x2400000248000000 0x0248000004900000 0x3e0000007e000008 0x147c000000fc0000

def z422 : W := mkw 0x0000000000000000 0x0000000000000000 0x00180000000e0059 0x1800300000001c00

def z423 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff80181c7ff 0xeffffffff003038f

def z424 : W := mkw 0x1892422000000000 0x0031248440000000 0x3818403800000008 0x0470308070000000

def z425 : W := mkw 0xb7f88807ffedf060 0x376ff1100fffdbe0 0xfff80007fffff85f 0x3ffff0000ffffff0

def z426 : W := mkw 0x836898dd07771e52 0x0906d131ba0eee3c 0xc7f9f9ff8fff3e7f 0x7b8ff3f3ff1ffe7c

def z427 : W := mkw 0x4807e806da01f060 0x10900fd00db403e0 0x0007f807fe01f860 0xb0000ff00ffc03f0

def z428 : W := mkw 0x2c0268025a007060 0x125804d004b400e0 0xfe007807fe00384f 0x37fc00f00ffc0070

def z429 : W := mkw 0xed47ed06da01f060 0x13da8fda0db403e0 0xffe7ffc7fe01f87f 0xf7ffcfff8ffc03f0

def z430 : W := mkw 0xa76800034d640000 0x274ed000069ac800 0xc7e000078ff00057 0x2b8fc0000f1fe000

def z431 : W := mkw 0xffff77f804360e12 0x4ffffeeff0086c1c 0xfffffff8007e063f 0xcffffffff000fc0c

def z432 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x39860600718fffc2 0xbc730c0c00e31fff

def z433 : W := mkw 0xc1458d4d87779f5a 0x09828b1a9b0eef3e 0xc1e787c78ffffff7 0xfb83cf0f8f1fffff

def z434 : W := mkw 0xffff77b010006000 0x47fffeef602000c0 0xfffffff87001f87f 0xf7fffffff0e003f0

def z435 : W := mkw 0x1090000020880000 0x0021200000411000 0x38180000700e0008 0x1470300000e01c00

def z436 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0619f9f80e0f3e28 0x500c33f3f01c1e7c

def z437 : W := mkw 0x1aba52b8308a6a84 0x003574a5706114d5 0x3ffffff8718fffff 0xfc7ffffff0e31fff

def z438 : W := mkw 0xd1d5876da1db8f9c 0x01a3ab0edb43b71f 0xc1ff87ff81ffc7f7 0xeb83ff0fff03ff8f

def z439 : W := mkw 0x000000034d640000 0x20000000069ac800 0x000000078e700000 0x000000000f1ce000

def z440 : W := mkw 0x7c97ea2efa8bfae4 0x12f92fd45df517f5 0xfe1ff83ffe0ff86f 0xb7fc3ff07ffc1ff0

def z441 : W := mkw 0x4005854480118518 0x00800b0a8900230a 0xc00787c78001c7e7 0xe3800f0f8f00038f

def z442 : W := mkw 0x93f817b125ec0000 0x6527f02f624bd800 0x01f807f801fe0010 0x4803f00ff003fc00

def z443 : W := mkw 0x022810d004340412 0x08045021a0086808 0x006001c000700000 0x0000c0038000e000

def z444 : W := mkw 0xd3fd97f581518518 0x45a7fb2feb02a30a 0xc1ff87ff81f1c7f7 0xeb83ff0fff03e38f

def z445 : W := mkw 0xffff7fb25a007060 0x57fffeff64b400e0 0xfffffff87e00383f 0xd7fffffff0fc0070

def z446 : W := mkw 0xe76d359000000000 0x47ceda6b20000000 0xc679f9f80000003d 0x438cf3f3f0000000

def z447 : W := mkw 0x3eba68027eac7060 0x367d74d004fd58e0 0x3e1878007e0e3808 0x147c30f000fc1c70

def z448 : W := mkw 0x6c07e006d801e020 0x12d80fc00db003c0 0xf8078007f001c067 0xa7f00f000fe00380

def z449 : W := mkw 0x0000189802021a42 0x0800003130040434 0x0000783800003800 0x000000f070000070

def z450 : W := mkw 0x4005050080008108 0x00800a0a01000102 0x000606000000c180 0x80000c0c00000183

def z451 : W := mkw 0x0000000248000000 0x0000000004900000 0x00000007fe000040 0x300000000ffc0000

def z452 : W := mkw 0x6c07ffb6da01f060 0x52d80fff6db403e0 0xfe07fffffe01f86f 0xf7fc0ffffffc03f0

def z453 : W := mkw 0x0802c80412017040 0x00100590082402e0 0x3e07f8047e01f86f 0xb47c0ff008fc03f0

def z454 : W := mkw 0x1892422030886084 0x00312484406110c1 0x398646007181f9eb 0xb4730c8c00e303f3

def z455 : W := mkw 0x4807e8049201f060 0x10900fd0092403e0 0x0607f8040e01f86d 0x900c0ff0081c03f0

def z456 : W := mkw 0xc145050000000000 0x01828a0a00000000 0xc1e787c00181c7f7 0xeb83cf0f8003038f

def z457 : W := mkw 0x8140054101500518 0x0102800a8202a00a 0xc1e007c781f007d7 0x6b83c00f8f03e00f

def z458 : W := mkw 0x000010d800120e12 0x08000021b000241c 0x000001f800000600 0x40000003f000000c

def z459 : W := mkw 0x1892ca2efa8bfae4 0x103125945df517f5 0x399e463fff8ffffb 0xfc733c8c7fff1fff

def z460 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x38184038718fffc8 0x3c70308070e31fff

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x006181c000000035 0x4000c30380000000

def z462 : W := mkw 0xc145854400110410 0x01828b0a88002208 0xc1e787c400710677 0xcb83cf0f8800e20c

def z463 : W := mkw 0x0000804581518518 0x000001008b02a30a 0x0186060781f1c7f3 0xe8030c0c0f03e38f

def z464 : W := mkw 0xed476503d940e128 0x13da8eca07b281c2 0xf9860603f180c182 0xa7f30c0c07e30183

def z465 : W := mkw 0xffff77b800020a00 0x47fffeef70000414 0xfffffff8000f3e7f 0xdffffffff0001e7c

def z466 : W := mkw 0x0000884406351452 0x08000110880c6a28 0x000000040e700000 0x00000000081ce000

def z467 : W := mkw 0x2c02400258006000 0x0258048004b000c0 0xfe064007fe01f86f 0xb7fc0c800ffc03f0

def z468 : W := mkw 0x022898d406351452 0x08045131a80c6a28 0x0679b9c40e7e005d 0x180cf373881cfc00

def z469 : W := mkw 0x6c076002d800e020 0x12d80ec005b001c0 0xfe060007fe00c04f 0xb7fc0c000ffc0180

def z470 : W := mkw 0x9bfa422935ee6a84 0x2537f484526bdcd5 0x39fe463871fffffb 0xfc73fc8c70e3ffff

def z471 : W := mkw 0xfdd7672369c80000 0x67fbaece46d39000 0xf9860603f1800002 0xa7f30c0c07e30000

def z472 : W := mkw 0x1090022020880084 0x0021200440411001 0x0180060001800180 0x0003000c00030003

def z473 : W := mkw 0x00000002d800e020 0x1000000005b001c0 0x00000003f000c000 0x2000000007e00180

def z474 : W := mkw 0xfffff7f581518518 0x47ffffefeb02a30a 0xffffffff8070003f 0xc7ffffffff00e000

def z475 : W := mkw 0xc145800581418000 0x01828b000b028300 0xc1e7800781f1c077 0xab83cf000f03e380

def z476 : W := mkw 0xffff77b8208a0a84 0x47fffeef70411415 0xfffffff8018e07bf 0xcffffffff0031c0f

def z477 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe01f807fe00380c 0x17fc03f00ffc0070

def z478 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x381e4638700fffa8 0xd4703c8c70e01fff

def z479 : W := mkw 0xb7f8000101400000 0x076ff00002028000 0xfff8000781f0005f 0x2ffff0000f03e000

def z480 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e187c781f00794 0x4b83c30f8f03e00f

def z481 : W := mkw 0x3c92422a788a6a84 0x0279248454f114d5 0xff9e463fff8fffff 0xffff3c8c7fff1fff

def z482 : W := mkw 0x022898dc02131e52 0x08045131b804263c 0x0679f9f800013e3d 0x400cf3f3f000027c

def z483 : W := mkw 0x6c07e8049201f060 0x12d80fd0092403e0 0xfe07f8000001f82f 0x87fc0ff0000003f0

def z484 : W := mkw 0xffff6003fdece020 0x37fffec007fbd9c0 0xfffe0007fffec05f 0xbffffc000ffffd80

def z485 : W := mkw 0x0000884f6fff1e52 0x280001109edffe3c 0x00000007ffff3e40 0x380000000ffffe7c

def z486 : W := mkw 0xc1459ddd83539f5a 0x09828b3bbb06a73e 0xc1e7ffff81f1fff7 0xeb83cfffff03e3ff

def z487 : W := mkw 0x7c97e806fa89f060 0x12f92fd00df513e0 0xff9ff807ff8ff87f 0xbfff3ff00fff1ff0

def z488 : W := mkw 0xf7fd9ddfefff9f5a 0x2feffb3bbfdfff3e 0xffffffffffffffff 0xffffffffffffffff

def z489 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xf9fe07f800000012 0xc7f3fc0ff0000000

def z490 : W := mkw 0x10900008208a0a00 0x0021200010411414 0x39984038718f3e7b 0x7c73308070e31e7c

def z491 : W := mkw 0x00000008208a0a84 0x0000000010411415 0x00000000018e0780 0x0800000000031c0f

def z492 : W := mkw 0x4807ed449211f578 0x10900fda892423ea 0x0007ffc00001ffa0 0xc0000fff800003ff

def z493 : W := mkw 0x4005800480018000 0x00800b0009000300 0xc001800780000004 0x038003000f000000

def z494 : W := mkw 0x3490000268880000 0x0269200004d11000 0xff980007ff8e005f 0x3fff30000fff1c00

def z495 : W := mkw 0x8140050000000000 0x0102800a00000000 0x01e007c000000010 0x4003c00f80000000

def z496 : W := mkw 0x022810d804360e12 0x08045021b0086c1c 0x007841f8007f3e79 0x5800f083f000fe7c

def z497 : W := mkw 0xffff77b020880000 0x47fffeef60411000 0xfffffff8718e007f 0xfffffffff0e31c00

def z498 : W := mkw 0xe76d8547cd758518 0x27cedb0a8f9aeb0a 0xc66181c78e700004 0x038cc3038f1ce000

def z499 : W := mkw 0xfffff7f480118518 0x47ffffefe900230a 0xfffffff80001c7bf 0xc7fffffff000038f

def z500 : W := mkw 0x00008806da01f060 0x100001100db403e0 0x0601f807fe01f86d 0x300c03f00ffc03f0

def z501 : W := mkw 0x4005800480018000 0x00800b0009000300 0xc18786078181c7f7 0xeb830f0c0f03038f

def z502 : W := mkw 0xa76800036dec0000 0x274ed00006dbd800 0xc6600007fffe0044 0x3b8cc0000ffffc00

def z503 : W := mkw 0xc145054101500518 0x01828a0a8202a00a 0xc1e787c001f007b7 0xcb83cf0f8003e00f

def z504 : W := mkw 0x022898df6fff1e52 0x28045131bedffe3c 0x0679f9ffffff3e7d 0x780cf3f3fffffe7c

def z505 : W := mkw 0x00000008308a6a84 0x00000000106114d5 0x01860600718ffff3 0xf8030c0c00e31fff

def z506 : W := mkw 0x000098d402111452 0x08000131a8042228 0x0001b9c000000000 0x0000037380000000

def z507 : W := mkw 0xbdd2422b79ca6a84 0x277ba48456f394d5 0xf99e463bf18ffffb 0xfff33c8c77e31fff

def z508 : W := mkw 0xc145050000000000 0x01828a0a00000000 0xc186060000000002 0x83830c0c00000000

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x060000040e00004d 0x100c0000081c0000

def z510 : W := mkw 0x8368000105640000 0x0106d000020ac800 0xc7f800078ffe005f 0x3b8ff0000f1ffc00

def z511 : W := mkw 0x0000884d87779f5a 0x080001109b0eef3e 0x000000078fffffc0 0x380000000f1fffff

def z512 : W := mkw 0x6c0777b000000000 0x42d80eef60000000 0xfe07fff80000002f 0xc7fc0ffff0000000

def z513 : W := mkw 0x6c07e00480018000 0x02d80fc009000300 0xfe07f8078001c06f 0xa7fc0ff00f000380

def z514 : W := mkw 0x1892422000000000 0x0031248440000000 0x399e46380181c7fb 0xec733c8c7003038f

def z515 : W := mkw 0xb7f8022b6dee0a84 0x276ff00456dbdc15 0xfff8063ffffe07df 0x7ffff00c7ffffc0f

def z516 : W := mkw 0xf7fda807efed9060 0x37effb500fdfdb20 0xfff9b807fffe005f 0x3ffff3700ffffc00

def z517 : W := mkw 0x0000022800020a84 0x0000000450000415 0x0000063800000780 0x4000000c7000000f

def z518 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x0018403c0e7f3e79 0x58003080781cfe7c

def z519 : W := mkw 0xc1458547edfd8518 0x21828b0a8fdbfb0a 0xc1e787c7ffffc7f7 0xfb83cf0f8fffff8f

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x000600000001c063 0xa0000c0000000380

def z521 : W := mkw 0x93f8000000000000 0x0527f00000000000 0x01f8000000000010 0x0003f00000000000

def z522 : W := mkw 0x0228109804260a02 0x0804502130084c14 0x00180038000e0000 0x0000300070001c00

def z523 : W := mkw 0x36b8189a6eae1a42 0x2e6d703134dd5c34 0x3e1878387e0e3808 0x147c30f070fc1c70

def z524 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679b9fc0e7e0614 0x480cf373f81cfc0c

def z525 : W := mkw 0x0a2adafc16377ed6 0x081455b5f82c6efd 0x067ffffc0e7ffffd 0xd80cfffff81cffff

def z526 : W := mkw 0xc36d9ddc06371e52 0x0986db3bb80c6e3c 0xc7fffffc0e7f3e7f 0xdb8ffffff81cfe7c

def z527 : W := mkw 0x10900228208a0a84 0x0021200450411415 0x39980638718e07db 0x7c73300c70e31c0f

def z528 : W := mkw 0x12b812b000000000 0x4425702560000000 0x0018003800000000 0x0000300070000000

def z529 : W := mkw 0x422d9ddc86379f5a 0x08845b3bb90c6f3e 0x067ffffc0e7ffffd 0xd80cfffff81cffff

def z530 : W := mkw 0x00000008308a6a84 0x00000000106114d5 0x00000000700e3800 0x1000000000e01c70

def z531 : W := mkw 0x1892400030886000 0x00312480006110c0 0x399e4000718ff87b 0xbc733c8000e31ff0

def z532 : W := mkw 0xe76db5d581518518 0x47cedb6bab02a30a 0xc661b9c780700004 0x038cc3738f00e000

def z533 : W := mkw 0x0802dafc12137ed6 0x081005b5f82426fd 0x0007fff80001ffa0 0xc0000ffff00003ff

def z534 : W := mkw 0xc947ed459351f578 0x11928fda8b26a3ea 0xc1e7ffc781f1fff7 0xeb83cfff8f03e3ff

def z535 : W := mkw 0xc36d9ddd87779f5a 0x0986db3bbb0eef3e 0xc679f9ff8e7f3e7d 0x5b8cf3f3ff1cfe7c

def z536 : W := mkw 0xf7fd050000000000 0x07effa0a00000000 0xffff87c00000003f 0xc7ffff0f80000000

def z537 : W := mkw 0x4807ffb49201f060 0x50900fff692403e0 0x0007fff80001f820 0xc0000ffff00003f0

def z538 : W := mkw 0xfffff7f400110410 0x47ffffefe8002208 0xfffffffc0071067f 0xcffffffff800e20c

def z539 : W := mkw 0x93f8022925ee0a84 0x2527f004524bdc15 0x01f8063801fe0790 0x4803f00c7003fc0f

def z540 : W := mkw 0xb7f817b000000000 0x476ff02f60000000 0xfff807f80000001f 0x47fff00ff0000000

def z541 : W := mkw 0xe76d35934d640000 0x67ceda6b269ac800 0xc661b9c78e700004 0x038cc3738f1ce000

def z542 : W := mkw 0x91d0072000000000 0x4523a00e40000000 0x0180060000000000 0x0003000c00000000

def z543 : W := mkw 0x0802422810026a84 0x00100484502004d5 0x001e4638000ffff9 0xd8003c8c70001fff

def z544 : W := mkw 0x1090000020880000 0x0021200000411000 0x01980000018e0010 0x0803300000031c00

def z545 : W := mkw 0x2400000248000000 0x0248000004900000 0xc60000078e000004 0x038c00000f1c0000

def z546 : W := mkw 0xc947f7f581518518 0x41928fefeb02a30a 0xc1e7ffff81f1c7f7 0xeb83cfffff03e38f

def z547 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x399e4638718ef98a 0xb4733c8c70e31df3

def z548 : W := mkw 0xb7f8000004240000 0x076ff00000084800 0xfff800040e7e005f 0x1ffff000081cfc00

def z549 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x399e4638700e383b 0xd4733c8c70e01c70

def z550 : W := mkw 0x8368159000000000 0x4506d02b20000000 0x006001c000000000 0x0000c00380000000

def z551 : W := mkw 0xffff60036dec0000 0x27fffec006dbd800 0xfffff807fffe007f 0xbffffff00ffffc00

def z552 : W := mkw 0xa76898d74f751452 0x2f4ed131ae9eea28 0xc661b9c78e700004 0x038cc3738f1ce000

def z553 : W := mkw 0xb7f880476dfd0410 0x276ff1008edbfa08 0xfff981c7ffff067f 0x7ffff3038ffffe0c

def z554 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e181c781f00057 0x2b83c3038f03e000

def z555 : W := mkw 0x022898dede37fe72 0x18045131bdbc6ffc 0x0679f9fffe7ffe7d 0x780cf3f3fffcfffc

def z556 : W := mkw 0x36b800026cac0000 0x266d700004d95800 0xfe180007fe0e004f 0x37fc30000ffc1c00

def z557 : W := mkw 0x0228000004240000 0x0004500000084800 0x066000040e700004 0x000cc000081ce000

def z558 : W := mkw 0x0228989c06271a42 0x08045131380c4e34 0x0619f83c0e0f386d 0x100c33f0781c1e70

def z559 : W := mkw 0xd9d7c765b1d9e59c 0x01b3af8ecb63b3cb 0xf9e787c7f1f1c7f7 0xeff3cf0f8fe3e38f

def z560 : W := mkw 0x0000004000100410 0x0000000080002008 0x006001c000700610 0x4800c0038000e00c

def z561 : W := mkw 0x12b8000024ac0000 0x0025700000495800 0x3ff800047ffe005f 0x3c7ff00008fffc00

def z562 : W := mkw 0xfdd7e807fbc9f060 0x37fbafd00ff793e0 0xff87f807ff81f86f 0xb7ff0ff00fff03f0

def z563 : W := mkw 0x000098dc02131e52 0x08000131b804263c 0x0019f9f8000f3e79 0x580033f3f0001e7c

def z564 : W := mkw 0x022810d804360e12 0x08045021b0086c1c 0x0679f9f8007e063d 0x480cf3f3f000fc0c

def z565 : W := mkw 0x40059ddc82139f5a 0x08800b3bb904273e 0x0007fff80001ffa0 0xc0000ffff00003ff

def z566 : W := mkw 0x4807e8049201f060 0x10900fd0092403e0 0x3807f8007001f86b 0xb4700ff000e003f0

def z567 : W := mkw 0xa540000349400000 0x034a800006928000 0xffe00007fff0005f 0x3fffc0000fffe000

def z568 : W := mkw 0x1892422030886084 0x00312484406110c1 0x399e0600718ec1db 0xbc733c0c00e31d83

def z569 : W := mkw 0x0228989402011040 0x0004513128040220 0x0679f9fc0e01387d 0x500cf3f3f81c0270

def z570 : W := mkw 0xfffffffd87779f5a 0x4ffffffffb0eef3e 0xffffffff8fffffff 0xffffffffff1fffff

def z571 : W := mkw 0x0228189006241042 0x08045031200c4820 0x060038000e000000 0x000c0070001c0000

def z572 : W := mkw 0xbffa422000000000 0x077ff48440000000 0xfffe46380000003f 0xc7fffc8c70000000

def z573 : W := mkw 0xc94777b000000000 0x41928eef60000000 0xc1e7fff800000037 0xc383cffff0000000

def z574 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x019e4638018fffb0 0xc8033c8c70031fff

def z575 : W := mkw 0x000008025a007060 0x1000001004b400e0 0x000000007e003800 0x1000000000fc0070

def z576 : W := mkw 0xb7f8000248000000 0x076ff00004900000 0xfff80007fe00005f 0x37fff0000ffc0000

def z577 : W := mkw 0xfffffffc36bf7ed6 0x4ffffffff86d7efd 0xfffffffc7fffffff 0xfffffffff8ffffff

def z578 : W := mkw 0xc947c76d9153ef9c 0x01928f8edb22a7df 0xc1e7c7ff81f1fff7 0xeb83cf8fff03e3ff

def z579 : W := mkw 0x5897ea2cb28bfae4 0x10b12fd4596517f5 0x399ffe38718ffffb 0xfc733ffc70e31fff

def z580 : W := mkw 0xc145050181408108 0x01828a0a03028102 0xc000000380000000 0x0380000007000000

def z581 : W := mkw 0xb5d0000369c80000 0x276ba00006d39000 0xff800007ff80004f 0x37ff00000fff0000

def z582 : W := mkw 0x3c92622000000000 0x467924c440000000 0x3800000000000000 0x0470000000000000

def z583 : W := mkw 0x0802400010006000 0x00100480002000c0 0x000640000001f820 0x80000c80000003f0

def z584 : W := mkw 0xe545ad47cb519578 0x13ca8b5a8f96a32a 0xc7e7bfc78ff1c7f7 0xeb8fcf7f8f1fe38f

def z585 : W := mkw 0x6c07600010006000 0x02d80ec0002000c0 0xfe07f8007001f86f 0xb7fc0ff000e003f0

def z586 : W := mkw 0x8140804501510410 0x010281008a02a208 0xc1e181c781f10677 0x6b83c3038f03e20c

def z587 : W := mkw 0x6e2ff896da01f060 0x12dc5ff12db403e0 0xfe7ff9fffe01f87f 0xf7fcfff3fffc03f0

def z588 : W := mkw 0x0802422810026a84 0x00100484502004d5 0x0000403800003800 0x0000008070000070

def z589 : W := mkw 0xb7f8000b7dee6a84 0x276ff00016fbdcd5 0xfff80007ffffffdf 0x3ffff0000fffffff

def z590 : W := mkw 0xc145854db1dbef9c 0x01828b0a9b63b7df 0xc1e787c7f1fffff7 0xfb83cf0f8fe3ffff

def z591 : W := mkw 0x00008807ffedf060 0x300001100fffdbe0 0x00000007fffff840 0x380000000ffffff0

def z592 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xff980003ff8e000a 0x37ff300007ff1c00

def z593 : W := mkw 0x0000000125ec0000 0x20000000024bd800 0x0000000001fe0000 0x080000000003fc00

def z594 : W := mkw 0x3eba72b8308a6a84 0x467d74e5706114d5 0x3f9e7e38718ffffb 0xfc7f3cfc70e31fff

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000400000013869 0x1000008000000270

def z596 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc06781c78071c067 0xa380cf038f00e380

def z597 : W := mkw 0xbdd2422379c86084 0x277ba48446f390c1 0xf9860603f180c182 0xa7f30c0c07e30183

def z598 : W := mkw 0xffff672000000000 0x47fffece40000000 0xfffe06000000001f 0x87fffc0c00000000

def z599 : W := mkw 0x0000800480018000 0x0000010009000300 0x000000078001c040 0x200000000f000380

def z600 : W := mkw 0xe76dbd96ca019060 0x57cedb7b2d940320 0xc661b9c78e000004 0x038cc3738f1c0000

def z601 : W := mkw 0xf7fd854581518518 0x07effb0a8b02a30a 0xffff87c781f1c7ff 0xefffff0f8f03e38f

def z602 : W := mkw 0xf7fd0503edec8108 0x27effa0a07dbd902 0xfffe0607fffec1df 0xbffffc0c0ffffd83

def z603 : W := mkw 0x6405a806ca019060 0x12c80b500d940320 0xc607b8078e01c067 0xa38c0f700f1c0380

def z604 : W := mkw 0x6c07e80efa8bfae4 0x12d80fd01df517f5 0xfe07f807ff8fffef 0xbffc0ff00fff1fff

def z605 : W := mkw 0xe76dbddc06371e52 0x4fcedb7bb80c6e3c 0xc679f9fc0e7f3e7d 0x5b8cf3f3f81cfe7c

def z606 : W := mkw 0x0000000020880000 0x0000000000411000 0x00000000718e0040 0x3800000000e31c00

def z607 : W := mkw 0x5897c76cb09bef9c 0x00b12f8ed96137df 0x399fc7f8718ffffb 0xfc733f8ff0e31fff

def z608 : W := mkw 0xc36d9dd58775955a 0x0986db3bab0eeb2a 0xc7e7bfc78ff1c7f7 0xeb8fcf7f8f1fe38f

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0x380000007000004b 0x3470000000e00000

def z610 : W := mkw 0xef6ffddfdf77ff7a 0x1bdedffbbfbeeffe 0xffffffffffffffff 0xffffffffffffffff

def z611 : W := mkw 0x6c07600000000000 0x02d80ec000000000 0xf806000000000002 0x87f00c0000000000

def z612 : W := mkw 0x93f898dd27ff1e52 0x2d27f131ba4ffe3c 0x07f9f9fc0fff3e7d 0x580ff3f3f81ffe7c

def z613 : W := mkw 0x0000804400110410 0x0000010088002208 0x01e787c401f1c7f7 0xe803cf0f8803e38f

def z614 : W := mkw 0x3eba422a7cae6a84 0x267d748454f95cd5 0x3e1840387e0e3808 0x147c308070fc1c70

def z615 : W := mkw 0xf7fd359000000000 0x47effa6b20000000 0xfff9b9c00000001f 0x07fff37380000000

def z616 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x007801fc0e7f3e50 0x5800f003f81cfe7c

def z617 : W := mkw 0x2e2a789a5e267a62 0x1a5c54f134bc4cf4 0x3e1878387e0e3808 0x147c30f070fc1c70

def z618 : W := mkw 0x0000880402011040 0x0000011008040220 0x0601b8040e000004 0x000c0370081c0000

def z619 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0618783c0e7f3e48 0x180c30f0781cfe7c

def z620 : W := mkw 0xb5d0000369c80000 0x276ba00006d39000 0xf9980003f18e005b 0x3ff3300007e31c00

def z621 : W := mkw 0x3c926a2a7a8a7ae4 0x127924d454f514f5 0x3e1878387e0e3808 0x147c30f070fc1c70

def z622 : W := mkw 0xbffa77b000000000 0x477ff4ef60000000 0x3ff87ff800000018 0x447ff0fff0000000

def z623 : W := mkw 0x8140000101400000 0x0102800002028000 0xc1e6060781f1c7f7 0xeb83cc0c0f03e38f

def z624 : W := mkw 0x480777b810026a84 0x40900eef702004d5 0x0007fff80001ffa0 0xc0000ffff00003ff

def z625 : W := mkw 0x0a2ad8dc16377e52 0x081455b1b82c6efc 0x3e7ff9fc7e7ffe7f 0xfc7cfff3f8fcfffc

def z626 : W := mkw 0x93f89ffc06371e52 0x4d27f13ff80c6e3c 0x07f9fffc0e7f3e7d 0x580ff3fff81cfe7c

def z627 : W := mkw 0x0228000004240000 0x0004500000084800 0x00780000007e0010 0x0800f0000000fc00

def z628 : W := mkw 0x022898d406351452 0x08045131a80c6a28 0x0661f9c40e71386d 0x100cc3f3881ce270

def z629 : W := mkw 0x7ebf72b000000000 0x46fd7ee560000000 0xfe1ff8380000002f 0x87fc3ff070000000

def z630 : W := mkw 0xffff7fb806261a42 0x4ffffeff700c4c34 0xfffffff80e0e383f 0xd7fffffff01c1c70

def z631 : W := mkw 0x4807ea2c9203fae4 0x10900fd4592407f5 0x0007fe380001ffa0 0xc0000ffc700003ff

def z632 : W := mkw 0x7ebffab6da01f060 0x56fd7ff56db403e0 0xfe1ff83ffe01f86f 0xb7fc3ff07ffc03f0

def z633 : W := mkw 0xbffadaff7fff7ed6 0x2f7ff5b5fefffefd 0xffffffffffffffff 0xffffffffffffffff

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180060001800790 0x4803000c0003000f

def z635 : W := mkw 0x0228189806261a42 0x08045031300c4c34 0x061878380e0f3e79 0x580c30f0701c1e7c

def z636 : W := mkw 0xed47650000000000 0x03da8eca00000000 0xffe7ffc00000003f 0xc7ffcfff80000000

def z637 : W := mkw 0x00008806ca019060 0x100001100d940320 0x000000078e000000 0x000000000f1c0000

def z638 : W := mkw 0xbffa422b7dee6a84 0x277ff48456fbdcd5 0xfff8403ffffe385f 0x3ffff0807ffffc70

def z639 : W := mkw 0x83689ddd07771f5a 0x0906d13bba0eee3e 0x07f9fffc0fff3ffd 0x580ff3fff81ffe7f

def z640 : W := mkw 0x0000804400110410 0x0000010088002208 0x006181c400700004 0x0000c3038800e000

def z641 : W := mkw 0x000000026cac0000 0x2000000004d95800 0x000000007e0e0000 0x1000000000fc1c00

def z642 : W := mkw 0x0802400810026a00 0x00100480102004d4 0x381e4038700ffe7b 0xfc703c8070e01ffc

def z643 : W := mkw 0xfdd7672000000000 0x47fbaece40000000 0xf9e787c000000037 0xc7f3cf0f80000000

def z644 : W := mkw 0xfdd76003f9c8e020 0x37fbaec007f391c0 0xf9860003f180c002 0xa7f30c0007e30180

def z645 : W := mkw 0x0000000800020a00 0x0000000010000414 0x00180038000e0610 0x4800300070001c0c

def z646 : W := mkw 0x000098dc02131e52 0x08000131b804263c 0x0601f9fc0e013e6d 0x500c03f3f81c027c

def z647 : W := mkw 0x4005a80482019060 0x10800b5009040320 0x0001b80000000000 0x0000037000000000

def z648 : W := mkw 0x2400000248000000 0x0248000004900000 0xf8000003f0000002 0x27f0000007e00000

def z649 : W := mkw 0x1892ca6c36bf7ed6 0x08312594d86d7efd 0x399e463c7ffffffb 0xfc733c8c78ffffff

def z650 : W := mkw 0x4807c76c9013ef9c 0x00900f8ed92027df 0x0007c7f80001ffa0 0xc0000f8ff00003ff

def z651 : W := mkw 0x3ebafafc06371e52 0x4e7d75f5f80c6e3c 0x3e79f9fc0e7f3e7d 0x5c7cf3f3f81cfe7c

def z652 : W := mkw 0x2628309000000000 0x464c506120000000 0x0600380000000000 0x000c007000000000

def z653 : W := mkw 0x0228880406251040 0x00045110080c4a20 0x0679f8040e7f387d 0x180cf3f0081cfe70

def z654 : W := mkw 0x00008847db51f578 0x100001108fb6a3ea 0x00000007fff1ffc0 0x380000000fffe3ff

def z655 : W := mkw 0x8140854581518518 0x0102810a8b02a30a 0x01e007c781f1c7d0 0x6803c00f8f03e38f

def z656 : W := mkw 0x9bfa57b8308a6a84 0x4537f4af706114d5 0x39fe47f8718ffffb 0xfc73fc8ff0e31fff

def z657 : W := mkw 0x0000004101500518 0x000000008202a00a 0x0000000001f00780 0x080000000003e00f

def z658 : W := mkw 0xa540000349400000 0x274a800006928000 0xc000000380000000 0x0380000007000000

def z659 : W := mkw 0x8140000101400000 0x0102800002028000 0x01e0000001f00010 0x0803c0000003e000

def z660 : W := mkw 0x0228804404350410 0x0004510088086a08 0x067981c40e7f067d 0x580cf303881cfe0c

def z661 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe07b807fe00c006 0xa7fc0f700ffc0180

def z662 : W := mkw 0x0000000030886084 0x00000000006110c1 0x000000007180c180 0x2000000000e30183

def z663 : W := mkw 0xffffffb49201f060 0x57ffffff692403e0 0xfffffff80001f83f 0xc7fffffff00003f0

def z664 : W := mkw 0x4005854480118518 0x00800b0a8900230a 0x000181c000000000 0x0000030380000000

def z665 : W := mkw 0x12b8000024ac0000 0x2425700000495800 0x00180000000e0000 0x0000300000001c00

def z666 : W := mkw 0x0802422810026a84 0x00100484502004d5 0x018646380181fff3 0xe8030c8c700303ff

def z667 : W := mkw 0x6e2ff8d6de35f472 0x1adc5ff1adbc6be8 0xfe67f9c7fe71f86f 0xb7fccff38ffce3f0

def z668 : W := mkw 0x0000880c02031a40 0x0000011018040634 0x0619f83c0e0f3e7d 0x580c33f0781c1e7c

def z669 : W := mkw 0x4005800480018000 0x00800b0009000300 0x000780000001c020 0x80000f0000000380

def z670 : W := mkw 0x1abadafc06371e52 0x083575b5f80c6e3c 0x3ffffffc0e7f3e7f 0xdc7ffffff81cfe7c

def z671 : W := mkw 0xc145850480018000 0x01828b0a09000300 0xc1e787c78001c077 0xe383cf0f8f000380

def z672 : W := mkw 0x1090000020880000 0x0021200000411000 0x399e0600718fc7fb 0xfc733c0c00e31f8f

def z673 : W := mkw 0x6c076002d800e020 0x12d80ec005b001c0 0xf8064003f001f86b 0xb7f00c8007e003f0

def z674 : W := mkw 0x91d0000121c80000 0x2523a00002439000 0x0180000001800000 0x0003000000030000

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x0060000400700055 0x0800c0000800e000

def z676 : W := mkw 0xc145854480118518 0x01828b0a8900230a 0xc1e787c00001c7b7 0xc383cf0f8000038f

def z677 : W := mkw 0x93f817f101500518 0x4527f02fe202a00a 0x01f807f801f00790 0x4803f00ff003e00f

def z678 : W := mkw 0x4807e8049201f060 0x10900fd0092403e0 0xc007f8078001f867 0xa3800ff00f0003f0

def z679 : W := mkw 0xf7fd8007eded8000 0x27effb000fdbdb00 0xffff8007ffffc07f 0xbfffff000fffff80

def z680 : W := mkw 0xb7f8000b6dee0a00 0x276ff00016dbdc14 0xfff8403fffff3e7f 0x7ffff0807ffffe7c

def z681 : W := mkw 0x022898dc36bf7ed6 0x08045131b86d7efd 0x0679f9fc7ffffffd 0x780cf3f3f8ffffff

def z682 : W := mkw 0x99d2422931ca6a84 0x0133a484526394d5 0xf9fe463ff1ffffff 0xfff3fc8c7fe3ffff

def z683 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc06181c780710675 0x4b80c3038f00e20c

def z684 : W := mkw 0x93f8000125ec0000 0x2527f000024bd800 0x07f800040ffe005d 0x180ff000081ffc00

def z685 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0661f9fc0e713e24 0x400cc3f3f81ce27c

def z686 : W := mkw 0xb7f8000020880000 0x076ff00000411000 0xfff80000718e005f 0x3ffff00000e31c00

def z687 : W := mkw 0xffffc76ffdffef9c 0x27ffff8edffbffdf 0xffffc7ffffffffff 0xffffff8fffffffff

def z688 : W := mkw 0x7c976228308a6a84 0x02f92ec4506114d5 0xff9ffe38718fffff 0xffff3ffc70e31fff

def z689 : W := mkw 0x1892422030886084 0x00312484406110c1 0x3800000070000000 0x0470000000e00000

def z690 : W := mkw 0x0000804c00130e10 0x000001009800261c 0x0079c1fc007f3e7d 0x5800f383f800fe7c

def z691 : W := mkw 0x2c02600258006020 0x125804c004b000c0 0x3800000070000000 0x0470000000e00000

def z692 : W := mkw 0x6e2ff89ede27fa62 0x1adc5ff13dbc4ff4 0xfe1ff83ffe0ff86f 0xb7fc3ff07ffc1ff0

def z693 : W := mkw 0x9bfa57b000000000 0x4537f4af60000000 0x39fe47f80000003b 0xc473fc8ff0000000

def z694 : W := mkw 0xed47e54581518518 0x03da8fca8b02a30a 0xffe7ffc781f1c7ff 0xefffcfff8f03e38f

def z695 : W := mkw 0x6c07ea2eda03fae4 0x12d80fd45db407f5 0xfe07fe3ffe01ffef 0xf7fc0ffc7ffc03ff

def z696 : W := mkw 0x0802c806da01f060 0x101005900db403e0 0x38064007fe01f86b 0xb4700c800ffc03f0

def z697 : W := mkw 0xc1458d47db51f578 0x11828b1a8fb6a3ea 0xc1e787c7fff1fff7 0xfb83cf0f8fffe3ff

def z698 : W := mkw 0xfffffff406351452 0x4fffffffe80c6a28 0xfffffffc0e70003f 0xc7fffffff81ce000

def z699 : W := mkw 0x8140050101400108 0x0102800a02028002 0x0180060001800180 0x0003000c00030003

def z700 : W := mkw 0xfdd7e76581518518 0x47fbafcecb02a30a 0xf9e787c781f1c7f7 0xeff3cf0f8f03e38f

def z701 : W := mkw 0x0802680012007060 0x101004d0002400e0 0x0000780000003800 0x000000f000000070

def z702 : W := mkw 0x0000804400110410 0x0000010088002208 0x000181c000010620 0x400003038000020c

def z703 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x39984638718e3f98 0x5c73308c70e31c7f

def z704 : W := mkw 0xb7f810db6dfe0e12 0x2f6ff021b6dbfc1c 0xfff801fffffe065f 0x7ffff003fffffc0c

def z705 : W := mkw 0x0802400010006000 0x00100480002000c0 0x3800400070003808 0x1470008000e00070

def z706 : W := mkw 0xe76d8547cd758518 0x27cedb0a8f9aeb0a 0xc7e787c78ff1c7f7 0xeb8fcf0f8f1fe38f

def z707 : W := mkw 0xfdd777b000000000 0x47fbaeef60000000 0xff87fff80000002f 0xc7ff0ffff0000000

def z708 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff80001c7bf 0xc7fffffff000038f

def z709 : W := mkw 0xe76d3598308a6a84 0x47ceda6b306114d5 0xc661b9c0718fffc4 0x3b8cc37380e31fff

def z710 : W := mkw 0x6c07600258006000 0x02d80ec004b000c0 0xfe07f807fe01f86f 0xb7fc0ff00ffc03f0

def z711 : W := mkw 0x480777b36dec0000 0x60900eef66dbd800 0x0007fffffffe0060 0xf8000ffffffffc00

def z712 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x3f9e463c7f8fffff 0xfc7f3c8c78ff1fff

def z713 : W := mkw 0xc36d159000000000 0x0186da2b20000000 0xc679f9f80000003d 0x438cf3f3f0000000

def z714 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff80000000e 0x87fffffff0000000

def z715 : W := mkw 0x1abadaf436bd74d6 0x083575b5e86d7ae9 0x3fe7bfc47ff0c186 0xa47fcf7f88ffe183

def z716 : W := mkw 0xb5d098df6bdb1e52 0x2f6ba131bed7b63c 0xf981f9fbf1813e22 0x67f303f3f7e3027c

def z717 : W := mkw 0x12b812b000000000 0x0025702560000000 0x07f9fff80000003d 0x400ff3fff0000000

def z718 : W := mkw 0x480777b000000000 0x40900eef60000000 0x0001f9f800000000 0x000003f3f0000000

def z719 : W := mkw 0xffff77b010006000 0x47fffeef602000c0 0xfffffff87181ffff 0xfffffffff0e303ff

def z720 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe07f807fe00f80e 0xb7fc0ff00ffc01f0

def z721 : W := mkw 0x4807e84c9213fe72 0x18900fd0992427fc 0x0007f8000001fe20 0x80000ff0000003fc

def z722 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x000000040e7e3800 0x10000000081cfc70

def z723 : W := mkw 0xffff77b020880084 0x47fffeef60411001 0xfffffff8018001bf 0xc7fffffff0030003

def z724 : W := mkw 0xe76d359000000000 0x47ceda6b20000000 0xc7fffff80000003f 0xc38ffffff0000000

def z725 : W := mkw 0x93f817f925fe0e12 0x6d27f02ff24bfc1c 0x01f807f801fe0610 0x4803f00ff003fc0c

def z726 : W := mkw 0xc36d159181408108 0x0186da2b23028102 0xc7fffffb8180c1bf 0xe38ffffff7030183

def z727 : W := mkw 0xffff77b024ac0000 0x67fffeef60495800 0xfffffff8000e003f 0xc7fffffff0001c00

def z728 : W := mkw 0x4a2f77b000000000 0x40945eef60000000 0x0667fff800000024 0xc00ccffff0000000

def z729 : W := mkw 0x4005804480118410 0x00800b0089002308 0xc1e787c781f1c7f7 0xeb83cf0f8f03e38f

def z730 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffffc0070007f 0xcffffffff800e000

def z731 : W := mkw 0xef6f77b34d640000 0x67dedeef669ac800 0xc667ffff8e700024 0xc38ccfffff1ce000

def z732 : W := mkw 0x12b8884c36bf7ed6 0x08257110986d7efd 0x3ff800047fffffdf 0x3c7ff00008ffffff

def z733 : W := mkw 0x2c02e8065a017060 0x125805d00cb402e0 0xfe01f807fe01386f 0x37fc03f00ffc0270

def z734 : W := mkw 0x6c07e8064a011040 0x02d80fd00c940220 0xfe07f807fe01386f 0xb7fc0ff00ffc0270

def z735 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe67f807fe71f87f 0xbffccff00ffce3f0

def z736 : W := mkw 0xb7f810936dec0000 0x276ff02126dbd800 0xfff9b9c7fffe005f 0x3ffff3738ffffc00

def z737 : W := mkw 0xd3fd17b000000000 0x45a7fa2f60000000 0xc7fffff80000003f 0xc38ffffff0000000

def z738 : W := mkw 0xffff77b105640000 0x47fffeef620ac800 0xffffffff8ffe007f 0xffffffffff1ffc00

def z739 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679f9fc0e7f3e4c 0x180cf3f3f81cfe7c

def z740 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679f9fc0e7f3e2c 0x500cf3f3f81cfe7c

def z741 : W := mkw 0xd3fd37b000000000 0x45a7fa6f60000000 0x01f9bff800000010 0x4003f37ff0000000

def z742 : W := mkw 0xb7f802236dec0084 0x276ff00446dbd801 0xfff80607fffe01df 0x3ffff00c0ffffc03

def z743 : W := mkw 0xc36d159105640000 0x0186da2b220ac800 0xc7ffffff8ffe007f 0xfb8fffffff1ffc00

def z744 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff8000e007f 0xdffffffff0001c00

def z745 : W := mkw 0xffff77b09000e020 0x57fffeef612001c0 0xfffffff80000c03f 0xc7fffffff0000180

def z746 : W := mkw 0xc36d1d9987669b4a 0x0986da3b330ecd36 0xc79e7e3b8f8ef98a 0xb38f3cfc771f1df3

def z747 : W := mkw 0x0228884c06371e52 0x08045110980c6e3c 0x007800040e7f3e50 0x1800f000081cfe7c

def z748 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x000040040e7f3e69 0x18000080081cfe7c

def z749 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0xf99e463ff18fffff 0xfff33c8c7fe31fff

def z750 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x018606040ffffff3 0xf8030c0c081fffff

def z751 : W := mkw 0xb5d0000369c80000 0x036ba00006d39000 0xfff80007fffe005f 0x3ffff0000ffffc00

def z752 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xffffbff800000016 0xc7ffff7ff0000000

def z753 : W := mkw 0x240000036dec0000 0x2248000006dbd800 0xf8000007fffe0042 0x3ff000000ffffc00

def z754 : W := mkw 0xfdd7ef6c06371e52 0x4ffbafded80c6e3c 0xf98606040e7f3e42 0x9ff30c0c081cfe7c

def z755 : W := mkw 0x2e2a709000000000 0x025c54e120000000 0x3e79f9f80000003d 0x447cf3f3f0000000

def z756 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfff9f9f80000001f 0x07fff3f3f0000000

def z757 : W := mkw 0xffff77b3d940e128 0x57fffeef67b281c2 0xfffffffbf180c1bf 0xe7fffffff7e30183

def z758 : W := mkw 0x5abf77b000000000 0x44b57eef60000000 0x001ffff800000020 0xc0003ffff0000000

def z759 : W := mkw 0xffff77b004240000 0x47fffeef60084800 0xfffffffc0e70003f 0xc7fffffff81ce000

def z760 : W := mkw 0xbffa52bb7dee6a84 0x277ff4a576fbdcd5 0xffffffffffffffff 0xffffffffffffffff

def z761 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xffffffff8000007f 0xe7ffffffff000000

def z762 : W := mkw 0x422d109000000000 0x00845a2120000000 0xc67ff9f80000003f 0xc38cfff3f0000000

def z763 : W := mkw 0x6405a806da01f060 0x12c80b500db403e0 0xfe01b807fe01f84f 0x37fc03700ffc03f0

def z764 : W := mkw 0xb7f817b36dec0000 0x676ff02f66dbd800 0xfff9fffffffe007f 0x7ffff3fffffffc00

def z765 : W := mkw 0x0000884d07771e52 0x080001109a0eee3c 0x000000078fff3e40 0x380000000f1ffe7c

def z766 : W := mkw 0x8368109101400000 0x0106d02122028000 0xc7f9f9ff81f0007f 0x6b8ff3f3ff03e000

def z767 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x3f9ffe38718fffff 0xfc7f3ffc70e31fff

def z768 : W := mkw 0x6c07ed06da01f168 0x12d80fda0db403e2 0xfe07fe07fe01f9ef 0xb7fc0ffc0ffc03f3

def z769 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff981c7fffe007f 0x7ffff3038ffffc00

def z770 : W := mkw 0xffff77b004240000 0x47fffeef60084800 0xfffffff80e0e003f 0xd7fffffff01c1c00

def z771 : W := mkw 0x422d159000000000 0x00845a2b20000000 0x067ffff80000003d 0xc00cfffff0000000

def z772 : W := mkw 0x36b810926cac0000 0x266d702124d95800 0x3e79f9f87e0e003d 0x547cf3f3f0fc1c00

def z773 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e787c781f1c7a6 0xe383cf0f8f03e38f

def z774 : W := mkw 0x9bfa57b000000000 0x4537f4af60000000 0x3ffffff80000003f 0xc47ffffff0000000

def z775 : W := mkw 0xffff77b24c240000 0x47fffeef64984800 0xfffffffffe7e007f 0xfffffffffffcfc00

def z776 : W := mkw 0xa76810934d640000 0x274ed021269ac800 0xc661b9c78e700004 0x038cc3738f1ce000

def z777 : W := mkw 0xffff77b105640000 0x67fffeef620ac800 0xfffffff80070003f 0xc7fffffff000e000

def z778 : W := mkw 0x4807709000000000 0x00900ee120000000 0x0007f9f800000020 0xc0000ff3f0000000

def z779 : W := mkw 0xa76810934d640000 0x274ed021269ac800 0xc679f9ff8e70003d 0x438cf3f3ff1ce000

def z780 : W := mkw 0xc94777b000000000 0x41928eef60000000 0x01e7fff800000030 0xc003cffff0000000

def z781 : W := mkw 0xed4777b000000000 0x47da8eef60000000 0xc007fff800000020 0xc3800ffff0000000

def z782 : W := mkw 0x6e2f70dadc36ee32 0x1adc5ee1b5b86ddc 0xf87e01fbf07ec612 0xeff0fc03f7e0fd8c

def z783 : W := mkw 0x0000884eda13fe72 0x180001109db427fc 0x00000007fe01fe40 0x300000000ffc03fc

def z784 : W := mkw 0xffff77b36dec0000 0x67fffeef66dbd800 0xffffffffffffc7ff 0xffffffffffffff8f

def z785 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff80007ffffc7df 0x3ffff0000fffff8f

def z786 : W := mkw 0x76bd8546ecbd8518 0x26ed7b0a8dd97b0a 0x3e1f87c07e0fc7a8 0xd47c3f0f80fc1f8f

def z787 : W := mkw 0x10900008208a0a00 0x0021200010411414 0x399e4638718ffffb 0xfc733c8c70e31fff

def z788 : W := mkw 0x480777b000000000 0x40900eef60000000 0x0067fff800000035 0xc000cffff0000000

def z789 : W := mkw 0xfdd76723f9c8e020 0x77fbaece47f391c0 0xf9860603f180c002 0xa7f30c0c07e30180

def z790 : W := mkw 0x6c07ef26da01f060 0x52d80fde4db403e0 0xfe07fe07fe01f86f 0xb7fc0ffc0ffc03f0

def z791 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe1ff83ffe01f87f 0xf7fc3ff07ffc03f0

def z792 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xf9f80007fffe0052 0x3ff3f0000ffffc00

def z793 : W := mkw 0x0000884f4f771e52 0x280001109e9eee3c 0x000000078e7f3e40 0x180000000f1cfe7c

def z794 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff80607fffe07df 0x7ffff00c0ffffc0f

def z795 : W := mkw 0xb7f830936dec0000 0x676ff06126dbd800 0xfff83807fffe005f 0x3ffff0700ffffc00

def z796 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1ff87c781ffc7ff 0xfb83ff0f8f03ff8f

def z797 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679f9fc0e7f386d 0x100cf3f3f81cfe70

def z798 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffffc0e00007f 0xd7fffffff81c0000

def z799 : W := mkw 0xe76dbdd7cf75957a 0x1bcedb7baf9eeb2a 0xc661b9c78e700004 0x038cc3738f1ce000

def z800 : W := mkw 0xbffa72b000000000 0x477ff4e560000000 0xfff9f9f80000003f 0x47fff3f3f0000000

def z801 : W := mkw 0xffff77b181408108 0x47fffeef63028102 0xffffffff81f0c1ff 0xefffffffff03e183

def z802 : W := mkw 0x240008024a001040 0x0248001004940020 0xfe007807fe00384f 0x37fc00f00ffc0070

def z803 : W := mkw 0x480777b000000000 0x40900eef60000000 0xc007fff800000027 0xc3800ffff0000000

def z804 : W := mkw 0xffff77b030886000 0x47fffeef606110c0 0xfffffff8718ff87f 0xfffffffff0e31ff0

def z805 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e787c781f1c7c6 0xab83cf0f8f03e38f

def z806 : W := mkw 0xb7f8884c06371e52 0x0f6ff110980c6e3c 0xfff800040e7f3e5f 0x1ffff000081cfe7c

def z807 : W := mkw 0xbffa52b000000000 0x077ff4a560000000 0xfffffff80000003f 0xc7fffffff0000000

def z808 : W := mkw 0xffff77b2f888e0a4 0x57fffeef65f111c1 0xfffffffbf180c1bf 0xe7fffffff7e30183

def z809 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfffe0607fffe007f 0xfffffc0c0ffffc00

def z810 : W := mkw 0xb5d000036dec0000 0x276ba00006dbd800 0xff800007fffe004f 0x3fff00000ffffc00

def z811 : W := mkw 0x36b800026cac0000 0x026d700004d95800 0xfff80007fffe005f 0x3ffff0000ffffc00

def z812 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e607c781f1c7d2 0xeb83cc0f8f03e38f

def z813 : W := mkw 0xc145159000000000 0x01828a2b20000000 0xc1e7fff800000037 0xc383cffff0000000

def z814 : W := mkw 0xffff77b010006000 0x47fffeef602000c0 0xfffffff80001f83f 0xc7fffffff00003f0

def z815 : W := mkw 0xfdd76723f9c8e1ac 0x13fbaece47f391c3 0xf9860603f180c182 0xa7f30c0c07e30183

def z816 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfe7ffff80000002c 0xc7fcfffff0000000

def z817 : W := mkw 0xc1458d4583519558 0x01828b1a8b06a32a 0xc1e7ffc781f1fff7 0xeb83cfff8f03e3ff

def z818 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff80007ffff067f 0x7ffff0000ffffe0c

def z819 : W := mkw 0x64058806ca019040 0x02c80b100d940320 0xfe07f807fe01f86f 0xb7fc0ff00ffc03f0

def z820 : W := mkw 0x8140000101400000 0x0102800002028000 0xc1e181c781f00077 0x6b83c3038f03e000

def z821 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x07fffffc0e7f3e7f 0xd80ffffff81cfe7c

def z822 : W := mkw 0x4807fffc9213fe72 0x58900ffff92427fc 0x0007fff80001fe20 0xc0000ffff00003fc

def z823 : W := mkw 0xb7f802236dec0000 0x276ff00446dbd800 0xfff8063ffffe005f 0x7ffff00c7ffffc00

def z824 : W := mkw 0x0000884c16377ed6 0x08000110982c6efd 0x000000040e7fffc0 0x18000000081cffff

def z825 : W := mkw 0xad426d435b507578 0x135a84da86b6a0ea 0x3fe07fc07ff03f98 0x5c7fc0ff80ffe07f

def z826 : W := mkw 0x93f8000125ec0000 0x0127f000024bd800 0xfff80007fffe005f 0x3ffff0000ffffc00

def z827 : W := mkw 0xef6f77b000000000 0x47dedeef60000000 0xfe67fff80000002f 0xc7fccffff0000000

def z828 : W := mkw 0x0228109004240000 0x0004502120084800 0x0679f9fc0e70003d 0x400cf3f3f81ce000

def z829 : W := mkw 0xffff77b34d640000 0x67fffeef669ac800 0xffffffff8ff0007f 0xefffffffff1fe000

def z830 : W := mkw 0x3eba72ba7cae6a84 0x667d74e574f95cd5 0x3e1878387e0e3808 0x147c30f070fc1c70

def z831 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe1ff807fe0ff87f 0xbffc3ff00ffc1ff0

def z832 : W := mkw 0x6c076802da00f060 0x12d80ed005b401e0 0xfe07f803fe00f82f 0xb7fc0ff007fc01f0

def z833 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfe780007fe7e004f 0x37fcf0000ffcfc00

def z834 : W := mkw 0xd9d777b000000000 0x41b3aeef60000000 0xf9fffff80000003f 0xc7f3fffff0000000

def z835 : W := mkw 0xffff77b020880000 0x47fffeef60411000 0xfffffff87180003f 0xe7fffffff0e30000

def z836 : W := mkw 0xffff77b010006084 0x47fffeef602000c1 0xfffffff80000c1bf 0xc7fffffff0000183

def z837 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x399e0638718fffd2 0xfc733c0c70e31fff

def z838 : W := mkw 0x2400000248000000 0x0248000004900000 0xfe01f807fe00006f 0x37fc03f00ffc0000

def z839 : W := mkw 0x0000884efebffef6 0x180001109dfd7ffd 0x00000007ffffffc0 0x380000000fffffff

def z840 : W := mkw 0xb7f812b36dec0000 0x676ff02566dbd800 0xfff8003ffffe005f 0x3ffff0007ffffc00

def z841 : W := mkw 0xc145050101400000 0x01828a0a02028000 0xc1e787c781f1c7f7 0xeb83cf0f8f03e38f

def z842 : W := mkw 0x6c076802da00f060 0x12d80ed005b401e0 0xfe067807fe00f84f 0xb7fc0cf00ffc01f0

def z843 : W := mkw 0x6c07ea26da01f060 0x12d80fd44db403e0 0xfe07fe3ffe01f86f 0xf7fc0ffc7ffc03f0

def z844 : W := mkw 0xd9d7c76db1dbef9c 0x01b3af8edb63b7df 0xf879c1fff07e380c 0x17f0f383ffe0fc70

def z845 : W := mkw 0xffff77b26cac0000 0x67fffeef64d95800 0xfffffffc7e7e007f 0xdffffffff8fcfc00

def z846 : W := mkw 0x8140054101500518 0x0102800a8202a00a 0xc1e607c781f1c7f7 0xeb83cc0f8f03e38f

def z847 : W := mkw 0x93f89fb6da01f060 0x5527f13f6db403e0 0x01f807fffe01f850 0x7003f00ffffc03f0

def z848 : W := mkw 0x2c02e806da01f060 0x125805d00db403e0 0xfe007807fe01f84f 0x37fc00f00ffc03f0

def z849 : W := mkw 0x0228189806261a42 0x08045031300c4c34 0x0679f9fc0e7e387d 0x580cf3f3f81cfc70

def z850 : W := mkw 0x93f815d925fe0f1a 0x2d27f02bb24bfc1e 0x01f807f801fe0790 0x4803f00ff003fc0f

def z851 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc7e7ffc781f1c7ff 0xeb8fcfff8f03e38f

def z852 : W := mkw 0x0a2a509000000000 0x001454a120000000 0x3e7ff9f80000003f 0xc47cfff3f0000000

def z853 : W := mkw 0x0228109000000000 0x0004502120000000 0x07fffff80000003f 0xc00ffffff0000000

def z854 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff8403ffffe007f 0x7ffff0807ffffc00

def z855 : W := mkw 0x6c07e846da11f470 0x12d80fd08db423e8 0xfe07f9c7fe01fe6f 0xf7fc0ff38ffc03fc

def z856 : W := mkw 0xf7fd95d7edfd8518 0x27effb2bafdbfb0a 0xffffffffffffc7ff 0xffffffffffffff8f

def z857 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xffe7fff800000026 0xc7ffcffff0000000

def z858 : W := mkw 0x4807dffc9213ffde 0x08900fbff92427ff 0x0007fff80001ffa0 0xc0000ffff00003ff

def z859 : W := mkw 0x0802c84c16377e52 0x08100590982c6efc 0x380640047e7ffe6b 0xbc700c8008fcfffc

def z860 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe07f807fe00382f 0x97fc0ff00ffc0070

def z861 : W := mkw 0xffff77b030886084 0x47fffeef606110c1 0xfffffff87000003f 0xc7fffffff0e00000

def z862 : W := mkw 0xef6f759000000000 0x03dedeeb20000000 0xfffffff80000003f 0xc7fffffff0000000

def z863 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xff9ffff80000002a 0xc7ff3ffff0000000

def z864 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfe79f9f80000003d 0x47fcf3f3f0000000

def z865 : W := mkw 0xdbffe805b7edf060 0x35b7ffd00b6fdbe0 0x01fff80001fff830 0x8803fff00003fff0

def z866 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff9f807fffe007f 0x3ffff3f00ffffc00

def z867 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe07f807fe01f826 0xa7fc0ff00ffc03f0

def z868 : W := mkw 0xffff77b24c240000 0x67fffeef64984800 0xfffffff80e00003f 0xc7fffffff01c0000

def z869 : W := mkw 0xdbff57b000000000 0x01b7feaf60000000 0xfffffff80000003f 0xc7fffffff0000000

def z870 : W := mkw 0xf7fd15936dec0000 0x27effa2b26dbd800 0xfffffffffffe007f 0xfffffffffffffc00

def z871 : W := mkw 0x662d309000000000 0x02cc5a6120000000 0xc679f9f80000003d 0x438cf3f3f0000000

def z872 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff80007fffe001c 0x1ffff0000ffffc00

def z873 : W := mkw 0x0000884d87779f5a 0x080001109b0eef3e 0x000000078e7f3e40 0x180000000f1cfe7c

def z874 : W := mkw 0xffff77b26cac0000 0x67fffeef64d95800 0xfffffffffe0e007f 0xf7fffffffffc1c00

def z875 : W := mkw 0x2c0268025a007060 0x125804d004b400e0 0xfe007807fe00380c 0x17fc00f00ffc0070

def z876 : W := mkw 0xffff77b125ec0000 0x67fffeef624bd800 0xfffffffc0ffe007f 0xdffffffff81ffc00

def z877 : W := mkw 0x12b8109000000000 0x0025702120000000 0x3ff9f9f80000003f 0x447ff3f3f0000000

def z878 : W := mkw 0xdbff77b000000000 0x45b7feef60000000 0x07fffff80000003d 0xc00ffffff0000000

def z879 : W := mkw 0xfdd777b369c80000 0x67fbaeef66d39000 0xf987fffbf1800022 0xe7f30ffff7e30000

def z880 : W := mkw 0x0228109804260a00 0x0004502130084c14 0x0679f9fc0e7f3e7d 0x580cf3f3f81cfe7c

def z881 : W := mkw 0xa768109000000000 0x074ed02120000000 0xc679f9f80000003d 0x438cf3f3f0000000

def z882 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x000000040fffffc0 0x38000000081fffff

def z883 : W := mkw 0x6c0768025a007060 0x12d80ed004b400e0 0xfe07f807fe00386f 0xb7fc0ff00ffc0070

def z884 : W := mkw 0xffff77b2c8008020 0x57fffeef65900100 0xfffffffb8000003f 0xc7fffffff7000000

def z885 : W := mkw 0xc1458d4583519558 0x01828b1a8b06a32a 0xc1e787c78ff1fff7 0xfb83cf0f8f1fe3ff

def z886 : W := mkw 0xa76800036dec0000 0x274ed00006dbd800 0xfe600007fffe004f 0x3ffcc0000ffffc00

def z887 : W := mkw 0x0802400810026a00 0x00100480102004d4 0x399e4638718ffffb 0xfc733c8c70e31fff

def z888 : W := mkw 0xfdd7672379c86084 0x67fbaece46f390c1 0xf9860603f180c182 0xa7f30c0c07e30183

def z889 : W := mkw 0x8368109000000000 0x0106d02120000000 0xc7f9f9f80000003f 0x438ff3f3f0000000

def z890 : W := mkw 0x8368884d87779f5a 0x0906d1109b0eef3e 0xc7f800078fffffdf 0x3b8ff0000f1fffff

def z891 : W := mkw 0x6c07e846da11f470 0x12d80fd08db423e8 0xffe7ffc7fff1ffff 0xffffcfff8fffe3ff

def z892 : W := mkw 0xffff77b2d800e020 0x57fffeef65b001c0 0xfffffffffe00c07f 0xf7fffffffffc0180

def z893 : W := mkw 0x0000109000000000 0x0000002120000000 0x0601f9f80000002d 0x400c03f3f0000000

def z894 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe07f807fe01f82c 0x97fc0ff00ffc03f0

def z895 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xff87fe07fe01f87f 0xf7ff0ffc0ffc03f0

def z896 : W := mkw 0x589777b020880000 0x40b12eef60411000 0x399ffff8718e007b 0xfc733ffff0e31c00

def z897 : W := mkw 0x2628884ede37fe72 0x1a4c51109dbc6ffc 0xfe780007fe7ffe5f 0x3ffcf0000ffcfffc

def z898 : W := mkw 0x4a2f77b000000000 0x40945eef60000000 0x061ffff800000028 0xc00c3ffff0000000

def z899 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfe780007fe7e005d 0x1ffcf0000ffcfc00

def z900 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1ffc7ff81f1c7ff 0xeb83ff8fff03e38f

def z901 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0xc679f9ff8e7f3e7f 0x7b8cf3f3ff1cfe7c

def z902 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff84007ffff387f 0x3ffff0800ffffe70

def z903 : W := mkw 0xffff77b37dec6084 0x67fffeef66fbd8c1 0xfffffffffffec1ff 0xfffffffffffffd83

def z904 : W := mkw 0x589777b030886084 0x40b12eef606110c1 0x3987fff87180c1a2 0xe4730ffff0e30183

def z905 : W := mkw 0x6c07709000000000 0x02d80ee120000000 0xfe07f9f80000002f 0xc7fc0ff3f0000000

def z906 : W := mkw 0x480777b000000000 0x40900eef60000000 0x0007fff80001c7a0 0xc0000ffff000038f

def z907 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc7e787c78ff1c7ff 0xfb8fcf0f8f1fe38f

def z908 : W := mkw 0x6c0777b000000000 0x42d80eef60000000 0xc607fff800000024 0xc38c0ffff0000000

def z909 : W := mkw 0x6c0777b000000000 0x42d80eef60000000 0xf807fff800000022 0xc7f00ffff0000000

def z910 : W := mkw 0x022898dc86379f5a 0x08045131b90c6f3e 0x0679f9fc0e7ffffd 0x580cf3f3f81cffff

def z911 : W := mkw 0x4807fafc9213fef6 0x18900ff5f92427fd 0x0007fff80001ffa0 0xc0000ffff00003ff

def z912 : W := mkw 0xffff77b3edec8108 0x67fffeef67dbd902 0xfffffffffffec1ff 0xfffffffffffffd83

def z913 : W := mkw 0xaf6a422b5d666a84 0x275ed48456baccd5 0xc666463f8e71ffa4 0xc38ccc8c7f1ce3ff

def z914 : W := mkw 0x7ebf77b000000000 0x46fd7eef60000000 0xfe1ffff80000002f 0xc7fc3ffff0000000

def z915 : W := mkw 0x480777b010006084 0x40900eef602000c1 0x0007fff80000c1a0 0xc0000ffff0000183

def z916 : W := mkw 0x240000024c240000 0x0248000004984800 0xfe000007fe7e004f 0x3ffc00000ffcfc00

def z917 : W := mkw 0x0000884c12137ed6 0x08000110982426fd 0x000000000001ff80 0x00000000000003ff

def z918 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x399e4638718fffaa 0xf4733c8c70e31fff

def z919 : W := mkw 0xdbff77b000000000 0x45b7feef60000000 0x39fffff80000003b 0xc473fffff0000000

def z920 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xf9e787c7f1f1c7ff 0xfff3cf0f8fe3e38f

def z921 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x067ff9fc0e7ffe7f 0xf80cfff3f81cfffc

def z922 : W := mkw 0x0000884c86379f5a 0x08000110990c6f3e 0x000000040e7fffc0 0x18000000081cffff

def z923 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfffe0607fffec1df 0xbffffc0c0ffffd83

def z924 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x39ffc7f8718fffff 0xfc73ff8ff0e31fff

def z925 : W := mkw 0x3ebaf2f581518518 0x467d75e5eb02a30a 0x3e18783f81f1c7c8 0x2c7c30f07f03e38f

def z926 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xffe00007fffe0046 0x3fffc0000ffffc00

def z927 : W := mkw 0xef6f759000000000 0x47dedeeb20000000 0xfe7ff9f80000003f 0xc7fcfff3f0000000

def z928 : W := mkw 0xffff77b34d640000 0x67fffeef669ac800 0xfffffffffe70007f 0xf7fffffffffce000

def z929 : W := mkw 0x6c07ed46da11f578 0x12d80fda8db423ea 0xff87ffc7ff81ffff 0xffff0fff8fff03ff

def z930 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe07f807fe01fe7f 0xfffc0ff00ffc03fc

def z931 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x39fe463c71ffffff 0xfc73fc8c78e3ffff

def z932 : W := mkw 0xffff77b1b1c8e18c 0x47fffeef636391c3 0xfffffffbf180c1bf 0xe7fffffff7e30183

def z933 : W := mkw 0xdbff77b125ec0000 0x65b7feef624bd800 0x01fffff801fe0030 0xc803fffff003fc00

def z934 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff80001c07f 0xe7fffffff0000380

def z935 : W := mkw 0xf7fd37b36dec0000 0x67effa6f66dbd800 0xc7f9bfff8ffe0014 0x4b8ff37fff1ffc00

def z936 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679f9fc0e7e3e1c 0x580cf3f3f81cfc7c

def z937 : W := mkw 0xffff77b101400000 0x47fffeef62028000 0xfffffff801f0003f 0xcffffffff003e000

def z938 : W := mkw 0xb7f8884ffffffe72 0x3f6ff1109ffffffc 0xfff80007fffffe5f 0x3ffff0000ffffffc

def z939 : W := mkw 0xf7fd37b000000000 0x47effa6f60000000 0xfff9bff80000001f 0x47fff37ff0000000

def z940 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff8018007bf 0xcffffffff003000f

def z941 : W := mkw 0xffff77b010006000 0x47fffeef602000c0 0xfffffff87000c03f 0xe7fffffff0e00180

def z942 : W := mkw 0xcb6f77b000000000 0x4196deef60000000 0xc7fffff80000003f 0xc38ffffff0000000

def z943 : W := mkw 0x0228109000000000 0x0004502120000000 0x0079f9f800000030 0x4000f3f3f0000000

def z944 : W := mkw 0xa768884f4f771e52 0x2f4ed1109e9eee3c 0xc66000078e7f3e44 0x1b8cc0000f1cfe7c

def z945 : W := mkw 0x3eba72b000000000 0x467d74e560000000 0x3e79f9f80000000c 0x047cf3f3f0000000

def z946 : W := mkw 0x589777b000000000 0x40b12eef60000000 0x3987fff800000022 0xc4730ffff0000000

def z947 : W := mkw 0x36b810926cac0000 0x266d702124d95800 0x3e1878387e0e0008 0x147c30f070fc1c00

def z948 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfffe0007ffffc07f 0xbffffc000fffff80

def z949 : W := mkw 0x0000884c02131e52 0x080001109804263c 0x00000000000f3e40 0x1800000000001e7c

def z950 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff80007fffe0016 0x2ffff0000ffffc00

def z951 : W := mkw 0x1892ca6c36bf7ed6 0x08312594d86d7efd 0x398606047fffffc2 0xbc730c0c08ffffff

def z952 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe67f9c7fe01f87f 0xf7fccff38ffc03f0

def z953 : W := mkw 0x480777b000000000 0x40900eef60000000 0x001ffff800000039 0xc0003ffff0000000

def z954 : W := mkw 0xe76d9dd7cf75955a 0x2fcedb3baf9eeb2a 0xc661b9c78e700004 0x038cc3738f1ce000

def z955 : W := mkw 0xb7f810936dec0000 0x276ff02126dbd800 0xfff8783ffffe005f 0x3ffff0f07ffffc00

def z956 : W := mkw 0xf7fd37b000000000 0x47effa6f60000000 0xc679b9f800000004 0x038cf373f0000000

def z957 : W := mkw 0xffff77b3fdece020 0x77fffeef67fbd9c0 0xfffffffffffec07f 0xfffffffffffffd80

def z958 : W := mkw 0x93f8109125ec0000 0x2527f021224bd800 0x01f801f801fe0010 0x4803f003f003fc00

def z959 : W := mkw 0x6c076802da00f060 0x12d80ed005b401e0 0xfe007803fe003808 0x17fc00f007fc0070

def z960 : W := mkw 0xe76d35934d640000 0x67ceda6b269ac800 0xc679f9ff8e7e007d 0x5b8cf3f3ff1cfc00

def z961 : W := mkw 0x24008806da01f060 0x124801100db403e0 0xfe01f807fe01f86f 0x37fc03f00ffc03f0

def z962 : W := mkw 0xffff77b101400000 0x47fffeef62028000 0xfffffffb8180003f 0xe7fffffff7030000

def z963 : W := mkw 0x0228109000000000 0x0004502120000000 0x0679f9f80001067d 0x480cf3f3f000020c

def z964 : W := mkw 0x6c07e846da11f470 0x12d80fd08db423e8 0xfe07f807fe71fe6f 0xbffc0ff00ffce3fc

def z965 : W := mkw 0x7ebf77b000000000 0x46fd7eef60000000 0x3e19f9f800000008 0x047c33f3f0000000

def z966 : W := mkw 0xffff77b34d640000 0x67fffeef669ac800 0xffffffff8e7e007f 0xdfffffffff1cfc00

def z967 : W := mkw 0xa76800034d640000 0x274ed000069ac800 0xfe780007fe7e005f 0x3ffcf0000ffcfc00

def z968 : W := mkw 0x0000884c02131e52 0x080001109804263c 0x0000000400713e40 0x080000000800e27c

def z969 : W := mkw 0xffff77b020880000 0x47fffeef60411000 0xfffffff8700e003f 0xd7fffffff0e01c00

def z970 : W := mkw 0xffff77b36dec0000 0x67fffeef66dbd800 0xfff9f9fffffe005f 0x3ffff3f3fffffc00

def z971 : W := mkw 0x022898dc86379e52 0x08045131b90c6f3c 0x0679f9ff8e7ffe7d 0x780cf3f3ff1cfffc

def z972 : W := mkw 0xffff709000000000 0x07fffee120000000 0xfffff9f80000003f 0xc7fffff3f0000000

def z973 : W := mkw 0x262800036dec0000 0x224c500006dbd800 0xfe780007fffe005f 0x3ffcf0000ffffc00

def z974 : W := mkw 0x7ebf77b26cac0000 0x66fd7eef64d95800 0x3e1ffff87e0e0028 0xd47c3ffff0fc1c00

def z975 : W := mkw 0xc145054181508518 0x01828a0a8302a10a 0xc1e787c381f0c7b7 0xeb83cf0f8703e18f

def z976 : W := mkw 0xb7f810936dec0000 0x276ff02126dbd800 0xfff801fffffe005f 0x7ffff003fffffc00

def z977 : W := mkw 0xed4777b000000000 0x43da8eef60000000 0xffe7fff80000003f 0xc7ffcffff0000000

def z978 : W := mkw 0x7ebf72b000000000 0x46fd7ee560000000 0xfe7ff9f80000003f 0xc7fcfff3f0000000

def z979 : W := mkw 0x6e2f70924c240000 0x02dc5ee124984800 0xfe7ff9fffe7e007f 0xfffcfff3fffcfc00

def z980 : W := mkw 0x4005359000000000 0x40800a6b20000000 0x0001f9f800000020 0x400003f3f0000000

def z981 : W := mkw 0x6c0777b248000000 0x42d80eef64900000 0xfe07fffffe00006f 0xf7fc0ffffffc0000

def z982 : W := mkw 0xf7fd359000000000 0x47effa6b20000000 0xfff9f9f80000003f 0x47fff3f3f0000000

def z983 : W := mkw 0x0228989406251040 0x00045131280c4a20 0x0679f9fc0e7f387d 0x580cf3f3f81cfe70

def z984 : W := mkw 0xffff77b030886084 0x47fffeef606110c1 0xfffffff87181c7ff 0xeffffffff0e3038f

def z985 : W := mkw 0x7ebf72b000000000 0x02fd7ee560000000 0xfffffff80000003f 0xc7fffffff0000000

def z986 : W := mkw 0xffff77b181408108 0x47fffeef63028102 0xfffffffb8000003f 0xc7fffffff7000000

def z987 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfff9fff80000001c 0x47fff3fff0000000

def z988 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679f9fc0e7e385d 0x180cf3f3f81cfc70

def z989 : W := mkw 0x2628109248000000 0x024c502124900000 0xfe79f9fffe00007f 0x77fcf3f3fffc0000

def z990 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679f9fc0ffffffd 0x780cf3f3f81fffff

def z991 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679f9fc0e7e383d 0x500cf3f3f81cfc70

def z992 : W := mkw 0x93f8109000000000 0x0527f02120000000 0x07f9f9f80000003d 0x400ff3f3f0000000

def z993 : W := mkw 0xd9d777b000000000 0x45b3aeef60000000 0x0187fff800000020 0xc0030ffff0000000

def z994 : W := mkw 0x0228109000000000 0x0004502120000000 0x0679f9f8000e007d 0x580cf3f3f0001c00

def z995 : W := mkw 0x0228884c06371e52 0x08045110980c6e3c 0x066000040e7f3e44 0x180cc000081cfe7c

def z996 : W := mkw 0x0000884f7fff7ed6 0x280001109efffefd 0x00000007ffffffc0 0x380000000fffffff

def z997 : W := mkw 0xffff77b36dec0000 0x67fffeef66dbd800 0xfffffffbf1fe003f 0xeffffffff7e3fc00

def z998 : W := mkw 0xa76800034d640000 0x034ed000069ac800 0xfff80007fffe005f 0x3ffff0000ffffc00

def z999 : W := mkw 0xfdd7672000000000 0x03fbaece40000000 0xfffffff80000003f 0xc7fffffff0000000

def z1000 : W := mkw 0x12b812b000000000 0x4425702560000000 0x0679f9f80000003d 0x400cf3f3f0000000

def z1001 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e787c781f1c7b4 0xcb83cf0f8f03e38f

def z1002 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x006000040e7f3e55 0x1800c000081cfe7c

def z1003 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe07b807fe01f846 0xb7fc0f700ffc03f0

def z1004 : W := mkw 0x0000884c82139f5a 0x080001109904273e 0x000000000001ff80 0x00000000000003ff

def z1005 : W := mkw 0x0000884c26bf1e52 0x08000110984d7e3c 0x000000047fff3e40 0x3800000008fffe7c

def z1006 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x00000000007f3e00 0x080000000000fe7c

def z1007 : W := mkw 0xef6f77b000000000 0x47dedeef60000000 0xc661f9f800000004 0x038cc3f3f0000000

def z1008 : W := mkw 0x0000884d83539f5a 0x080001109b06a73e 0x0000000781f1ffc0 0x280000000f03e3ff

def z1009 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xc7fffff800000034 0xc38ffffff0000000

def z1010 : W := mkw 0xffff77b020880000 0x47fffeef60411000 0xfffffff8018e003f 0xcffffffff0031c00

def z1011 : W := mkw 0x0228109000000000 0x0004502120000000 0x0679f9fc0070007d 0x480cf3f3f800e000

def z1012 : W := mkw 0x6c07e846da11f578 0x12d80fd08db423ea 0xfe07f807fe01ffef 0xb7fc0ff00ffc03ff

def z1013 : W := mkw 0x2c02c8065a017040 0x025805900cb402e0 0xfe07f807fe01f86f 0xb7fc0ff00ffc03f0

def z1014 : W := mkw 0x5abf77b000000000 0x40b57eef60000000 0x3ffffff80000003f 0xc47ffffff0000000

def z1015 : W := mkw 0x93f817b000000000 0x4527f02f60000000 0x07f9bff800000014 0x400ff37ff0000000

def z1016 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe01f807fe00384f 0x37fc03f00ffc0070

def z1017 : W := mkw 0xffff77b369c80000 0x67fffeef66d39000 0xfffffffff1f0007f 0xefffffffffe3e000

def z1018 : W := mkw 0xdbff77b000000000 0x45b7feef60000000 0xc1fffff800000037 0xc383fffff0000000

def z1019 : W := mkw 0x0000884d27ff1e52 0x280001109a4ffe3c 0x000000040fff3e40 0x18000000081ffe7c

def z1020 : W := mkw 0x0228109000000000 0x0004502120000000 0x0679b9f800000014 0x400cf373f0000000

def z1021 : W := mkw 0xffff77b37dec6000 0x67fffeef66fbd8c0 0xfffffffffffff87f 0xfffffffffffffff0

def z1022 : W := mkw 0x0000884d07771f5a 0x080001109a0eee3e 0x000000040fff3fc0 0x18000000081ffe7f

def z1023 : W := mkw 0x8140884d07771e52 0x090281109a0eee3c 0xc1e000078fff3e57 0x3b83c0000f1ffe7c

def z1024 : W := mkw 0x0000884ece379e72 0x180001109d9c6f3c 0x000000078e7f3e40 0x180000000f1cfe7c

def z1025 : W := mkw 0x0a2a509010006000 0x001454a1202000c0 0x3e7ff9f87001f87f 0xf47cfff3f0e003f0

def z1026 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xff87f807ff81f87f 0xbfff0ff00fff03f0

def z1027 : W := mkw 0x93f817b925ee0a84 0x6527f02f724bdc15 0x01f807f801fe0790 0x4803f00ff003fc0f

def z1028 : W := mkw 0x2628109000000000 0x024c502120000000 0xfe79f9f80000003f 0x47fcf3f3f0000000

def z1029 : W := mkw 0x4a2f709000000000 0x00945ee120000000 0x067ff9f80000003d 0xc00cfff3f0000000

def z1030 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xff87fe07ff81f9ef 0xb7ff0ffc0fff03f3

def z1031 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x07f9fffc0fff3ffd 0x580ff3fff81ffe7f

def z1032 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x399e4638718fffb8 0xdc733c8c70e31fff

def z1033 : W := mkw 0xffff77b36dec0000 0x67fffeef66dbd800 0xfffffff87ffe003f 0xdffffffff0fffc00

def z1034 : W := mkw 0xb5d000036dec0000 0x276ba00006dbd800 0xf9980007fffe005b 0x3ff330000ffffc00

def z1035 : W := mkw 0x0000884e6ebf1e52 0x280001109cdd7e3c 0x000000047e7f3e40 0x1800000008fcfe7c

def z1036 : W := mkw 0x4807c8049201f040 0x00900f90092403e0 0xfe07f807fe01f86f 0xb7fc0ff00ffc03f0

def z1037 : W := mkw 0xb7f805036dec0108 0x276ff00a06dbd802 0xfff80607fffe01df 0x3ffff00c0ffffc03

def z1038 : W := mkw 0x480777b000000000 0x40900eef60000000 0x0187fff80181c7f3 0xe8030ffff003038f

def z1039 : W := mkw 0xa54000036dec0000 0x234a800006dbd800 0xffe00007fffe005f 0x3fffc0000ffffc00

def z1040 : W := mkw 0x480777b000000000 0x40900eef60000000 0x0607fff80000002d 0xc00c0ffff0000000

def z1041 : W := mkw 0x349000036dec0000 0x2269200006dbd800 0xff980007fffe005f 0x3fff30000ffffc00

def z1042 : W := mkw 0x2c0268025a007060 0x125804d004b400e0 0xfe007803fe00380a 0x37fc00f007fc0070

def z1043 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x000000040e7e0600 0x08000000081cfc0c

def z1044 : W := mkw 0x480777b000000000 0x40900eef60000000 0x3807fff80000002b 0xc4700ffff0000000

def z1045 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff80001067f 0xcffffffff000020c

def z1046 : W := mkw 0xffff77b030886084 0x47fffeef606110c1 0xfffffff87181f9ff 0xf7fffffff0e303f3

def z1047 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0x3ffffff800000038 0xc47ffffff0000000

def z1048 : W := mkw 0xffff77b36dec0000 0x67fffeef66dbd800 0xfffffffffff0003f 0xe7ffffffffffe000

def z1049 : W := mkw 0x0000884c86379e52 0x08000110990c6f3c 0x000000078e7ffe40 0x380000000f1cfffc

def z1050 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e7c7c781f1ffff 0xfb83cf8f8f03e3ff

def z1051 : W := mkw 0x480777b010006000 0x40900eef602000c0 0x3807fff87001f86b 0xf4700ffff0e003f0

def z1052 : W := mkw 0xb7f805036dec0000 0x276ff00a06dbd800 0xfff807c7fffe005f 0x7ffff00f8ffffc00

def z1053 : W := mkw 0xffff77b268880000 0x67fffeef64d11000 0xfffffff87000003f 0xc7fffffff0e00000

def z1054 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xff980007fffe004a 0x3fff30000ffffc00

def z1055 : W := mkw 0xfdd777b000000000 0x47fbaeef60000000 0xf9e7fff800000037 0xc7f3cffff0000000

def z1056 : W := mkw 0x4005854480118518 0x00800b0a8900230a 0x000606000001c780 0x80000c0c0000038f

def z1057 : W := mkw 0x022817b000000000 0x4004502f60000000 0x0679fff80000003d 0x400cf3fff0000000

def z1058 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe07f803fe01f82a 0xb7fc0ff007fc03f0

def z1059 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe07fe07fe01ffef 0xf7fc0ffc0ffc03ff

def z1060 : W := mkw 0x3eba7aba7eae7ae6 0x1a7d74f574fd5cf5 0x3e1878387e0e3808 0x147c30f070fc1c70

def z1061 : W := mkw 0x1aba52b024ac0000 0x003574a560495800 0x3ffffffc7ffe007f 0xfc7ffffff8fffc00

def z1062 : W := mkw 0xfdd777b000000000 0x47fbaeef60000000 0xf99ffff80000003b 0xc7f33ffff0000000

def z1063 : W := mkw 0xffff77b248000000 0x47fffeef64900000 0xfffffffbf000003f 0xe7fffffff7e00000

def z1064 : W := mkw 0xbffa72b36dec0000 0x677ff4e566dbd800 0xfff9f9fffffe007f 0x7ffff3f3fffffc00

def z1065 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe07f807ff81ffef 0xbffc0ff00fff03ff

def z1066 : W := mkw 0x0000884c9637fe72 0x18000110992c6ffc 0x000000040e7ffe40 0x18000000081cfffc

def z1067 : W := mkw 0xb7f815936dec0000 0x676ff02b26dbd800 0xfff801c7fffe005f 0x3ffff0038ffffc00

def z1068 : W := mkw 0x589777b000000000 0x40b12eef60000000 0x381ffff800000028 0xc4703ffff0000000

def z1069 : W := mkw 0x6405a806ca019060 0x12c80b500d940320 0xfe01f807fe01386f 0x37fc03f00ffc0270

def z1070 : W := mkw 0xffff77b349400000 0x47fffeef66928000 0xfffffffffff0007f 0xffffffffffffe000

def z1071 : W := mkw 0xbffa52b36dec0000 0x277ff4a566dbd800 0xfffffffffffe007f 0xfffffffffffffc00

def z1072 : W := mkw 0x93f817b125ec0000 0x6527f02f624bd800 0x07f9fffc0ffe007d 0x580ff3fff81ffc00

def z1073 : W := mkw 0x7c9777b000000000 0x42f92eef60000000 0xff9ffff80000003f 0xc7ff3ffff0000000

def z1074 : W := mkw 0xffff77b121c80000 0x47fffeef62439000 0xfffffffff1fe007f 0xffffffffffe3fc00

def z1075 : W := mkw 0x4807fddc9213ff7a 0x18900ffbb92427fe 0x0007fff80001ffa0 0xc0000ffff00003ff

def z1076 : W := mkw 0xb5d000036dec0000 0x276ba00006dbd800 0xf9e00007fffe0057 0x3ff3c0000ffffc00

def z1077 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff80007fe7e001f 0x17fff0000ffcfc00

def z1078 : W := mkw 0x4a2f77b004240000 0x40945eef60084800 0x067ffffc0e7e007d 0xd80cfffff81cfc00

def z1079 : W := mkw 0x93f817f925fe0f9e 0x0927f02ff24bfc1f 0x01f807f801fe0790 0x4803f00ff003fc0f

def z1080 : W := mkw 0xffff77b101400000 0x47fffeef62028000 0xffffffff8070003f 0xc7ffffffff00e000

def z1081 : W := mkw 0xc94777b000000000 0x41928eef60000000 0xc067fff800000024 0xc380cffff0000000

def z1082 : W := mkw 0x2c0268025a007060 0x125804d004b400e0 0xfe067807fe01f86f 0xb7fc0cf00ffc03f0

def z1083 : W := mkw 0x0000884fefff9f5a 0x280001109fdfff3e 0x00000007ffffffc0 0x380000000fffffff

def z1084 : W := mkw 0x0a2a52b000000000 0x001454a560000000 0x067ffff80000003d 0xc00cfffff0000000

def z1085 : W := mkw 0x022818d806361e52 0x08045031b00c6c3c 0x0679f9f80e7e3e3d 0x580cf3f3f01cfc7c

def z1086 : W := mkw 0xffff77b121c80000 0x67fffeef62439000 0xfffffff80180003f 0xc7fffffff0030000

def z1087 : W := mkw 0x93f8109925ee0a02 0x2d27f021324bdc14 0x01f8003801fe0010 0x0803f0007003fc00

def z1088 : W := mkw 0x6c07ed46da11f578 0x12d80fda8db423ea 0xfe07f9c7fe01f86f 0xb7fc0ff38ffc03f0

def z1089 : W := mkw 0x4005159000000000 0x00800a2b20000000 0x0007fff800000020 0xc0000ffff0000000

def z1090 : W := mkw 0xffff77b258006000 0x47fffeef64b000c0 0xfffffffffe01f87f 0xf7fffffffffc03f0

def z1091 : W := mkw 0x36b800036dec0000 0x266d700006dbd800 0xfe180007fffe004f 0x3ffc30000ffffc00

def z1092 : W := mkw 0x1090000020880000 0x0021200000411000 0x39984038718e007b 0x7c73308070e31c00

def z1093 : W := mkw 0x0228109000000000 0x0004502120000000 0x0679f9f80000000c 0x000cf3f3f0000000

def z1094 : W := mkw 0xffff77b020880000 0x47fffeef60411000 0xfffffff8718fc7ff 0xfffffffff0e31f8f

def z1095 : W := mkw 0x0000884c02131e52 0x080001109804263c 0x000000040e013e40 0x10000000081c027c

def z1096 : W := mkw 0x3eba72b26cac0000 0x667d74e564d95800 0x3e79f9fc7e7e007d 0x5c7cf3f3f8fcfc00

def z1097 : W := mkw 0xf7fd37b000000000 0x47effa6f60000000 0xc7ffbff800000037 0xc38fff7ff0000000

def z1098 : W := mkw 0xffff77b248000000 0x47fffeef64900000 0xfffffff87e00003f 0xd7fffffff0fc0000

def z1099 : W := mkw 0x6e2f77b000000000 0x46dc5eef60000000 0x0607fff800000020 0xc00c0ffff0000000

def z1100 : W := mkw 0x0000884c02131e50 0x000001109804263c 0x0679f9fc0e7f3e7d 0x580cf3f3f81cfe7c

def z1101 : W := mkw 0x0228884c06371e52 0x08045110980c6e3c 0x061800040e7f3e48 0x180c3000081cfe7c

def z1102 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff80001387f 0xd7fffffff0000270

def z1103 : W := mkw 0x1aba52b030886084 0x003574a5606110c1 0x3ffffff87180c1bf 0xe47ffffff0e30183

def z1104 : W := mkw 0x000017b000000000 0x4000002f60000000 0x0001fff800000020 0x400003fff0000000

def z1105 : W := mkw 0x3eba72b000000000 0x467d74e560000000 0x3e19f9f800000028 0x447c33f3f0000000

def z1106 : W := mkw 0xffff77b181408108 0x47fffeef63028102 0xfffffffb8181c7ff 0xeffffffff703038f

def z1107 : W := mkw 0xffff77b080008000 0x47fffeef61000100 0xfffffffb8000c03f 0xe7fffffff7000180

def z1108 : W := mkw 0x12b8109020880000 0x0025702120411000 0x3ff9f9f8718e007f 0x7c7ff3f3f0e31c00

def z1109 : W := mkw 0x0228109000000000 0x0004502120000000 0x0679f9f80001387d 0x500cf3f3f0000270

def z1110 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x001800040e7f3e59 0x18003000081cfe7c

def z1111 : W := mkw 0xffff77b379c86084 0x67fffeef66f390c1 0xfffffffbf180c1bf 0xe7fffffff7e30183

def z1112 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e787c781f0c796 0xeb83cf0f8f03e18f

def z1113 : W := mkw 0x7c9777b000000000 0x46f92eef60000000 0x3807fff800000020 0xc4700ffff0000000

def z1114 : W := mkw 0xc94777b000000000 0x41928eef60000000 0xc187fff800000022 0xc3830ffff0000000

def z1115 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x399e4638718fffca 0xbc733c8c70e31fff

def z1116 : W := mkw 0x400537b000000000 0x40800a6f60000000 0x0001bff800000000 0x4000037ff0000000

def z1117 : W := mkw 0x93f8109125ec0000 0x2527f021224bd800 0x07f9f9f801fe003d 0x480ff3f3f003fc00

def z1118 : W := mkw 0x2400884e4e371e52 0x0a4801109c9c6e3c 0xfe000007fe7f3e4f 0x3ffc00000ffcfe7c

def z1119 : W := mkw 0xffff77b010006000 0x47fffeef602000c0 0xfffffff87000383f 0xd7fffffff0e00070

def z1120 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfe7ff9f80000002f 0x87fcfff3f0000000

def z1121 : W := mkw 0xffff77b3e9c88108 0x67fffeef67d39102 0xfffffffbf180c1bf 0xe7fffffff7e30183

def z1122 : W := mkw 0x0000884c9213fe72 0x18000110992427fc 0x000000000001fe00 0x00000000000003fc

def z1123 : W := mkw 0x480777b09000e020 0x50900eef612001c0 0x0007fff80000c020 0xc0000ffff0000180

def z1124 : W := mkw 0x7495aa2eea8b9ae4 0x12e92b545dd51735 0xc799be3f8f8e0794 0x4b8f337c7f1f1c0f

def z1125 : W := mkw 0x3eba5aba7eae7ac6 0x2e7d74b574fd5cf5 0x3e1878387e0e3808 0x147c30f070fc1c70

def z1126 : W := mkw 0xef6f77b000000000 0x47dedeef60000000 0xc67ffff80000003d 0xc38cfffff0000000

def z1127 : W := mkw 0xc145854581518518 0x01828b0a8b02a30a 0xc1e787c381f1c7b2 0xeb83cf0f8703e38f

def z1128 : W := mkw 0x6e2f77b000000000 0x42dc5eef60000000 0xfe7ffff80000003f 0xc7fcfffff0000000

def z1129 : W := mkw 0x36b8109000000000 0x066d702120000000 0x3e79f9f80000003d 0x447cf3f3f0000000

def z1130 : W := mkw 0x6c07ed06da01f060 0x12d80fda0db403e0 0xfe07ffc7fe01f86f 0xf7fc0fff8ffc03f0

def z1131 : W := mkw 0x6c07ea26da01f0e4 0x12d80fd44db403e1 0xfe07fe07fe01f9ef 0xb7fc0ffc0ffc03f3

def z1132 : W := mkw 0x36b8884e6ebf1e52 0x2e6d71109cdd7e3c 0x3e1800047e7f3e48 0x1c7c300008fcfe7c

def z1133 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x067ffffc0e7ffffd 0xd80cfffff81cffff

def z1134 : W := mkw 0x8368159000000000 0x4506d02b20000000 0x0679f9f80000003d 0x400cf3f3f0000000

def z1135 : W := mkw 0x480777b000000000 0x40900eef60000000 0x0187fff800000033 0xc0030ffff0000000

def z1136 : W := mkw 0xe76d359000000000 0x47ceda6b20000000 0xc679b9f800000014 0x438cf373f0000000

def z1137 : W := mkw 0x1090884c26bf1e52 0x08212110984d7e3c 0x399800047fff3e5b 0x3c73300008fffe7c

def z1138 : W := mkw 0xf7fd37b36dec0000 0x67effa6f66dbd800 0xfff9bffffffe005f 0x7ffff37ffffffc00

def z1139 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff80180007f 0xeffffffff0030000

def z1140 : W := mkw 0xb7f800024c240000 0x076ff00004984800 0xfff80007fe7e005f 0x3ffff0000ffcfc00

def z1141 : W := mkw 0xb7f817b000000000 0x476ff02f60000000 0xfff9fff80000003f 0x47fff3fff0000000

def z1142 : W := mkw 0xffff77b024ac0000 0x47fffeef60495800 0xfffffffc7ffe007f 0xfffffffff8fffc00

def z1143 : W := mkw 0x0000884c329b7ed6 0x08000110986536fd 0x00000000718fffc0 0x3800000000e31fff

def z1144 : W := mkw 0x6c0777b000000000 0x42d80eef60000000 0x3e07fff800000028 0xc47c0ffff0000000

def z1145 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x000000000e0f3e00 0x10000000001c1e7c

def z1146 : W := mkw 0x0000884ffbdbfffc 0x100001109ff7b7ff 0x00000007ffffffc0 0x380000000fffffff

def z1147 : W := mkw 0x8368159000000000 0x0106d02b20000000 0x07f9fff80000003d 0x400ff3fff0000000

def z1148 : W := mkw 0x0000884c26bf1ed6 0x08000110984d7e3d 0x000000040fff3fc0 0x18000000081ffe7f

def z1149 : W := mkw 0x0228109000000000 0x0004502120000000 0x0679f9fc0e00007d 0x500cf3f3f81c0000

def z1150 : W := mkw 0x7ebf77b000000000 0x46fd7eef60000000 0x3f9ffff80000003b 0xc47f3ffff0000000

def z1151 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfe780007fffe004c 0x3ffcf0000ffffc00

def z1152 : W := mkw 0xffff77b268880000 0x47fffeef64d11000 0xffffffffff8e007f 0xffffffffffff1c00

def z1153 : W := mkw 0xffff77b36dec0000 0x67fffeef66dbd800 0xfffffffffe7e003f 0xd7fffffffffcfc00

def z1154 : W := mkw 0x8140804501510410 0x010281008a02a208 0xc1e787c781f1c7f7 0xeb83cf0f8f03e38f

def z1155 : W := mkw 0x0000884c36bf7ed6 0x08000110986d7efd 0x000000047e7f3e40 0x1800000008fcfe7c

def z1156 : W := mkw 0x6c07ed46da11f578 0x12d80fda8db423ea 0xfe67ffc7fe71ffff 0xfffccfff8ffce3ff

def z1157 : W := mkw 0x0228109000000000 0x0004502120000000 0x0619f9f800000028 0x400c33f3f0000000

def z1158 : W := mkw 0xffff77b125ec0000 0x67fffeef624bd800 0xfffffff871fe007f 0xfffffffff0e3fc00

def z1159 : W := mkw 0x0802422810026a84 0x00100484502004d5 0x000606000001ff80 0x80000c0c000003ff

def z1160 : W := mkw 0x3eba72b000000000 0x467d74e560000000 0x3ffffff80000003f 0xc47ffffff0000000

def z1161 : W := mkw 0xcb6f77b000000000 0x4596deef60000000 0x0067fff800000020 0xc000cffff0000000

def z1162 : W := mkw 0xffff77b248000000 0x47fffeef64900000 0xffffffff8e00003f 0xc7ffffffff1c0000

def z1163 : W := mkw 0xef6f77b000000000 0x47dedeef60000000 0xc7e7fff800000037 0xc38fcffff0000000

def z1164 : W := mkw 0xc94777b101400000 0x41928eef62028000 0xc1e7ffff81f00077 0xeb83cfffff03e000

def z1165 : W := mkw 0x4a2f77b000000000 0x40945eef60000000 0x007ffff800000030 0xc000fffff0000000

def z1166 : W := mkw 0x080272b000000000 0x401004e560000000 0x0001f9f800000020 0x400003f3f0000000

def z1167 : W := mkw 0xffff77b369c80000 0x67fffeef66d39000 0xfffffffbf18e007f 0xfffffffff7e31c00

def z1168 : W := mkw 0x0000109000000000 0x0000002120000000 0x0019f9f800000039 0x400033f3f0000000

def z1169 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x000000040e713e00 0x00000000081ce27c

def z1170 : W := mkw 0xffff77b3f9c8e020 0x77fffeef67f391c0 0xfffffffbf180c03f 0xe7fffffff7e30180

def z1171 : W := mkw 0x6c076802da00f060 0x12d80ed005b401e0 0xfe067803fe01f86b 0xb7fc0cf007fc03f0

def z1172 : W := mkw 0x6c07e84ede37fe72 0x1ad80fd09dbc6ffc 0xf8060007fe7ffe42 0xbff00c000ffcfffc

def z1173 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x3e79f9fc7e7f3e7f 0x7c7cf3f3f8fcfe7c

def z1174 : W := mkw 0xffff77b36dec0000 0x67fffeef66dbd800 0xfe79f9fffe7e000c 0x17fcf3f3fffcfc00

def z1175 : W := mkw 0xc1458d4d87779f5a 0x09828b1a9b0eef3e 0xc18606078fffffc2 0xbb830c0c0f1fffff

def z1176 : W := mkw 0xfffff897ffedf060 0x37fffff12fffdbe0 0xfffff9fffffff87f 0xfffffff3fffffff0

def z1177 : W := mkw 0x0228109000000000 0x0004502120000000 0x07fffff80181c7ff 0xe80ffffff003038f

def z1178 : W := mkw 0x0000884e4e371e52 0x080001109c9c6e3c 0x00000007fe7f3e40 0x380000000ffcfe7c

def z1179 : W := mkw 0x91d000036dec0000 0x2123a00006dbd800 0xf9f80007fffe005f 0x3ff3f0000ffffc00

def z1180 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe01f807fe01386d 0x17fc03f00ffc0270

def z1181 : W := mkw 0xffff70936dec0000 0x27fffee126dbd800 0xfffff9fffffe007f 0xfffffff3fffffc00

def z1182 : W := mkw 0xffff77b349400000 0x67fffeef66928000 0xfffffffb8000003f 0xc7fffffff7000000

def z1183 : W := mkw 0xb7f807236dec0000 0x676ff00e46dbd800 0xfff80607fffe005f 0x3ffff00c0ffffc00

def z1184 : W := mkw 0x0228109000000000 0x0004502120000000 0x0661f9f800000024 0x400cc3f3f0000000

def z1185 : W := mkw 0xc145ad4583519578 0x11828b5a8b06a32a 0xc1e7bfc781f1c7f7 0xeb83cf7f8f03e38f

def z1186 : W := mkw 0xc145054181508518 0x01828a0a8302a10a 0xc1e607c781f0c7d7 0xeb83cc0f8f03e18f

def z1187 : W := mkw 0xe76d37b000000000 0x47ceda6f60000000 0xc661bff800000004 0x438cc37ff0000000

def z1188 : W := mkw 0x080252b000000000 0x001004a560000000 0x0007fff800000020 0xc0000ffff0000000

def z1189 : W := mkw 0xf7fd35936dec0000 0x67effa6b26dbd800 0xfff9f9fffffe007f 0x7ffff3f3fffffc00

def z1190 : W := mkw 0xf7fd159000000000 0x07effa2b20000000 0xfffffff80000003f 0xc7fffffff0000000

def z1191 : W := mkw 0xc94777b181408108 0x41928eef63028102 0xc187fffb8180c1a2 0xe3830ffff7030183

def z1192 : W := mkw 0x0000884e5e377e72 0x180001109cbc6efc 0x000000047e7f3e40 0x1800000008fcfe7c

def z1193 : W := mkw 0xb7f800036dec0000 0x276ff00006dbd800 0xfff80007fffe000e 0x37fff0000ffffc00

def z1194 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe01f807fe01f84c 0x37fc03f00ffc03f0

def z1195 : W := mkw 0xffff77b2d800e020 0x57fffeef65b001c0 0xfffffffbf001f87f 0xf7fffffff7e003f0

def z1196 : W := mkw 0x6c07e846da11f470 0x12d80fd08db423e8 0xfe67f9c7fe71f86f 0xb7fccff38ffce3f0

def z1197 : W := mkw 0xf7fd37b000000000 0x47effa6f60000000 0xc7f9fff80000003d 0x438ff3fff0000000

def z1198 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xf9fffff800000032 0xc7f3fffff0000000

def z1199 : W := mkw 0x0000109000000000 0x0000002120000000 0x0061f9f800000035 0x4000c3f3f0000000

def z1200 : W := mkw 0x422d359000000000 0x40845a6b20000000 0x0679f9f80000003d 0x400cf3f3f0000000

def z1201 : W := mkw 0x0228109004240000 0x0004502120084800 0x0679f9f80e0e003d 0x500cf3f3f01c1c00

def z1202 : W := mkw 0xc1458d4583519558 0x01828b1a8b06a32a 0xc7e7bfc78ff1c7f7 0xeb8fcf7f8f1fe38f

def z1203 : W := mkw 0xc145054181508518 0x01828a0a8302a10a 0xc1e607c381f1c7f3 0xeb83cc0f8703e38f

def z1204 : W := mkw 0xffff77b36dec0000 0x67fffeef66dbd800 0xfffffffbff8e003f 0xf7fffffff7ff1c00

def z1205 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x07f9f9fc0fff3e7f 0x780ff3f3f81ffe7c

def z1206 : W := mkw 0x0228109004240000 0x0004502120084800 0x0679f9f8007e003d 0x480cf3f3f000fc00

def z1207 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff80180c1bf 0xe7fffffff0030183

def z1208 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679f9fc0e7f3e34 0x480cf3f3f81cfe7c

def z1209 : W := mkw 0x2628309000000000 0x464c506120000000 0x0679f9f80000003d 0x400cf3f3f0000000

def z1210 : W := mkw 0x93f812f925fe0e96 0x2d27f025f24bfc1d 0x01f807f801fe0790 0x4803f00ff003fc0f

def z1211 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x000000040e7f3e71 0x58000000081cfe7c

def z1212 : W := mkw 0x0000884db7ffffde 0x080001109b6fffff 0x00000007ffffffc0 0x380000000fffffff

def z1213 : W := mkw 0xb5d0884f6fff1e52 0x2f6ba1109edffe3c 0xf9800007ffff3e42 0x3ff300000ffffe7c

def z1214 : W := mkw 0x6c07e806da01f060 0x12d80fd00db403e0 0xfe067807fe01f84a 0xb7fc0cf00ffc03f0

def z1215 : W := mkw 0x0a2a72b000000000 0x401454e560000000 0x0679f9f80000003d 0x400cf3f3f0000000

def z1216 : W := mkw 0x18924228308a6a84 0x00312484506114d5 0x399e4638718fffb2 0xec733c8c70e31fff

def z1217 : W := mkw 0xffff77b101400108 0x47fffeef62028002 0xfffffff8018001bf 0xc7fffffff0030003

def z1218 : W := mkw 0xb7f8109369c80000 0x276ff02126d39000 0xfff9f9fbf180003f 0x67fff3f3f7e30000

def z1219 : W := mkw 0x4807e8049201f060 0x10900fd0092403e0 0x000600000001f800 0x80000c00000003f0

def z1220 : W := mkw 0x022898dc06371e52 0x08045131b80c6e3c 0x0679f9f80e7f3e38 0x580cf3f3f01cfe7c

def z1221 : W := mkw 0xbffa77b000000000 0x477ff4ef60000000 0x3ff9fff80000003d 0x447ff3fff0000000

def z1222 : W := mkw 0x189252b000000000 0x003124a560000000 0x399ffff80000003b 0xc4733ffff0000000

def z1223 : W := mkw 0xffff77b030886084 0x47fffeef606110c1 0xfffffff8718ec1ff 0xfffffffff0e31d83

def z1224 : W := mkw 0xffff77b101400000 0x47fffeef62028000 0xffffffff81f1c7ff 0xefffffffff03e38f

def z1225 : W := mkw 0x1aba52b000000000 0x003574a560000000 0x3e79f9f80000003d 0x447cf3f3f0000000

def z1226 : W := mkw 0x36b800026cac0000 0x266d700004d95800 0xfe780007fe7e005f 0x3ffcf0000ffcfc00

def z1227 : W := mkw 0x0000884c16377e52 0x08000110982c6efc 0x000000047e7ffe40 0x3800000008fcfffc

def z1228 : W := mkw 0x480777b010006000 0x40900eef602000c0 0x0007fff80001f820 0xc0000ffff00003f0

def z1229 : W := mkw 0x4807ef6c9213fffc 0x10900fded92427ff 0x0007fff80001ffa0 0xc0000ffff00003ff

def z1230 : W := mkw 0x93f8884d27ff1e52 0x2d27f1109a4ffe3c 0x01f800040fff3e50 0x1803f000081ffe7c

def z1231 : W := mkw 0xffff77b258006020 0x57fffeef64b000c0 0xfffffff87000003f 0xc7fffffff0e00000

def z1232 : W := mkw 0x0000884c06371e52 0x08000110980c6e3c 0x060000040e7f3e4d 0x180c0000081cfe7c

def z1233 : W := mkw 0xffff77b125ec0000 0x67fffeef624bd800 0xffffffff81fe007f 0xefffffffff03fc00

def z1234 : W := mkw 0xffff77b369c80000 0x67fffeef66d39000 0xffffffffff80007f 0xf7ffffffffff0000

def z1235 : W := mkw 0xffff77b080008108 0x47fffeef61000102 0xfffffff80000c1bf 0xc7fffffff0000183

def z1236 : W := mkw 0xb7f8884f7fff7ed6 0x2f6ff1109efffefd 0xfff80007ffffffdf 0x3ffff0000fffffff

def z1237 : W := mkw 0x022810936dec0000 0x2004502126dbd800 0x0679f9fffffe007d 0x780cf3f3fffffc00

def z1238 : W := mkw 0xffff77b000000000 0x47fffeef60000000 0xfffffff87000007f 0xf7fffffff0e00000

def z1239 : W := mkw 0xe76d359000000000 0x47ceda6b20000000 0xc661f9f800000024 0x438cc3f3f0000000

def z1240 : W := mkw 0xffff77b36dec0000 0x67fffeef66dbd800 0xffffffff8ffe003f 0xcfffffffff1ffc00

def z1241 : W := mkw 0x0000884ffffffe72 0x380001109ffffffc 0x00000007fffffe40 0x380000000ffffffc

def z1242 : W := mkw 0xb7f8884fefff9f5a 0x2f6ff1109fdfff3e 0xfff80007ffffffdf 0x3ffff0000fffffff

def z1243 : W := mkw 0x0000884fdf77ff7a 0x180001109fbeeffe 0x00000007ffffffc0 0x380000000fffffff

def z1244 : W := mkw 0xffff77b004240000 0x47fffeef60084800 0xfffffff8007e003f 0xcffffffff000fc00

def z1245 : W := mkw 0x93f817b000000000 0x4527f02f60000000 0x01f9fff800000030 0x4003f3fff0000000

def z1246 : W := mkw 0x589777b000000000 0x40b12eef60000000 0x019ffff800000030 0xc0033ffff0000000

def z1247 : W := mkw 0x7ebf77b000000000 0x46fd7eef60000000 0x3e7ffff80000003d 0xc47cfffff0000000

def z1248 : W := mkw 0x480777b080008108 0x40900eef61000102 0x0007fff80000c1a0 0xc0000ffff0000183

def z1249 : W := mkw 0x6e2f7092d800e020 0x12dc5ee125b001c0 0xfe7ff9fbf000c03f 0xe7fcfff3f7e00180

def z1250 : W := mkw 0x6c0777b2d800e020 0x52d80eef65b001c0 0xf807fffbf000c022 0xe7f00ffff7e00180

def z1251 : W := mkw 0xffff77b26cac0000 0x67fffeef64d95800 0xfffffff87f8e007f 0xfffffffff0ff1c00

def z1252 : W := mkw 0xe76d359000000000 0x47ceda6b20000000 0xc679f9f80000000c 0x038cf3f3f0000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z6,z2,z3,z4,z7]),(0,[z0,z1,z2,z8,z4,z9,z7]),(0,[z10,z0,z1,z2,z3,z4,z7]),(0,[z0,z11,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z12,z3,z4,z7]),(0,[z0,z1,z2,z13,z3,z4,z7])],[(0,[z14,z15,z0,z1,z2,z3,z4]),(0,[z0,z16,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z17,z4,z7]),(0,[z18,z0,z1,z2,z3,z4,z7]),(0,[z19,z0,z1,z2,z3,z4,z7])],[(0,[z15,z20,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z21,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z22,z7]),(0,[z23,z0,z1,z2,z3,z24,z7]),(0,[z0,z1,z25,z2,z3,z4,z7]),(0,[z14,z0,z1,z2,z26,z3,z4]),(0,[z27,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z28,z4,z7]),(0,[z0,z1,z29,z2,z3,z4,z7])],[(0,[z30,z0,z1,z2,z3,z4,z31]),(0,[z0,z1,z2,z3,z4,z7,z32]),(0,[z0,z1,z2,z3,z33,z4,z34]),(0,[z35,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z36]),(0,[z0,z1,z37,z2,z38,z3,z4]),(0,[z0,z1,z2,z39,z3,z4,z7]),(0,[z40,z0,z1,z2,z3,z4,z34])],[(0,[z14,z41,z0,z1,z2,z3,z4]),(0,[z42,z0,z1,z43,z2,z3,z4]),(0,[z0,z1,z2,z44,z3,z4,z7]),(0,[z45,z0,z1,z2,z3,z4,z7]),(0,[z46,z0,z1,z2,z3,z4,z34]),(0,[z0,z1,z2,z47,z3,z4,z7])],[(0,[z0,z1,z2,z48,z3,z4,z7]),(0,[z49,z30,z0,z1,z2,z3,z4]),(0,[z30,z0,z1,z2,z3,z50,z4]),(1,[z0,z1,z2,z51,z4,z7]),(0,[z0,z1,z2,z52,z3,z4,z7]),(0,[z0,z1,z2,z53,z3,z4,z7])],[(0,[z54,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z55,z3,z4,z7])]],
   [[(0,[z0,z1,z56,z2,z57,z4,z7]),(0,[z0,z1,z2,z58,z3,z4,z7]),(0,[z0,z59,z1,z2,z3,z4,z34]),(0,[z0,z1,z2,z3,z4,z60,z7]),(0,[z0,z1,z61,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z62]),(0,[z63,z30,z0,z1,z2,z3,z4]),(0,[z40,z14,z0,z1,z2,z3,z4]),(0,[z0,z1,z43,z2,z3,z8,z4]),(0,[z0,z1,z2,z3,z4,z64,z7])],[(0,[z65,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z66,z43,z2,z3,z4]),(1,[z0,z67,z2,z68,z4,z7]),(0,[z0,z69,z1,z2,z3,z4,z34]),(0,[z0,z1,z2,z3,z4,z7,z70])],[(1,[z65,z0,z1,z2,z3,z4]),(1,[z71,z1,z57,z3,z4,z7]),(0,[z0,z72,z1,z73,z3,z4,z7]),(0,[z63,z0,z1,z2,z74,z4,z7]),(0,[z0,z1,z75,z2,z3,z4,z7]),(0,[z76,z0,z1,z2,z3,z4,z7]),(0,[z0,z77,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z34])],[(0,[z0,z1,z2,z3,z4,z78,z7]),(0,[z0,z1,z79,z2,z3,z4,z7]),(0,[z80,z30,z0,z1,z2,z3,z4]),(0,[z14,z0,z1,z2,z3,z8,z4]),(0,[z0,z67,z1,z43,z2,z3,z4]),(0,[z0,z1,z43,z2,z3,z4,z81]),(0,[z0,z1,z82,z2,z3,z4,z81]),(1,[z40,z0,z2,z3,z4,z83]),(0,[z0,z1,z84,z2,z3,z4,z7]),(0,[z0,z1,z2,z85,z3,z4,z7]),(0,[z0,z1,z86,z2,z3,z4,z7])],[(0,[z0,z1,z2,z87,z3,z4,z7]),(0,[z0,z1,z2,z88,z3,z4,z7]),(1,[z0,z1,z89,z2,z3,z4]),(0,[z0,z1,z2,z90,z3,z4,z7]),(1,[z0,z1,z91,z3,z4,z7])],[(0,[z0,z67,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z92,z7]),(0,[z0,z93,z1,z2,z3,z94,z7]),(0,[z0,z1,z95,z2,z3,z4,z7]),(0,[z96,z0,z1,z2,z3,z4,z7])],[(0,[z30,z0,z1,z66,z2,z3,z4]),(0,[z0,z97,z1,z2,z3,z4,z7]),(0,[z14,z0,z1,z2,z3,z4,z81])]],
   [[(0,[z0,z1,z98,z2,z99,z3,z4]),(0,[z0,z100,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z101]),(0,[z0,z1,z2,z3,z4,z7,z102]),(0,[z0,z103,z1,z2,z3,z4,z7])],[(0,[z0,z1,z104,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z105,z4,z7]),(0,[z80,z0,z1,z2,z38,z4,z7]),(0,[z0,z1,z106,z2,z3,z4,z7])],[(1,[z107,z0,z1,z2,z3,z4]),(0,[z41,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z108,z2,z3,z4,z7]),(0,[z23,z0,z1,z2,z3,z4,z34]),(0,[z109,z0,z1,z2,z3,z4,z7]),(0,[z110,z0,z1,z111,z2,z4,z7]),(0,[z0,z1,z112,z2,z3,z4,z7])],[(0,[z0,z1,z113,z2,z3,z4,z7]),(1,[z0,z1,z2,z38,z4,z34]),(0,[z30,z0,z1,z2,z3,z4,z114]),(0,[z115,z0,z1,z2,z3,z4,z7]),(0,[z116,z0,z1,z82,z2,z3,z4])],[(0,[z14,z0,z93,z1,z2,z3,z4]),(0,[z63,z0,z1,z2,z3,z4,z117]),(0,[z118,z0,z1,z2,z3,z4,z7])],[(0,[z30,z0,z1,z2,z3,z4,z119]),(0,[z30,z0,z67,z1,z2,z3,z4]),(0,[z0,z67,z59,z2,z3,z4,z7]),(0,[z63,z0,z93,z2,z3,z4,z7])],[(0,[z0,z1,z120,z2,z3,z4,z7]),(0,[z23,z15,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z57,z3,z4,z34]),(2,[z0,z1,z2,z121,z4]),(0,[z0,z1,z122,z2,z3,z4,z7]),(0,[z0,z1,z123,z75,z3,z4,z7]),(0,[z0,z1,z124,z2,z3,z4,z7]),(0,[z0,z125,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z126,z4,z7]),(0,[z0,z1,z127,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z128,z4,z7])]],
   [[(0,[z42,z0,z1,z2,z3,z24,z7]),(0,[z0,z1,z2,z3,z4,z7,z129]),(0,[z0,z1,z2,z3,z4,z7,z130]),(1,[z0,z1,z131,z95,z2,z7]),(0,[z132,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z133,z4,z7]),(0,[z0,z1,z2,z3,z134,z4,z7]),(0,[z0,z135,z1,z2,z3,z4,z7]),(0,[z0,z1,z136,z2,z3,z4,z7]),(0,[z0,z1,z2,z137,z3,z4,z7]),(0,[z0,z1,z123,z2,z4,z7,z34]),(0,[z0,z1,z138,z2,z3,z4,z7])],[(0,[z0,z139,z1,z2,z3,z4,z34])],[(0,[z0,z20,z1,z2,z3,z4,z7]),(0,[z80,z0,z1,z123,z2,z4,z7]),(0,[z0,z140,z1,z2,z3,z4,z7]),(0,[z141,z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z142,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z143,z7]),(0,[z0,z1,z2,z3,z144,z4,z7]),(1,[z116,z0,z1,z82,z2,z3])],[(0,[z0,z1,z2,z145,z3,z4,z7]),(0,[z146,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z147,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z148])],[(0,[z30,z0,z1,z2,z57,z3,z4]),(0,[z149,z14,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z150,z7]),(0,[z0,z72,z1,z2,z3,z4,z34]),(0,[z40,z0,z69,z2,z3,z4,z7]),(0,[z40,z0,z2,z3,z4,z83,z7]),(1,[z0,z1,z123,z2,z4,z34]),(0,[z0,z1,z151,z43,z2,z3,z4])],[(0,[z0,z59,z1,z2,z3,z4,z152]),(0,[z63,z0,z1,z2,z28,z4,z7]),(0,[z0,z1,z123,z2,z4,z7,z102])],[(0,[z153,z0,z1,z2,z3,z4,z7]),(0,[z0,z154,z1,z2,z3,z4,z7]),(0,[z0,z1,z75,z57,z3,z4,z7]),(0,[z0,z1,z2,z155,z3,z4,z7]),(0,[z156,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z157])]],
   [[(0,[z30,z0,z1,z2,z68,z3,z4]),(0,[z0,z1,z158,z2,z3,z4,z7])],[(1,[z0,z1,z159,z2,z4,z7]),(0,[z0,z1,z2,z3,z4,z160,z7]),(0,[z0,z1,z123,z111,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z161,z7]),(0,[z0,z1,z75,z162,z3,z4,z7])],[(1,[z0,z1,z2,z3,z4,z163]),(0,[z71,z30,z0,z1,z2,z3,z4]),(0,[z164,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z165,z3,z4,z7]),(0,[z18,z0,z1,z2,z3,z4,z34])],[(0,[z30,z0,z1,z2,z166,z3,z4]),(0,[z30,z0,z1,z2,z3,z4,z167]),(0,[z0,z168,z1,z2,z3,z4,z7]),(0,[z0,z1,z169,z2,z3,z170,z7]),(1,[z0,z1,z171,z2,z4,z7]),(0,[z0,z1,z171,z2,z172,z4,z7]),(0,[z0,z1,z173,z2,z3,z4,z7]),(0,[z0,z1,z43,z2,z4,z7,z34])],[(0,[z0,z1,z43,z2,z3,z4,z174]),(0,[z40,z0,z1,z43,z2,z3,z4]),(0,[z175,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z166,z3,z4,z34])],[(0,[z176,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z177,z2,z3,z4,z7]),(0,[z0,z1,z178,z2,z3,z4,z34]),(0,[z0,z179,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z172,z180,z4,z7])],[(0,[z181,z0,z1,z2,z3,z4,z7]),(0,[z182,z0,z1,z2,z3,z4,z7]),(0,[z183,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z184,z2,z3,z4,z7]),(0,[z0,z1,z185,z2,z3,z4,z7]),(0,[z186,z80,z0,z1,z2,z3,z4]),(0,[z14,z0,z1,z187,z2,z3,z4]),(0,[z14,z0,z1,z2,z3,z4,z174]),(0,[z188,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z189,z2,z3,z4,z7])]],
   [[(0,[z42,z0,z1,z2,z3,z4,z34])],[(0,[z14,z0,z1,z66,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z190,z7]),(0,[z191,z0,z1,z2,z3,z4,z7])],[(0,[z23,z1,z66,z2,z3,z4,z7]),(0,[z15,z0,z20,z2,z3,z4,z7]),(0,[z0,z1,z2,z192,z3,z4,z7]),(0,[z0,z193,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z121,z4,z7]),(0,[z0,z1,z194,z2,z3,z4,z7]),(0,[z0,z1,z195,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z196,z7]),(0,[z30,z0,z1,z2,z121,z4,z7]),(0,[z0,z1,z75,z178,z3,z4,z7])],[(1,[z197,z1,z98,z3,z4,z7]),(0,[z30,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z198,z7]),(0,[z0,z1,z2,z3,z4,z7,z199]),(0,[z0,z1,z2,z3,z4,z7,z200]),(0,[z0,z1,z201,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z202,z7])],[(0,[z203,z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z66,z2,z3,z4,z34]),(0,[z42,z14,z0,z1,z2,z3,z4]),(0,[z30,z0,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z172,z3,z4,z83]),(0,[z0,z1,z2,z3,z4,z7,z204]),(0,[z110,z0,z1,z2,z3,z4,z7]),(0,[z110,z0,z1,z43,z2,z4,z7])],[(0,[z71,z0,z1,z205,z3,z4,z7]),(0,[z197,z0,z1,z98,z3,z4,z7]),(0,[z23,z1,z2,z3,z24,z4,z7]),(1,[z0,z1,z2,z3,z206,z4]),(0,[z207,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z208,z7]),(0,[z0,z1,z2,z209,z3,z4,z7])],[(0,[z0,z1,z2,z210,z3,z4,z7]),(0,[z0,z1,z2,z3,z211,z4,z7]),(0,[z0,z67,z1,z2,z3,z4,z34]),(0,[z0,z1,z2,z3,z28,z4,z7]),(0,[z0,z1,z2,z3,z4,z83,z200])]],
   [[(0,[z0,z1,z212,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z213])],[(0,[z0,z1,z214,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z215,z7]),(0,[z0,z1,z2,z3,z4,z7,z216]),(0,[z0,z1,z2,z3,z4,z217,z7]),(0,[z0,z1,z218,z2,z3,z4,z7])],[(0,[z219,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z220,z4,z7]),(0,[z30,z0,z1,z2,z51,z3,z4]),(0,[z0,z1,z221,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z222,z7]),(0,[z0,z1,z2,z3,z4,z7,z223])],[(0,[z224,z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z225,z3,z4,z7]),(0,[z0,z1,z43,z2,z3,z226,z4]),(0,[z0,z1,z2,z3,z227,z4,z7]),(0,[z0,z1,z228,z2,z3,z4,z7])],[(0,[z15,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z43,z2,z57,z3,z4]),(0,[z0,z1,z229,z2,z3,z4,z7]),(0,[z0,z178,z2,z73,z3,z4,z7]),(0,[z0,z230,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z231,z7]),(0,[z0,z1,z2,z205,z3,z4,z157])],[(0,[z15,z1,z2,z3,z4,z31,z7]),(0,[z0,z1,z43,z2,z38,z3,z4]),(0,[z0,z1,z232,z2,z3,z4,z7]),(0,[z0,z1,z233,z2,z3,z4,z7]),(0,[z186,z0,z1,z2,z3,z4,z34])],[(0,[z14,z0,z1,z2,z3,z226,z4]),(0,[z0,z139,z2,z73,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z234,z7]),(0,[z0,z1,z235,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z236,z7]),(0,[z0,z1,z2,z3,z4,z170,z7])],[(0,[z14,z0,z1,z2,z57,z3,z4]),(0,[z0,z1,z123,z43,z2,z3,z4])]],
   [[(0,[z30,z0,z20,z1,z2,z3,z4]),(0,[z30,z197,z0,z1,z2,z3,z4]),(0,[z14,z0,z1,z2,z38,z3,z4]),(0,[z30,z0,z1,z131,z2,z3,z4]),(0,[z0,z1,z2,z237,z3,z4,z7]),(0,[z0,z1,z2,z26,z3,z4,z34]),(0,[z0,z1,z2,z3,z128,z4,z34]),(0,[z238,z0,z1,z43,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z239,z7]),(0,[z0,z1,z98,z2,z3,z4,z7]),(0,[z116,z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z240,z2,z3,z4,z7])],[(0,[z1,z98,z2,z57,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z241,z7]),(0,[z80,z1,z2,z38,z3,z4,z7]),(0,[z186,z14,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z94,z7])],[(0,[z242,z0,z1,z2,z3,z4,z7]),(0,[z243,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z244,z2,z3,z4,z7]),(0,[z0,z245,z1,z2,z3,z4,z7])],[(0,[z30,z0,z139,z1,z2,z3,z4]),(0,[z0,z1,z73,z3,z4,z170,z7]),(0,[z0,z1,z2,z3,z4,z7,z246]),(0,[z0,z1,z247,z2,z3,z4,z7]),(0,[z0,z1,z2,z172,z3,z4,z34]),(0,[z248,z0,z1,z2,z3,z4,z7])],[(1,[z0,z1,z2,z3,z249,z7]),(0,[z0,z1,z250,z2,z3,z4,z7]),(0,[z0,z1,z251,z2,z3,z4,z7])],[(0,[z0,z1,z2,z252,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z253]),(0,[z30,z0,z1,z2,z3,z4,z83]),(0,[z0,z1,z2,z3,z4,z254,z7]),(0,[z0,z1,z169,z3,z4,z170,z7]),(0,[z0,z1,z2,z255,z3,z4,z7])],[(0,[z197,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z68,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z256,z7]),(0,[z0,z1,z131,z2,z3,z4,z7]),(0,[z0,z257,z1,z43,z2,z3,z4]),(0,[z0,z1,z2,z3,z258,z4,z7])]],
   [[(1,[z0,z1,z2,z121,z4,z7])],[(1,[z0,z1,z2,z3,z4,z7]),(0,[z20,z1,z66,z2,z3,z4,z7]),(0,[z0,z259,z1,z2,z3,z4,z7]),(1,[z164,z1,z2,z3,z4,z7]),(0,[z0,z1,z43,z260,z2,z3,z4])],[(0,[z0,z261,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z262,z7]),(0,[z0,z1,z162,z3,z4,z170,z7])],[(0,[z23,z0,z1,z2,z3,z31,z7]),(0,[z0,z1,z2,z3,z8,z4,z34]),(0,[z263,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z43,z2,z3,z4,z7]),(0,[z0,z264,z1,z2,z3,z4,z7]),(0,[z0,z1,z82,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z50,z4,z7]),(0,[z0,z1,z265,z2,z3,z4,z7]),(1,[z0,z69,z2,z3,z4,z81]),(0,[z0,z266,z1,z2,z3,z4,z7]),(0,[z0,z1,z43,z2,z3,z4,z9]),(0,[z0,z1,z267,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z268,z7]),(0,[z0,z269,z1,z2,z3,z4,z7]),(0,[z14,z23,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z270,z7]),(0,[z0,z1,z2,z3,z271,z4,z7]),(0,[z0,z1,z272,z2,z3,z4,z7]),(0,[z0,z1,z273,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z274,z4,z7])],[(0,[z275,z14,z0,z1,z2,z3,z4]),(0,[z0,z1,z276,z2,z3,z4,z7])],[(0,[z0,z1,z277,z2,z3,z4,z7]),(0,[z0,z1,z278,z2,z3,z4,z7]),(0,[z30,z0,z1,z178,z2,z3,z4]),(0,[z30,z0,z1,z75,z2,z3,z4]),(0,[z14,z0,z1,z2,z3,z4,z9]),(0,[z0,z1,z279,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z280,z7]),(0,[z0,z1,z281,z2,z3,z4,z7]),(0,[z0,z1,z2,z38,z3,z4,z34]),(0,[z0,z1,z2,z282,z3,z4,z7]),(0,[z0,z1,z283,z2,z3,z4,z7])],[(0,[z284,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z162,z3,z31,z7]),(0,[z30,z0,z1,z2,z3,z121,z4]),(0,[z30,z0,z59,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z285,z7]),(0,[z0,z1,z2,z3,z4,z286,z7]),(0,[z0,z1,z2,z287,z3,z4,z7]),(0,[z288,z0,z1,z2,z3,z4,z7]),(0,[z289,z0,z1,z2,z3,z4,z7])],[(0,[z15,z0,z66,z2,z3,z4,z7]),(0,[z0,z1,z2,z290,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z291]),(0,[z292,z0,z1,z2,z3,z4,z7]),(0,[z0,z293,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z24,z170,z7]),(0,[z0,z294,z1,z2,z3,z4,z7]),(0,[z0,z295,z1,z2,z3,z4,z7]),(0,[z0,z1,z296,z2,z3,z4,z7])],[(0,[z297,z0,z1,z2,z3,z4,z7]),(0,[z0,z139,z1,z73,z3,z4,z7]),(0,[z0,z1,z298,z2,z3,z4,z7]),(0,[z0,z1,z2,z299,z3,z4,z7])],[(0,[z0,z1,z2,z300,z3,z4,z7]),(0,[z40,z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z301,z3,z4,z7]),(0,[z0,z1,z2,z302,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z303]),(0,[z0,z1,z75,z43,z2,z3,z4])],[(0,[z0,z0,z1,z2,z3,z4,z7]),(0,[z238,z80,z0,z1,z2,z3,z4]),(0,[z304,z30,z0,z1,z2,z3,z4]),(0,[z14,z0,z1,z169,z2,z3,z4]),(0,[z0,z1,z79,z43,z2,z3,z4]),(0,[z0,z1,z84,z43,z2,z3,z4])],[(0,[z0,z1,z305,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z31,z7]),(0,[z0,z1,z2,z3,z4,z306,z7]),(0,[z0,z1,z2,z3,z307,z4,z7]),(0,[z110,z0,z1,z2,z3,z4,z34]),(1,[z0,z1,z2,z3,z128,z114]),(0,[z0,z1,z2,z3,z4,z308,z7])],[(0,[z0,z1,z2,z3,z4,z309,z7]),(0,[z0,z1,z2,z3,z310,z4,z34]),(0,[z0,z1,z43,z2,z3,z310,z4]),(0,[z0,z1,z2,z3,z4,z7,z311]),(0,[z0,z312,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z313,z7]),(0,[z0,z1,z2,z3,z4,z314,z7]),(0,[z315,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z166,z4,z9,z7]),(0,[z0,z1,z95,z43,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z34,z114])]],
   [[(0,[z316,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z83,z34]),(0,[z0,z1,z2,z317,z3,z4,z7]),(0,[z0,z103,z1,z43,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z318,z7]),(0,[z14,z0,z1,z2,z3,z310,z4]),(0,[z0,z1,z319,z2,z3,z4,z7]),(0,[z30,z0,z1,z111,z2,z3,z4]),(0,[z0,z1,z2,z3,z320,z4,z7])],[(0,[z197,z0,z1,z57,z3,z4,z7]),(0,[z41,z0,z1,z43,z2,z3,z4]),(0,[z110,z14,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z81,z200]),(0,[z321,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z123,z2,z205,z4,z7]),(0,[z0,z1,z2,z322,z3,z4,z7]),(0,[z0,z1,z75,z2,z162,z3,z7])],[(1,[z0,z1,z323,z2,z3,z4]),(0,[z0,z1,z2,z73,z3,z4,z34]),(0,[z0,z1,z2,z3,z4,z324,z7]),(0,[z0,z1,z325,z2,z3,z4,z7])],[(0,[z15,z0,z1,z2,z3,z4,z34]),(0,[z0,z1,z37,z2,z3,z4,z7]),(0,[z0,z1,z82,z2,z3,z4,z83]),(0,[z0,z1,z2,z3,z326,z4,z7]),(0,[z0,z1,z327,z2,z3,z4,z7])],[(0,[z328,z0,z1,z2,z3,z4,z7]),(0,[z14,z0,z139,z1,z2,z3,z4]),(0,[z329,z0,z1,z2,z3,z4,z7]),(0,[z330,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z205,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z331,z7])],[(0,[z0,z1,z332,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z333,z4,z7]),(0,[z0,z59,z1,z2,z68,z4,z7]),(1,[z0,z1,z2,z334,z3,z4]),(0,[z0,z1,z2,z3,z4,z34,z335]),(0,[z0,z1,z2,z336,z3,z4,z7])]],
   [[(0,[z0,z1,z56,z2,z3,z4,z7]),(0,[z1,z2,z38,z3,z310,z4,z7]),(0,[z0,z59,z1,z2,z8,z4,z7]),(0,[z0,z2,z3,z226,z4,z94,z7]),(0,[z0,z1,z2,z337,z3,z4,z7]),(0,[z0,z1,z111,z2,z4,z7,z34])],[(0,[z30,z0,z1,z98,z2,z3,z4]),(0,[z0,z1,z2,z338,z3,z4,z7]),(0,[z42,z0,z1,z305,z3,z4,z7]),(0,[z0,z1,z178,z3,z4,z170,z7])],[(0,[z49,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z123,z2,z3,z4,z34])],[(0,[z0,z1,z339,z2,z3,z4,z7]),(0,[z340,z0,z1,z2,z3,z4,z7]),(0,[z0,z341,z1,z2,z3,z4,z7]),(0,[z0,z1,z82,z2,z3,z7,z114])],[(0,[z0,z20,z1,z43,z2,z3,z4]),(0,[z0,z1,z2,z342,z3,z4,z7]),(0,[z343,z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z344,z2,z3,z4,z7]),(0,[z345,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z346,z2,z3,z4,z7]),(0,[z243,z0,z1,z2,z3,z4,z34]),(0,[z0,z1,z347,z2,z3,z4,z7])],[(0,[z0,z1,z43,z2,z3,z4,z31]),(0,[z0,z1,z75,z73,z3,z4,z7]),(0,[z63,z164,z1,z2,z3,z4,z7]),(0,[z63,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z111,z2,z4,z7,z102])],[(1,[z203,z66,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z121,z4]),(0,[z0,z1,z2,z3,z4,z348,z7]),(0,[z175,z0,z1,z172,z3,z4,z7]),(0,[z0,z1,z251,z2,z3,z4,z34])],[(1,[z0,z1,z2,z3,z105,z7]),(0,[z30,z0,z1,z2,z3,z4,z170]),(0,[z30,z0,z1,z2,z3,z128,z4]),(0,[z0,z1,z2,z3,z4,z34,z167])]],
   [[(0,[z197,z0,z1,z2,z3,z4,z34]),(0,[z14,z0,z1,z2,z3,z4,z31]),(0,[z14,z0,z1,z2,z3,z349,z4]),(0,[z0,z1,z131,z2,z3,z4,z34])],[(0,[z107,z0,z1,z2,z57,z3,z4]),(0,[z0,z1,z98,z2,z3,z4,z350]),(0,[z0,z1,z2,z3,z351,z4,z7]),(0,[z14,z0,z1,z75,z2,z3,z4]),(0,[z0,z352,z1,z2,z3,z4,z7])],[(1,[z0,z1,z2,z3,z4,z353]),(0,[z0,z1,z2,z3,z4,z117,z7]),(0,[z0,z1,z354,z2,z3,z4,z7])],[(0,[z0,z1,z355,z2,z3,z4,z7]),(0,[z80,z0,z1,z2,z310,z4,z7]),(0,[z356,z14,z0,z1,z2,z3,z4]),(0,[z14,z0,z59,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z357,z4,z7]),(0,[z0,z69,z2,z3,z4,z7,z81]),(0,[z0,z1,z2,z3,z4,z7,z358]),(0,[z0,z1,z169,z2,z3,z4,z7])],[(0,[z0,z1,z2,z359,z3,z4,z7]),(0,[z360,z0,z1,z2,z3,z4,z7]),(0,[z0,z361,z1,z2,z3,z4,z7]),(0,[z0,z139,z1,z2,z3,z4,z348]),(0,[z0,z362,z1,z2,z3,z4,z7])],[(0,[z71,z0,z1,z98,z3,z4,z7]),(1,[z0,z1,z2,z310,z4,z34]),(0,[z30,z0,z72,z1,z2,z3,z4]),(0,[z175,z0,z1,z43,z2,z3,z4]),(0,[z110,z0,z1,z2,z26,z4,z7]),(0,[z0,z1,z363,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z5,z7]),(1,[z0,z1,z75,z162,z3,z7]),(0,[z175,z0,z1,z364,z3,z4,z7]),(0,[z176,z0,z1,z43,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z7,z365]),(0,[z0,z1,z2,z3,z4,z174,z7]),(0,[z0,z1,z2,z3,z366,z4,z7]),(1,[z367,z1,z2,z3,z4,z7])]],
   [[(1,[z0,z1,z120,z2,z3,z4]),(0,[z0,z1,z2,z3,z368,z4,z7]),(0,[z369,z0,z1,z2,z3,z4,z7]),(0,[z30,z0,z1,z2,z3,z4,z94]),(0,[z0,z1,z2,z370,z3,z4,z7])],[(1,[z0,z1,z2,z3,z4,z350]),(0,[z30,z0,z1,z364,z2,z3,z4]),(0,[z0,z1,z371,z2,z3,z4,z7]),(0,[z40,z0,z1,z2,z3,z4,z81]),(0,[z0,z1,z43,z111,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z372,z7])],[(0,[z0,z373,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z91,z3,z4,z7])],[(0,[z41,z0,z1,z2,z3,z4,z374]),(0,[z0,z1,z2,z3,z4,z7,z375]),(0,[z376,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z377,z3,z4,z7])],[(0,[z378,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z379,z3,z4]),(0,[z0,z1,z2,z380,z3,z4,z7]),(0,[z14,z0,z1,z2,z381,z3,z4]),(0,[z14,z0,z1,z111,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z382,z7]),(0,[z0,z1,z364,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z383,z7])],[(0,[z0,z1,z2,z3,z384,z4,z7]),(1,[z41,z1,z2,z310,z4,z7]),(0,[z0,z1,z385,z2,z3,z4,z7]),(0,[z0,z1,z323,z2,z3,z24,z4]),(0,[z30,z0,z1,z43,z2,z3,z4]),(0,[z0,z1,z43,z2,z3,z4,z114])],[(0,[z0,z1,z2,z3,z386,z310,z4]),(0,[z30,z0,z1,z2,z3,z4,z200]),(0,[z0,z1,z2,z3,z4,z387,z7]),(0,[z388,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z389]),(0,[z110,z0,z1,z43,z2,z3,z4])],[(0,[z0,z69,z1,z2,z3,z4,z81]),(0,[z0,z1,z75,z2,z3,z4,z34])]],
   [[(0,[z0,z1,z43,z98,z2,z3,z4]),(0,[z42,z23,z1,z2,z3,z4,z7]),(0,[z42,z30,z0,z1,z2,z3,z4]),(0,[z14,z0,z1,z2,z3,z4,z114]),(0,[z0,z1,z2,z3,z4,z7,z81]),(0,[z0,z390,z1,z2,z3,z4,z7]),(0,[z116,z0,z1,z2,z3,z128,z7])],[(0,[z0,z1,z2,z391,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z392,z7]),(0,[z0,z393,z1,z2,z3,z4,z7]),(0,[z0,z394,z1,z2,z3,z4,z7]),(0,[z0,z1,z131,z2,z3,z4,z148]),(0,[z0,z1,z2,z395,z3,z4,z7])],[(0,[z71,z197,z1,z2,z3,z4,z7]),(0,[z396,z0,z1,z2,z3,z4,z7]),(0,[z71,z0,z1,z2,z3,z249,z7]),(0,[z14,z0,z67,z1,z2,z3,z4]),(0,[z0,z1,z95,z2,z3,z4,z34])],[(0,[z14,z0,z1,z98,z2,z3,z4]),(0,[z14,z0,z1,z2,z301,z3,z4]),(1,[z0,z1,z2,z3,z4,z148])],[(0,[z0,z1,z2,z3,z4,z7,z397]),(0,[z0,z1,z2,z3,z4,z398,z7]),(0,[z116,z0,z1,z2,z3,z4,z114])],[(0,[z15,z0,z1,z43,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z399,z7]),(0,[z0,z1,z21,z3,z310,z4,z7]),(0,[z400,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z401]),(0,[z402,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z403,z2,z3,z4,z7])],[(0,[z0,z1,z404,z2,z3,z4,z7]),(0,[z71,z0,z1,z2,z3,z4,z7]),(0,[z41,z0,z1,z2,z3,z4,z34]),(0,[z405,z30,z0,z1,z2,z3,z4]),(0,[z14,z0,z1,z2,z3,z206,z4]),(0,[z0,z1,z43,z2,z3,z4,z170]),(0,[z406,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z43,z2,z3,z128,z4]),(0,[z0,z1,z82,z2,z3,z128,z4])],[(0,[z203,z0,z20,z2,z3,z4,z7]),(0,[z0,z407,z1,z2,z3,z4,z7]),(0,[z0,z1,z205,z3,z4,z7,z102]),(0,[z0,z1,z2,z205,z3,z4,z34]),(0,[z408,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z409,z4,z7])]],
   [[(0,[z0,z1,z410,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z152]),(0,[z0,z1,z111,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z180,z4,z7])],[(0,[z14,z0,z1,z2,z3,z4,z170]),(0,[z0,z1,z2,z3,z411,z4,z7]),(0,[z0,z1,z43,z201,z2,z3,z4])],[(0,[z0,z1,z2,z412,z3,z4,z7]),(0,[z0,z1,z43,z2,z68,z3,z4]),(0,[z413,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z414,z4,z7]),(0,[z0,z125,z1,z2,z3,z4,z34])],[(0,[z415,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z416,z7])],[(0,[z30,z0,z69,z1,z2,z3,z4]),(0,[z0,z1,z2,z417,z3,z4,z7]),(0,[z0,z1,z123,z2,z3,z4,z204])],[(0,[z30,z1,z2,z3,z4,z7,z167]),(0,[z0,z1,z43,z2,z3,z4,z167]),(0,[z14,z0,z1,z2,z68,z3,z4]),(0,[z0,z2,z68,z3,z8,z4,z7]),(0,[z0,z1,z43,z2,z166,z3,z4])],[(0,[z0,z1,z2,z418,z3,z4,z7]),(0,[z63,z0,z1,z2,z3,z4,z34]),(0,[z0,z419,z1,z2,z3,z4,z7])],[(0,[z0,z20,z1,z2,z3,z4,z34]),(0,[z42,z0,z1,z338,z3,z4,z7]),(0,[z30,z0,z0,z1,z2,z3,z4]),(0,[z14,z0,z72,z1,z2,z3,z4]),(0,[z0,z67,z1,z2,z8,z4,z7]),(0,[z0,z1,z420,z2,z3,z4,z7]),(0,[z0,z1,z421,z2,z3,z4,z7])]],
   [[(0,[z422,z0,z1,z2,z3,z4,z7]),(0,[z197,z0,z1,z43,z2,z3,z4]),(0,[z41,z0,z1,z2,z38,z4,z7]),(0,[z0,z1,z2,z3,z4,z5,z31]),(0,[z14,z0,z1,z2,z3,z4,z167]),(0,[z14,z0,z1,z2,z166,z3,z4]),(1,[z0,z1,z2,z3,z4,z423]),(0,[z0,z424,z1,z2,z3,z4,z7]),(0,[z0,z93,z2,z3,z226,z4,z7]),(0,[z0,z1,z43,z364,z2,z3,z4]),(0,[z0,z1,z131,z43,z2,z3,z4])],[(0,[z203,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z159,z2,z57,z4,z7]),(0,[z0,z1,z2,z3,z425,z4,z7]),(0,[z0,z1,z2,z426,z3,z4,z7]),(0,[z0,z1,z427,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z34,z32])],[(0,[z0,z1,z428,z2,z3,z4,z7]),(1,[z0,z1,z43,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z429,z7])],[(0,[z0,z1,z2,z3,z4,z119,z7]),(0,[z63,z14,z0,z1,z2,z3,z4]),(0,[z14,z0,z1,z364,z2,z3,z4]),(0,[z63,z367,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z430,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z431]),(0,[z0,z432,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z433,z7]),(0,[z0,z1,z2,z3,z4,z7,z434]),(0,[z0,z435,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z204]),(0,[z436,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z43,z43,z2,z3,z4]),(0,[z0,z1,z43,z2,z3,z3,z4]),(0,[z0,z1,z82,z43,z2,z3,z4])],[(0,[z30,z0,z1,z437,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z438,z7]),(0,[z439,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z440,z3,z4,z7]),(0,[z0,z1,z441,z2,z3,z4,z7]),(0,[z0,z1,z2,z442,z3,z4,z7])],[(0,[z443,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z374,z7]),(1,[z0,z1,z111,z205,z4,z7]),(0,[z0,z1,z2,z3,z4,z444,z7]),(0,[z0,z1,z273,z43,z2,z3,z4])],[(0,[z224,z0,z1,z2,z3,z4,z7]),(0,[z30,z0,z1,z2,z205,z3,z4]),(1,[z0,z1,z169,z3,z170,z7]),(0,[z0,z1,z2,z3,z4,z7,z445])]],
   [[(0,[z0,z1,z2,z3,z4,z7,z163]),(0,[z0,z1,z2,z3,z4,z446,z7]),(0,[z80,z0,z1,z111,z2,z4,z7]),(0,[z153,z14,z0,z1,z2,z3,z4]),(0,[z0,z1,z447,z2,z3,z4,z7]),(0,[z0,z1,z75,z2,z3,z170,z7]),(0,[z175,z0,z1,z2,z3,z4,z34]),(0,[z0,z1,z2,z3,z4,z34,z70])],[(0,[z0,z1,z448,z2,z3,z4,z7]),(1,[z30,z0,z1,z2,z51,z4]),(0,[z14,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z34,z34]),(0,[z176,z0,z1,z2,z3,z4,z34])],[(0,[z71,z0,z1,z57,z3,z4,z7]),(0,[z41,z0,z1,z123,z2,z4,z7]),(0,[z449,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z111,z2,z4,z34])],[(0,[z0,z1,z450,z2,z3,z4,z7]),(0,[z0,z1,z2,z381,z3,z4,z7]),(0,[z451,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z43,z2,z452,z3,z4])],[(0,[z0,z453,z1,z2,z3,z4,z7]),(0,[z0,z454,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z99,z3,z4,z7]),(0,[z0,z1,z455,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z456,z4,z7]),(0,[z0,z1,z2,z457,z3,z4,z7]),(0,[z175,z0,z1,z2,z172,z3,z4])],[(0,[z458,z0,z1,z2,z3,z4,z7]),(0,[z30,z0,z1,z2,z3,z24,z4]),(0,[z175,z14,z0,z1,z2,z3,z4]),(1,[z0,z139,z73,z3,z4,z7]),(0,[z0,z93,z1,z2,z3,z4,z7]),(0,[z0,z1,z459,z2,z3,z4,z7]),(0,[z0,z460,z1,z2,z3,z4,z7]),(0,[z116,z0,z1,z2,z3,z4,z7])],[(0,[z461,z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z462,z4,z7]),(0,[z176,z14,z0,z1,z2,z3,z4]),(0,[z463,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z34,z102]),(0,[z0,z1,z2,z3,z4,z464,z7]),(1,[z0,z1,z2,z180,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z465]),(0,[z466,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z467,z2,z3,z4,z7]),(0,[z468,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z3,z4,z34])]],
   [[(0,[z0,z1,z469,z2,z3,z4,z7]),(1,[z14,z30,z1,z2,z3,z4]),(0,[z30,z0,z1,z2,z3,z4,z34]),(0,[z0,z1,z2,z470,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z471,z7]),(1,[z415,z0,z1,z2,z3,z4])],[(1,[z30,z1,z2,z3,z4,z167])],[(0,[z0,z472,z1,z2,z3,z4,z7]),(0,[z473,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z474]),(0,[z0,z1,z2,z3,z475,z4,z7]),(0,[z0,z1,z111,z2,z205,z4,z7])],[(0,[z0,z139,z1,z2,z3,z4,z434]),(0,[z0,z1,z2,z3,z4,z7,z476]),(0,[z0,z1,z477,z2,z3,z4,z7]),(0,[z0,z478,z1,z2,z3,z4,z7])],[(0,[z0,z1,z278,z3,z310,z4,z7]),(0,[z30,z0,z1,z2,z172,z3,z4]),(0,[z0,z1,z2,z479,z3,z4,z7])],[(0,[z14,z0,z20,z1,z2,z3,z4]),(0,[z14,z197,z0,z1,z2,z3,z4]),(0,[z30,z0,z1,z2,z3,z4,z102]),(0,[z14,z0,z1,z131,z2,z3,z4]),(0,[z0,z1,z2,z3,z480,z4,z7]),(0,[z0,z1,z481,z2,z3,z4,z7]),(0,[z482,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z483,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z484,z7]),(0,[z485,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z486,z7]),(0,[z110,z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z487,z3,z4,z7]),(1,[z0,z1,z477,z3,z4,z7])],[(0,[z203,z0,z66,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z488,z7]),(0,[z0,z1,z43,z2,z47,z3,z4])]],
   [[(0,[z0,z1,z43,z2,z3,z4,z83])],[(0,[z0,z1,z2,z3,z4,z489,z7]),(0,[z0,z490,z1,z2,z3,z4,z7]),(0,[z0,z1,z437,z2,z3,z4,z7]),(0,[z14,z0,z0,z1,z2,z3,z4]),(1,[z0,z93,z2,z3,z226,z7]),(0,[z0,z1,z111,z2,z3,z4,z34])],[(1,[z0,z1,z2,z3,z4,z374]),(0,[z491,z0,z1,z2,z3,z4,z7]),(0,[z0,z67,z2,z68,z3,z4,z7]),(0,[z0,z1,z492,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z170,z34])],[(0,[z110,z0,z1,z2,z38,z4,z7]),(0,[z14,z0,z1,z2,z3,z4,z83]),(0,[z0,z1,z493,z2,z3,z4,z7])],[(0,[z42,z0,z1,z2,z3,z31,z7]),(0,[z0,z1,z2,z3,z31,z170,z7]),(0,[z0,z1,z494,z2,z3,z4,z7]),(0,[z63,z0,z1,z2,z3,z4,z423])],[(0,[z0,z1,z98,z2,z3,z4,z34]),(0,[z0,z1,z205,z3,z4,z170,z7]),(0,[z0,z1,z95,z2,z4,z9,z7])],[(0,[z0,z1,z2,z2,z3,z4,z7]),(0,[z63,z0,z1,z43,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z94,z34]),(0,[z0,z1,z2,z495,z3,z4,z7])],[(1,[z15,z20,z2,z3,z4,z7]),(0,[z496,z0,z1,z2,z3,z4,z7]),(0,[z0,z59,z1,z2,z3,z4,z497]),(0,[z0,z1,z2,z3,z4,z498,z7]),(0,[z0,z1,z2,z3,z4,z7,z499]),(0,[z0,z1,z2,z3,z33,z4,z7])]],
   [[(0,[z500,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z501,z2,z3,z4,z7]),(0,[z0,z1,z2,z502,z3,z4,z7]),(0,[z0,z1,z2,z3,z503,z4,z7]),(0,[z248,z0,z1,z2,z3,z4,z34]),(0,[z0,z504,z1,z2,z3,z4,z7])],[(0,[z80,z0,z1,z43,z2,z3,z4]),(0,[z0,z1,z43,z178,z2,z3,z4]),(0,[z0,z1,z2,z172,z3,z4,z81]),(0,[z505,z0,z1,z2,z3,z4,z7])],[(0,[z203,z0,z1,z2,z3,z4,z34]),(0,[z506,z0,z1,z2,z3,z4,z7]),(0,[z485,z0,z1,z2,z3,z310,z4]),(0,[z0,z1,z2,z3,z507,z4,z7]),(0,[z0,z1,z2,z3,z508,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z497])],[(0,[z509,z0,z1,z2,z3,z4,z7]),(0,[z80,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z510,z3,z4,z7]),(0,[z511,z0,z1,z2,z3,z4,z31]),(0,[z238,z30,z0,z1,z2,z3,z4]),(0,[z14,z1,z2,z3,z4,z174,z7]),(0,[z0,z1,z2,z68,z3,z4,z34]),(0,[z0,z1,z512,z2,z3,z4,z7]),(0,[z0,z1,z354,z43,z2,z3,z4])],[(0,[z14,z0,z1,z178,z2,z3,z4]),(0,[z0,z59,z1,z2,z3,z4,z7]),(0,[z0,z1,z169,z43,z2,z3,z4])],[(1,[z0,z1,z21,z3,z4,z7]),(0,[z0,z1,z2,z3,z386,z4,z7]),(0,[z30,z0,z1,z2,z26,z3,z4]),(0,[z1,z2,z3,z4,z174,z7,z167]),(0,[z110,z0,z1,z123,z2,z4,z7]),(1,[z0,z1,z2,z3,z4,z34]),(1,[z0,z1,z43,z2,z4,z34]),(0,[z0,z1,z513,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z226,z4,z7]),(0,[z0,z69,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z442,z3,z4,z34]),(0,[z0,z514,z1,z2,z3,z4,z7])],[(0,[z203,z14,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z7]),(0,[z0,z1,z2,z3,z515,z4,z7]),(0,[z0,z1,z2,z3,z4,z516,z7]),(0,[z0,z1,z131,z95,z2,z3,z7]),(0,[z0,z1,z43,z2,z3,z4,z34]),(0,[z0,z1,z82,z2,z3,z4,z34])]],
   [[(0,[z517,z0,z1,z2,z3,z4,z7]),(0,[z518,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z519,z7])],[(0,[z41,z0,z1,z2,z3,z4,z253]),(0,[z520,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z521,z3,z4,z7]),(0,[z175,z0,z1,z2,z3,z4,z200])],[(0,[z522,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z523,z2,z3,z4,z7]),(1,[z14,z0,z1,z2,z3,z4]),(0,[z14,z0,z1,z2,z3,z4,z34]),(0,[z524,z0,z1,z2,z3,z4,z7]),(0,[z0,z525,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z101]),(0,[z0,z1,z2,z3,z4,z34,z200]),(0,[z0,z1,z2,z3,z4,z526,z7])],[(0,[z0,z1,z2,z3,z24,z4,z353]),(0,[z30,z0,z1,z2,z73,z3,z4]),(0,[z0,z1,z123,z3,z4,z7,z102]),(0,[z0,z527,z1,z2,z3,z4,z7]),(0,[z0,z1,z169,z2,z162,z3,z7]),(0,[z0,z528,z1,z2,z3,z4,z7]),(0,[z0,z1,z43,z2,z172,z3,z4]),(0,[z0,z1,z529,z2,z3,z4,z7])],[(0,[z530,z0,z1,z2,z3,z4,z7]),(0,[z0,z531,z1,z2,z3,z4,z7]),(0,[z0,z1,z43,z2,z3,z4,z102]),(0,[z0,z1,z2,z3,z4,z532,z7])],[(0,[z0,z533,z1,z2,z3,z4,z7]),(0,[z0,z2,z3,z4,z83,z7,z81]),(0,[z0,z1,z2,z3,z4,z534,z7]),(1,[z0,z1,z512,z2,z3,z4])],[(0,[z23,z0,z1,z2,z3,z4,z7]),(0,[z14,z0,z1,z2,z172,z3,z4]),(0,[z0,z93,z1,z2,z3,z4,z34]),(0,[z0,z1,z2,z3,z4,z535,z7]),(0,[z0,z1,z364,z2,z3,z4,z200]),(0,[z0,z1,z2,z3,z4,z536,z7])],[(0,[z30,z0,z1,z2,z3,z8,z4]),(0,[z14,z14,z0,z1,z2,z3,z4]),(0,[z0,z1,z537,z2,z3,z4,z7]),(0,[z0,z1,z2,z166,z3,z4,z213]),(0,[z0,z1,z2,z334,z166,z3,z4])]],
   [[(0,[z343,z0,z1,z2,z3,z4,z7]),(0,[z41,z1,z2,z3,z310,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z538]),(0,[z0,z1,z2,z539,z3,z4,z7]),(0,[z0,z1,z2,z3,z540,z4,z7]),(0,[z0,z1,z2,z3,z4,z541,z7])],[(0,[z0,z1,z2,z542,z3,z4,z7]),(0,[z0,z543,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z38,z3,z4,z397])],[(0,[z0,z1,z2,z57,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z31,z34]),(0,[z141,z0,z1,z2,z3,z4,z7]),(0,[z30,z0,z1,z2,z3,z4,z81]),(0,[z30,z0,z1,z82,z2,z3,z4]),(0,[z0,z544,z1,z2,z3,z4,z7]),(0,[z0,z1,z545,z2,z3,z4,z7]),(0,[z63,z0,z1,z477,z3,z4,z7]),(0,[z0,z393,z1,z43,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z546,z7])],[(0,[z0,z1,z1,z2,z3,z4,z7]),(0,[z107,z0,z1,z2,z3,z4,z7]),(0,[z0,z547,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z548,z3,z4,z7]),(0,[z292,z14,z0,z1,z2,z3,z4]),(0,[z0,z549,z1,z2,z3,z4,z7])],[(0,[z149,z0,z1,z2,z3,z4,z7]),(0,[z197,z0,z1,z205,z3,z4,z7]),(0,[z0,z1,z2,z550,z3,z4,z7]),(0,[z0,z1,z2,z162,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z551,z7]),(0,[z0,z1,z2,z26,z4,z7,z34])],[(0,[z0,z1,z2,z3,z4,z249,z7]),(0,[z0,z1,z2,z379,z57,z3,z4]),(0,[z0,z1,z2,z552,z3,z4,z7]),(0,[z0,z1,z2,z3,z553,z4,z7]),(0,[z466,z14,z0,z1,z2,z3,z4]),(0,[z14,z0,z294,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z554,z4,z7]),(0,[z0,z555,z1,z2,z3,z4,z7])],[(0,[z30,z0,z1,z25,z2,z3,z4]),(0,[z0,z139,z1,z2,z3,z4,z7]),(0,[z0,z367,z1,z2,z3,z4,z7]),(0,[z0,z1,z556,z2,z3,z4,z7]),(0,[z0,z1,z131,z95,z2,z4,z7]),(0,[z402,z0,z1,z43,z2,z3,z4])],[(0,[z557,z0,z1,z2,z3,z4,z7]),(0,[z71,z0,z1,z43,z2,z3,z4])]],
   [[(0,[z0,z69,z1,z2,z3,z4,z83]),(0,[z558,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z334,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z4,z7]),(0,[z0,z72,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z559,z7]),(0,[z560,z0,z1,z2,z3,z4,z7]),(0,[z197,z0,z1,z123,z3,z4,z7]),(0,[z63,z0,z1,z2,z3,z226,z7]),(0,[z0,z1,z2,z3,z4,z9,z7])],[(0,[z0,z561,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z562,z7]),(0,[z563,z0,z1,z2,z3,z4,z7]),(0,[z564,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z565,z2,z3,z4,z7]),(0,[z14,z0,z1,z2,z3,z128,z4]),(0,[z0,z1,z566,z2,z3,z4,z7]),(0,[z0,z1,z43,z2,z26,z3,z4]),(0,[z415,z0,z1,z43,z2,z3,z4])],[(0,[z0,z1,z2,z567,z3,z4,z7])],[(0,[z41,z30,z0,z1,z2,z3,z4]),(0,[z0,z568,z1,z2,z3,z4,z7]),(0,[z569,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z570]),(0,[z0,z1,z260,z2,z3,z4,z7])]],
   [[(0,[z571,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z572,z4,z7]),(0,[z0,z1,z2,z166,z3,z4,z7]),(0,[z0,z1,z131,z2,z3,z4,z573])],[(1,[z511,z0,z1,z2,z3,z4]),(0,[z0,z1,z178,z2,z3,z4,z7]),(0,[z0,z67,z1,z2,z68,z4,z7]),(0,[z0,z574,z1,z2,z3,z4,z7]),(0,[z575,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z576,z3,z4,z7]),(1,[z175,z0,z1,z172,z3,z4]),(0,[z0,z1,z2,z166,z3,z9,z7]),(1,[z46,z0,z1,z2,z3,z4])],[(0,[z203,z0,z1,z43,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z577]),(0,[z0,z1,z43,z2,z73,z3,z4]),(0,[z0,z1,z2,z3,z4,z578,z7]),(0,[z0,z1,z43,z2,z3,z4,z94]),(0,[z0,z1,z579,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z573])],[(0,[z0,z1,z2,z3,z580,z4,z7]),(0,[z0,z1,z2,z581,z3,z4,z7]),(0,[z0,z1,z582,z2,z3,z4,z7]),(0,[z0,z1,z2,z51,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z152,z7]),(0,[z0,z1,z75,z205,z3,z4,z7]),(0,[z116,z0,z1,z82,z2,z3,z7])],[(0,[z0,z1,z2,z379,z3,z4,z7]),(1,[z238,z0,z1,z2,z3,z4]),(0,[z80,z0,z1,z2,z3,z4,z34]),(0,[z0,z1,z2,z38,z4,z7,z34]),(0,[z42,z0,z1,z2,z3,z4,z7]),(0,[z30,z0,z1,z2,z162,z3,z4]),(0,[z0,z583,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z584,z7]),(0,[z0,z1,z585,z2,z3,z4,z7]),(0,[z0,z1,z172,z3,z4,z7,z200])],[(0,[z0,z1,z2,z586,z3,z4,z7]),(0,[z42,z1,z2,z3,z4,z31,z7]),(0,[z0,z1,z2,z162,z3,z24,z7]),(0,[z0,z1,z2,z587,z3,z4,z7]),(0,[z14,z0,z1,z2,z73,z3,z4]),(0,[z14,z0,z1,z2,z3,z4,z94]),(0,[z0,z588,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z589,z4,z7]),(0,[z0,z1,z2,z3,z4,z590,z7]),(1,[z0,z1,z364,z3,z4,z200])],[(0,[z591,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z592,z3,z4,z7]),(0,[z14,z0,z1,z2,z3,z4,z433]),(0,[z0,z72,z178,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z226,z4,z34]),(0,[z593,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z169,z2,z3,z4,z34]),(0,[z0,z1,z594,z2,z3,z4,z7])]],
   [[(0,[z595,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z353]),(0,[z63,z0,z1,z302,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z157]),(0,[z0,z1,z43,z2,z3,z4,z200])],[(0,[z0,z1,z66,z2,z3,z4,z7]),(0,[z0,z1,z323,z2,z3,z4,z7]),(1,[z30,z0,z1,z2,z121,z4])],[(0,[z405,z0,z1,z2,z3,z4,z7]),(0,[z30,z0,z1,z2,z3,z4,z174]),(0,[z14,z0,z1,z43,z2,z3,z4]),(0,[z0,z1,z2,z3,z596,z4,z7]),(0,[z0,z1,z2,z3,z597,z4,z7])],[(0,[z0,z1,z2,z3,z4,z598,z7]),(1,[z0,z1,z2,z3,z4,z397]),(0,[z14,z0,z1,z2,z3,z4,z200]),(0,[z0,z1,z2,z3,z4,z174,z34]),(0,[z599,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z600,z7]),(0,[z0,z1,z2,z3,z4,z601,z7])],[(0,[z80,z41,z1,z2,z3,z4,z7]),(0,[z511,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z602,z7]),(0,[z14,z0,z1,z82,z2,z3,z4]),(0,[z0,z1,z603,z2,z3,z4,z7]),(0,[z0,z1,z2,z604,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z605,z7])],[(0,[z0,z1,z2,z3,z24,z4,z7]),(0,[z360,z14,z0,z1,z2,z3,z4]),(0,[z606,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z607,z2,z3,z4,z7]),(0,[z0,z1,z2,z452,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z608,z7]),(0,[z609,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z68,z4,z9,z7]),(0,[z0,z93,z1,z43,z2,z3,z4]),(0,[z116,z0,z1,z43,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z610,z7]),(0,[z0,z1,z2,z3,z4,z7,z350])]],
   [[(0,[z0,z1,z611,z2,z3,z4,z7]),(0,[z175,z30,z0,z1,z2,z3,z4]),(0,[z0,z59,z2,z3,z8,z4,z7]),(0,[z0,z1,z2,z612,z3,z4,z7]),(0,[z0,z1,z364,z2,z3,z4,z34])],[(0,[z613,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z159,z2,z3,z4,z7]),(0,[z0,z1,z98,z3,z4,z170,z7]),(0,[z186,z0,z1,z2,z3,z4,z7]),(0,[z176,z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z614,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z615,z7]),(0,[z0,z1,z123,z3,z4,z170,z7]),(0,[z616,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z541,z34]),(0,[z0,z1,z2,z3,z4,z7,z114])],[(1,[z0,z1,z56,z2,z4,z7]),(0,[z0,z1,z617,z2,z3,z4,z7]),(0,[z41,z0,z1,z2,z310,z4,z7])],[(0,[z618,z0,z1,z2,z3,z4,z7]),(0,[z619,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z620,z3,z4,z7]),(0,[z0,z1,z621,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z83,z114]),(0,[z0,z1,z75,z169,z3,z4,z7]),(0,[z0,z1,z2,z3,z622,z4,z7]),(0,[z0,z1,z364,z2,z172,z3,z4]),(0,[z0,z1,z2,z26,z3,z4,z7])],[(0,[z0,z20,z1,z2,z3,z4,z446]),(1,[z0,z1,z2,z99,z3,z4]),(0,[z0,z1,z187,z2,z3,z4,z7]),(0,[z0,z1,z2,z623,z3,z4,z7]),(0,[z0,z1,z624,z2,z3,z4,z7]),(0,[z0,z1,z2,z162,z3,z4,z34])],[(1,[z186,z0,z1,z2,z3,z4]),(1,[z0,z1,z305,z3,z4,z7]),(0,[z0,z625,z1,z2,z3,z4,z7]),(0,[z0,z139,z1,z178,z3,z4,z7]),(0,[z0,z1,z2,z626,z3,z4,z7])],[(0,[z71,z0,z1,z2,z3,z105,z7]),(0,[z627,z0,z1,z2,z3,z4,z7]),(0,[z628,z0,z1,z2,z3,z4,z7]),(1,[z63,z0,z2,z3,z94,z7]),(0,[z0,z1,z2,z629,z3,z4,z7])]],
   [[(0,[z1,z66,z2,z3,z4,z31,z7]),(1,[z0,z1,z2,z3,z4,z253]),(0,[z0,z1,z2,z3,z4,z7,z630]),(0,[z30,z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z631,z2,z3,z4,z7]),(0,[z0,z1,z2,z172,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z573,z7]),(0,[z0,z1,z2,z632,z3,z4,z7])],[(0,[z0,z1,z2,z3,z633,z4,z7]),(0,[z30,z0,z1,z2,z3,z226,z4]),(0,[z14,z0,z69,z1,z2,z3,z4]),(0,[z0,z139,z72,z2,z3,z4,z7]),(0,[z634,z0,z1,z2,z3,z4,z7]),(0,[z0,z72,z1,z178,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z335]),(0,[z635,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z213]),(0,[z0,z1,z403,z2,z3,z4,z34])],[(0,[z71,z0,z1,z2,z3,z4,z34]),(0,[z0,z1,z2,z3,z4,z636,z7]),(0,[z0,z1,z95,z91,z3,z4,z7])],[(0,[z71,z1,z2,z57,z3,z4,z7]),(0,[z30,z0,z1,z2,z38,z3,z4]),(1,[z0,z1,z2,z3,z4,z434]),(0,[z637,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z638,z4,z7]),(0,[z0,z1,z2,z639,z3,z4,z7]),(0,[z0,z1,z43,z2,z162,z3,z4]),(0,[z0,z1,z2,z3,z4,z9,z34])],[(0,[z640,z0,z1,z2,z3,z4,z7]),(1,[z42,z1,z2,z3,z31,z7]),(0,[z0,z1,z151,z2,z3,z4,z7]),(0,[z641,z0,z1,z2,z3,z4,z7])],[(0,[z0,z642,z1,z2,z3,z4,z7]),(0,[z275,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z643,z7]),(0,[z0,z1,z123,z2,z3,z4,z64]),(0,[z0,z1,z2,z3,z4,z644,z7]),(1,[z0,z1,z2,z26,z4,z34])],[(0,[z645,z0,z1,z2,z3,z4,z7]),(0,[z14,z0,z1,z2,z162,z3,z4]),(0,[z63,z0,z1,z2,z3,z94,z7]),(0,[z646,z0,z1,z2,z3,z4,z7])],[(0,[z71,z14,z0,z1,z2,z3,z4]),(0,[z14,z80,z0,z1,z2,z3,z4]),(0,[z30,z0,z432,z1,z2,z3,z4]),(0,[z0,z1,z647,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z8,z4,z7])]],
   [[(1,[z0,z1,z2,z3,z386,z4])],[(0,[z0,z1,z2,z3,z4,z7,z167]),(0,[z0,z1,z43,z2,z205,z3,z4])],[(0,[z0,z1,z648,z2,z3,z4,z7]),(0,[z461,z0,z1,z2,z3,z4,z7]),(0,[z14,z30,z1,z2,z3,z4,z7])],[(0,[z0,z1,z649,z2,z3,z4,z7]),(0,[z0,z1,z650,z2,z3,z4,z7]),(0,[z40,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z651,z2,z3,z4,z7])],[(0,[z304,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z38,z3,z4,z7]),(0,[z30,z0,z1,z95,z2,z3,z4]),(0,[z14,z0,z1,z2,z205,z3,z4]),(0,[z63,z0,z2,z3,z4,z94,z7]),(0,[z0,z1,z652,z2,z3,z4,z7]),(1,[z0,z1,z123,z4,z7,z102]),(0,[z46,z0,z1,z2,z3,z4,z7])],[(0,[z30,z0,z1,z123,z2,z3,z4]),(0,[z0,z59,z1,z43,z2,z3,z4]),(1,[z0,z1,z2,z3,z4,z64]),(0,[z653,z0,z1,z2,z3,z4,z7])],[(0,[z14,z0,z1,z649,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z423]),(0,[z654,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z655,z3,z4,z7]),(0,[z0,z1,z2,z656,z3,z4,z7])],[(0,[z30,z15,z0,z1,z2,z3,z4]),(0,[z0,z1,z43,z2,z3,z24,z4]),(0,[z0,z1,z2,z74,z3,z4,z7]),(0,[z0,z69,z1,z43,z2,z3,z4]),(0,[z657,z0,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z658,z3,z4,z7]),(0,[z197,z1,z98,z2,z3,z4,z7]),(0,[z30,z23,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z659,z3,z4,z7]),(0,[z660,z0,z1,z2,z3,z4,z7])],[(0,[z203,z15,z1,z2,z3,z4,z7]),(0,[z0,z1,z661,z2,z3,z4,z7]),(0,[z662,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z310,z4,z7,z34]),(0,[z0,z1,z2,z3,z4,z7,z663]),(0,[z0,z1,z2,z3,z4,z34,z375])],[(1,[z0,z1,z37,z2,z3,z4]),(0,[z14,z0,z1,z2,z3,z24,z4]),(0,[z0,z1,z664,z2,z3,z4,z7]),(0,[z0,z93,z1,z2,z3,z226,z7])],[(0,[z0,z1,z2,z3,z310,z4,z7]),(0,[z0,z1,z2,z68,z3,z4,z101]),(0,[z0,z665,z1,z2,z3,z4,z7]),(0,[z0,z666,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z667,z3,z4,z7]),(0,[z0,z1,z2,z3,z206,z4,z7]),(0,[z668,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z669,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z128,z7,z114])],[(0,[z65,z0,z1,z66,z2,z3,z4]),(0,[z110,z0,z1,z2,z310,z4,z7]),(0,[z1,z2,z3,z24,z4,z31,z7]),(1,[z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z89,z2,z68,z3,z4]),(0,[z0,z1,z670,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z83,z7]),(0,[z0,z1,z111,z205,z3,z4,z7]),(0,[z0,z1,z2,z3,z671,z4,z7]),(0,[z0,z672,z1,z2,z3,z4,z7])],[(0,[z0,z1,z673,z2,z3,z4,z7]),(0,[z0,z1,z2,z674,z3,z4,z7]),(0,[z675,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z278,z3,z4,z7]),(0,[z0,z1,z2,z3,z24,z4,z34]),(0,[z0,z1,z2,z3,z4,z34,z81]),(0,[z0,z1,z2,z3,z676,z4,z7]),(0,[z0,z1,z43,z2,z3,z4,z546]),(0,[z0,z1,z2,z677,z3,z4,z7])],[(0,[z23,z0,z1,z43,z2,z3,z4]),(1,[z0,z1,z2,z3,z4,z348]),(1,[z0,z1,z302,z3,z4,z7]),(1,[z0,z1,z2,z74,z4,z7]),(0,[z0,z1,z678,z2,z3,z4,z7])]],
   [[(0,[z30,z0,z1,z169,z2,z3,z4]),(0,[z0,z1,z2,z73,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z679,z7])],[(0,[z0,z1,z2,z3,z680,z4,z7]),(0,[z71,z0,z1,z123,z3,z4,z7]),(0,[z0,z1,z57,z3,z4,z170,z7]),(0,[z30,z0,z1,z2,z51,z4,z7]),(0,[z0,z681,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z682,z3,z4,z7]),(0,[z116,z0,z1,z2,z3,z4,z34])],[(0,[z0,z1,z2,z3,z683,z4,z7]),(0,[z0,z1,z2,z684,z3,z4,z7]),(0,[z14,z30,z0,z1,z2,z3,z4]),(0,[z30,z0,z1,z2,z587,z3,z4]),(0,[z14,z0,z1,z2,z3,z4,z102]),(0,[z685,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z131,z2,z68,z4,z7]),(0,[z0,z1,z2,z686,z3,z4,z7])],[(0,[z0,z1,z131,z2,z8,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z687]),(0,[z0,z1,z2,z688,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z471,z34])],[(0,[z0,z689,z1,z2,z3,z4,z7]),(0,[z30,z0,z1,z2,z3,z310,z4]),(1,[z80,z1,z2,z38,z4,z7]),(1,[z14,z1,z2,z3,z4,z174]),(0,[z690,z0,z1,z2,z3,z4,z7]),(0,[z40,z0,z1,z2,z3,z4,z83]),(0,[z0,z1,z131,z2,z166,z4,z7])],[(0,[z0,z1,z691,z2,z3,z4,z7]),(0,[z116,z14,z0,z1,z2,z3,z4]),(0,[z0,z1,z123,z2,z3,z4,z7]),(1,[z0,z1,z428,z3,z4,z7])],[(0,[z41,z0,z1,z111,z2,z4,z7]),(0,[z238,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z692,z3,z4,z7]),(0,[z0,z139,z1,z43,z2,z3,z4]),(0,[z0,z1,z2,z693,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z694,z7])]],
   [[(0,[z0,z1,z2,z695,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z117]),(0,[z0,z1,z2,z3,z4,z81,z114]),(0,[z0,z696,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z697,z7]),(0,[z0,z1,z95,z2,z166,z3,z7]),(1,[z0,z1,z2,z166,z9,z7])],[(0,[z0,z1,z120,z66,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z698]),(0,[z0,z1,z2,z699,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z497]),(0,[z0,z1,z89,z2,z3,z4,z7])],[(0,[z356,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z75,z98,z3,z4,z7]),(0,[z30,z0,z93,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z700,z7]),(0,[z0,z72,z1,z43,z2,z3,z4]),(0,[z0,z701,z1,z2,z3,z4,z7]),(0,[z0,z1,z364,z3,z4,z7,z200])],[(1,[z0,z1,z2,z3,z4,z446]),(0,[z702,z0,z1,z2,z3,z4,z7])],[(0,[z0,z20,z1,z2,z3,z4,z163]),(1,[z0,z1,z338,z3,z4,z7]),(1,[z0,z59,z2,z8,z4,z7]),(0,[z0,z703,z1,z2,z3,z4,z7]),(0,[z0,z1,z171,z2,z3,z4,z7]),(0,[z0,z1,z428,z95,z3,z4,z7]),(1,[z110,z0,z1,z43,z2,z4])],[(0,[z203,z1,z66,z2,z3,z4,z7]),(1,[z485,z0,z1,z2,z3,z4]),(0,[z0,z1,z131,z2,z3,z9,z7])],[(1,[z23,z1,z2,z3,z24,z7]),(0,[z14,z0,z1,z95,z2,z3,z4]),(0,[z0,z1,z512,z2,z205,z3,z4]),(0,[z0,z257,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z128,z4,z114])],[(0,[z0,z1,z2,z3,z704,z4,z7]),(0,[z14,z0,z1,z123,z2,z3,z4]),(0,[z0,z1,z2,z3,z349,z4,z7]),(0,[z0,z705,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z706,z7])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z707]),(0,[z0,z1,z113,z3,z170,z7]),(0,[z23,z0,z1,z2,z121,z4]),(0,[z0,z1,z2,z3,z4,z708]),(0,[z0,z1,z2,z3,z4,z709]),(0,[z0,z1,z710,z3,z4,z34]),(0,[z0,z1,z43,z711,z2,z4])],[(0,[z0,z712,z2,z3,z4,z7]),(0,[z71,z107,z1,z57,z3,z4]),(0,[z186,z0,z1,z2,z38,z4]),(0,[z0,z1,z43,z305,z3,z4]),(0,[z0,z1,z2,z3,z4,z713]),(0,[z0,z1,z123,z2,z4,z34])],[(0,[z0,z1,z2,z3,z4,z714]),(0,[z715,z66,z2,z3,z4,z7]),(0,[z41,z1,z2,z716,z4,z7]),(0,[z482,z1,z2,z38,z4,z7]),(0,[z415,z1,z2,z3,z4,z174]),(0,[z0,z1,z2,z3,z4,z434]),(0,[z0,z717,z1,z2,z3,z4]),(0,[z0,z1,z718,z2,z28,z4]),(0,[z0,z1,z2,z3,z4,z719])],[(0,[z0,z1,z720,z3,z4,z7]),(0,[z458,z0,z1,z123,z4,z7]),(1,[z46,z1,z2,z310,z4]),(0,[z0,z1,z2,z386,z4,z34]),(0,[z186,z46,z1,z2,z3,z4]),(0,[z42,z1,z2,z3,z31,z7]),(0,[z23,z1,z2,z3,z24,z353]),(0,[z30,z0,z139,z73,z3,z4]),(0,[z14,z0,z67,z2,z68,z4]),(0,[z0,z1,z721,z2,z4,z7]),(0,[z722,z164,z1,z2,z3,z4])],[(0,[z0,z294,z2,z3,z4,z81])],[(0,[z0,z1,z2,z3,z4,z723]),(0,[z0,z1,z2,z3,z4,z724]),(0,[z0,z1,z159,z2,z4,z7]),(0,[z30,z0,z1,z21,z3,z4]),(0,[z0,z1,z725,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z726]),(0,[z141,z0,z1,z2,z3,z50]),(0,[z0,z1,z2,z121,z4,z174]),(0,[z0,z1,z2,z515,z4,z34]),(0,[z0,z1,z2,z3,z4,z727])],[(0,[z0,z1,z2,z3,z4,z163]),(0,[z0,z1,z728,z2,z3,z4]),(0,[z197,z1,z43,z98,z3,z4]),(0,[z176,z0,z1,z2,z121,z4]),(0,[z0,z1,z325,z43,z2,z4])],[(0,[z15,z20,z43,z2,z3,z4]),(0,[z0,z1,z2,z51,z121,z4])]],
   [[(0,[z0,z1,z729,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z730]),(0,[z0,z1,z169,z2,z121,z4]),(0,[z0,z1,z2,z3,z4,z731]),(0,[z0,z125,z2,z3,z4,z335])],[(0,[z0,z732,z1,z2,z3,z4]),(0,[z0,z1,z733,z3,z4,z7]),(0,[z0,z1,z734,z3,z4,z7]),(0,[z156,z0,z1,z43,z2,z4])],[(0,[z71,z30,z1,z57,z3,z4]),(0,[z71,z0,z1,z2,z121,z4]),(0,[z0,z1,z735,z3,z4,z7]),(0,[z0,z1,z2,z587,z121,z4]),(0,[z14,z0,z1,z2,z28,z4])],[(0,[z0,z1,z2,z736,z4,z7]),(0,[z0,z1,z2,z3,z4,z737]),(0,[z0,z1,z2,z3,z4,z738]),(0,[z739,z1,z2,z3,z4,z7])],[(0,[z740,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z741])],[(0,[z0,z1,z2,z742,z4,z7]),(0,[z0,z1,z2,z3,z4,z743]),(0,[z0,z1,z2,z121,z4,z119]),(0,[z0,z1,z123,z326,z4,z7])],[(0,[z0,z1,z2,z3,z4,z744]),(0,[z30,z0,z1,z2,z3,z249]),(0,[z0,z1,z2,z3,z4,z745]),(1,[z0,z1,z2,z121,z4]),(0,[z0,z1,z2,z3,z746,z7]),(0,[z0,z1,z2,z540,z4,z34]),(0,[z747,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z166,z9,z213])],[(0,[z748,z0,z1,z2,z3,z4]),(0,[z0,z749,z2,z3,z4,z7])]],
   [[(0,[z30,z197,z1,z98,z3,z4])],[(0,[z0,z1,z159,z75,z4,z7]),(0,[z0,z1,z410,z3,z170,z7]),(0,[z0,z139,z1,z2,z121,z4]),(0,[z750,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z751,z4,z7])],[(0,[z0,z1,z2,z3,z4,z752]),(0,[z186,z80,z1,z2,z38,z4]),(0,[z0,z93,z1,z2,z121,z4]),(0,[z0,z1,z79,z2,z121,z4]),(0,[z0,z666,z2,z68,z4,z7]),(0,[z0,z1,z302,z3,z4,z423])],[(0,[z0,z1,z753,z2,z4,z7]),(0,[z0,z1,z2,z553,z4,z34]),(0,[z14,z1,z2,z3,z4,z754])],[(0,[z42,z1,z2,z3,z746,z7]),(0,[z0,z1,z2,z121,z226,z4]),(0,[z0,z1,z755,z2,z3,z4])],[(0,[z0,z1,z278,z3,z4,z7]),(0,[z485,z0,z1,z21,z3,z4]),(0,[z14,z0,z1,z338,z3,z4]),(0,[z63,z30,z0,z2,z3,z94]),(0,[z0,z1,z2,z3,z4,z756]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1,z758,z2,z3,z4]),(0,[z0,z1,z354,z2,z4,z34])],[(0,[z0,z1,z2,z3,z4,z759]),(0,[z0,z1,z2,z121,z760,z4]),(0,[z0,z1,z2,z74,z4,z7]),(0,[z164,z1,z2,z74,z4,z7]),(0,[z0,z1,z2,z3,z4,z761]),(0,[z0,z1,z762,z2,z3,z4]),(0,[z0,z1,z43,z763,z3,z4])],[(1,[z0,z1,z2,z764,z4]),(0,[z0,z432,z2,z3,z4,z83]),(0,[z1,z2,z3,z4,z174,z754]),(0,[z0,z1,z123,z43,z4,z102]),(0,[z765,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z159,z43,z2,z4]),(0,[z0,z1,z2,z548,z4,z34]),(0,[z0,z1,z111,z403,z4,z34])],[(0,[z0,z1,z2,z300,z4,z34]),(0,[z0,z1,z501,z3,z170,z7])],[(0,[z0,z1,z56,z2,z4,z34]),(0,[z0,z1,z2,z766,z3,z4]),(0,[z0,z1,z43,z2,z180,z4])],[(0,[z0,z767,z2,z3,z4,z7]),(0,[z0,z1,z768,z3,z4,z7]),(0,[z0,z1,z2,z769,z4,z7]),(0,[z63,z367,z2,z3,z94,z7]),(0,[z0,z1,z111,z442,z4,z34])],[(0,[z0,z1,z205,z3,z249,z7]),(0,[z0,z1,z2,z3,z4,z770]),(0,[z0,z1,z75,z2,z121,z4]),(0,[z14,z1,z2,z3,z4,z174]),(0,[z0,z1,z354,z172,z3,z4]),(0,[z0,z1,z771,z2,z3,z4])],[(0,[z0,z1,z772,z2,z3,z4]),(0,[z0,z1,z428,z3,z4,z7])],[(0,[z0,z1,z2,z3,z773,z7]),(0,[z0,z1,z2,z774,z3,z4]),(0,[z0,z1,z159,z2,z4,z775]),(0,[z0,z1,z305,z3,z4,z34]),(0,[z0,z1,z2,z776,z121,z4]),(0,[z30,z1,z651,z2,z3,z4]),(0,[z14,z0,z1,z123,z4,z102]),(0,[z0,z1,z2,z3,z4,z777])],[(0,[z0,z1,z778,z56,z2,z4]),(0,[z42,z511,z1,z2,z3,z31]),(0,[z0,z1,z2,z779,z3,z4]),(0,[z0,z139,z73,z3,z4,z348]),(0,[z164,z1,z2,z3,z4,z117]),(0,[z0,z1,z2,z3,z4,z117]),(0,[z63,z0,z2,z3,z94,z34]),(0,[z0,z1,z2,z166,z9,z7])]],
   [[(0,[z14,z0,z1,z428,z3,z4]),(0,[z0,z1,z2,z3,z4,z497]),(0,[z0,z1,z123,z299,z4,z7]),(0,[z0,z1,z2,z3,z4,z780])],[(0,[z0,z1,z2,z3,z4,z781]),(0,[z71,z1,z782,z3,z4,z7]),(0,[z110,z0,z1,z278,z4,z7]),(0,[z0,z1,z278,z43,z3,z4]),(0,[z0,z1,z111,z290,z4,z7]),(0,[z783,z0,z1,z2,z3,z4]),(0,[z304,z0,z1,z2,z121,z4]),(0,[z0,z1,z477,z3,z4,z34]),(0,[z0,z1,z2,z3,z4,z784]),(0,[z0,z1,z2,z785,z4,z7]),(1,[z0,z1,z2,z786,z7])],[(0,[z0,z1,z2,z3,z4,z446]),(0,[z203,z65,z66,z2,z3,z4]),(0,[z0,z787,z2,z3,z4,z7]),(0,[z0,z1,z788,z2,z3,z4]),(0,[z0,z1,z2,z425,z4,z34]),(0,[z1,z2,z3,z4,z789,z34]),(0,[z0,z1,z43,z790,z3,z4])],[(0,[z0,z1,z791,z3,z4,z7]),(0,[z0,z1,z338,z3,z4,z7]),(0,[z1,z2,z38,z310,z4,z34]),(0,[z0,z59,z2,z8,z4,z7]),(0,[z0,z1,z2,z623,z9,z7]),(0,[z0,z1,z2,z589,z4,z34]),(0,[z110,z0,z1,z43,z2,z4])],[(0,[z0,z1,z2,z792,z4,z7]),(0,[z42,z1,z2,z3,z31,z34]),(0,[z793,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z7]),(1,[z1,z782,z3,z4,z7]),(0,[z30,z0,z1,z278,z3,z4]),(0,[z23,z1,z2,z3,z24,z7]),(0,[z0,z1,z2,z121,z4,z9]),(0,[z14,z0,z1,z75,z162,z3]),(0,[z0,z1,z2,z794,z4,z7]),(0,[z0,z1,z2,z28,z4,z784]),(0,[z0,z1,z228,z3,z170,z7])],[(0,[z0,z1,z725,z3,z4,z34])],[(0,[z0,z1,z2,z592,z4,z34]),(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z795,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z796,z7]),(0,[z14,z41,z1,z2,z310,z4]),(0,[z0,z1,z21,z3,z386,z4]),(0,[z30,z1,z2,z3,z4,z644]),(0,[z797,z1,z2,z3,z4,z7]),(0,[z0,z69,z2,z3,z4,z81]),(0,[z175,z0,z1,z442,z3,z4])],[(0,[z613,z1,z2,z3,z31,z7]),(0,[z0,z1,z2,z3,z4,z798]),(0,[z0,z2,z3,z4,z799,z7]),(0,[z0,z1,z2,z3,z800,z4]),(0,[z0,z1,z2,z3,z4,z801]),(0,[z14,z0,z1,z305,z3,z4]),(0,[z0,z1,z802,z3,z4,z7]),(0,[z0,z1,z2,z28,z4,z7]),(0,[z164,z1,z2,z28,z4,z7]),(0,[z0,z1,z803,z2,z3,z4]),(0,[z0,z1,z428,z43,z3,z4])],[(0,[z15,z20,z2,z3,z4,z34]),(0,[z14,z0,z1,z2,z51,z4]),(0,[z14,z0,z1,z169,z3,z170]),(0,[z0,z1,z123,z4,z64,z102]),(0,[z0,z1,z2,z3,z4,z804]),(0,[z0,z1,z734,z3,z4,z34])],[(0,[z0,z1,z2,z3,z805,z7]),(0,[z41,z1,z2,z310,z4,z253]),(0,[z116,z0,z1,z2,z121,z4]),(0,[z0,z1,z111,z2,z4,z157])],[(0,[z63,z0,z1,z2,z121,z4]),(0,[z0,z1,z2,z3,z806,z4]),(0,[z243,z0,z2,z3,z4,z541])],[(0,[z0,z1,z2,z3,z807,z4]),(0,[z0,z1,z778,z2,z3,z4]),(0,[z415,z1,z2,z3,z310,z4]),(0,[z0,z67,z1,z2,z121,z4]),(0,[z0,z1,z364,z587,z3,z4]),(0,[z110,z0,z1,z2,z121,z4]),(0,[z0,z1,z2,z3,z4,z808]),(0,[z0,z1,z2,z809,z4,z7])],[(1,[z715,z2,z3,z4,z7]),(0,[z71,z1,z57,z3,z249,z7]),(0,[z0,z1,z2,z810,z4,z7]),(0,[z0,z1,z98,z2,z121,z4]),(0,[z42,z30,z1,z2,z3,z31]),(0,[z0,z1,z2,z334,z166,z9]),(0,[z0,z1,z43,z2,z4,z202])],[(0,[z0,z1,z811,z2,z4,z7]),(0,[z0,z1,z2,z3,z812,z7]),(0,[z0,z1,z2,z3,z813,z4]),(0,[z46,z0,z1,z2,z38,z4]),(0,[z0,z1,z2,z3,z4,z814]),(0,[z1,z2,z3,z4,z815,z7]),(0,[z0,z1,z2,z3,z4,z816])]],
   [[(0,[z0,z1,z2,z3,z817,z7]),(0,[z0,z1,z2,z121,z310,z4]),(0,[z0,z1,z2,z786,z166,z7])],[(0,[z0,z1,z2,z818,z4,z7]),(0,[z0,z1,z819,z3,z4,z7]),(0,[z0,z1,z2,z820,z121,z4]),(0,[z30,z367,z1,z2,z3,z4]),(0,[z0,z67,z2,z68,z4,z7]),(0,[z821,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z786,z3,z7])],[(0,[z65,z0,z1,z2,z3,z4]),(0,[z0,z1,z822,z2,z4,z7]),(0,[z0,z1,z2,z823,z4,z7]),(0,[z824,z0,z1,z2,z3,z4]),(0,[z0,z1,z825,z3,z170,z7]),(0,[z415,z1,z79,z2,z3,z4]),(0,[z0,z1,z2,z3,z128,z114])],[(0,[z0,z1,z278,z2,z4,z34]),(0,[z30,z0,z93,z2,z3,z226]),(0,[z40,z0,z2,z3,z4,z83])],[(0,[z0,z1,z2,z418,z4,z34]),(0,[z0,z1,z2,z826,z4,z7]),(0,[z71,z46,z1,z2,z3,z4]),(0,[z0,z1,z338,z3,z24,z7]),(0,[z0,z1,z2,z3,z4,z827]),(0,[z0,z1,z89,z2,z3,z4])],[(0,[z224,z0,z1,z2,z121,z4]),(0,[z30,z616,z1,z2,z3,z4]),(0,[z828,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z829]),(0,[z175,z0,z1,z171,z172,z4]),(0,[z0,z1,z830,z2,z3,z34])],[(0,[z0,z1,z831,z3,z4,z7]),(0,[z0,z1,z832,z3,z4,z7]),(0,[z42,z1,z43,z2,z3,z31]),(0,[z0,z1,z2,z833,z4,z7]),(0,[z0,z1,z2,z3,z4,z834])],[(0,[z0,z1,z2,z3,z4,z835]),(0,[z0,z1,z2,z3,z4,z836]),(0,[z197,z0,z1,z159,z4,z7]),(0,[z0,z1,z98,z2,z764,z4]),(0,[z30,z0,z837,z2,z3,z4]),(0,[z30,z0,z1,z2,z792,z4]),(0,[z0,z1,z838,z2,z121,z4]),(0,[z0,z1,z250,z2,z4,z34]),(0,[z0,z1,z302,z3,z4,z34]),(0,[z0,z1,z441,z3,z170,z7])]],
   [[(0,[z839,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z68,z121,z4]),(0,[z0,z1,z2,z840,z4,z7]),(0,[z0,z1,z2,z3,z841,z34])],[(0,[z0,z1,z278,z310,z4,z34]),(0,[z0,z1,z842,z3,z4,z7]),(0,[z0,z1,z843,z3,z4,z7]),(0,[z0,z2,z3,z226,z844,z7]),(0,[z0,z696,z1,z172,z3,z4])],[(0,[z0,z1,z2,z3,z4,z845]),(0,[z0,z72,z1,z2,z121,z4]),(0,[z30,z0,z1,z171,z2,z4]),(0,[z0,z1,z2,z846,z3,z7]),(0,[z0,z2,z3,z4,z83,z709]),(0,[z0,z1,z492,z2,z4,z34]),(1,[z0,z1,z847,z3,z4]),(0,[z0,z1,z848,z3,z4,z7]),(0,[z849,z1,z2,z3,z4,z34])],[(0,[z0,z1,z2,z166,z121,z4])],[(0,[z0,z1,z185,z2,z4,z34]),(0,[z0,z1,z850,z3,z4,z7]),(0,[z367,z1,z302,z3,z4,z7]),(0,[z367,z1,z2,z74,z4,z7])],[(0,[z0,z1,z2,z3,z851,z7]),(0,[z80,z1,z2,z38,z4,z34]),(0,[z116,z0,z1,z2,z3,z433]),(0,[z14,z1,z2,z3,z4,z308]),(0,[z0,z852,z1,z2,z3,z4]),(0,[z853,z367,z1,z2,z3,z4]),(1,[z0,z2,z3,z844,z7])],[(0,[z0,z1,z2,z854,z4,z7]),(0,[z0,z1,z2,z3,z4,z775]),(0,[z0,z1,z855,z3,z4,z7]),(0,[z0,z1,z2,z121,z4,z31]),(0,[z0,z1,z2,z121,z4,z856]),(0,[z0,z1,z364,z2,z121,z4])],[(0,[z0,z1,z2,z3,z4,z857]),(0,[z0,z1,z858,z2,z4,z7]),(0,[z0,z1,z711,z2,z26,z4]),(0,[z116,z0,z1,z251,z2,z3])]],
   [[(0,[z0,z859,z1,z2,z3,z4]),(0,[z0,z1,z860,z3,z4,z7]),(0,[z0,z1,z123,z4,z204,z102]),(0,[z0,z1,z2,z786,z4,z7])],[(0,[z0,z1,z2,z3,z4,z861]),(0,[z0,z1,z2,z3,z4,z862]),(0,[z0,z1,z2,z3,z4,z863]),(0,[z41,z1,z278,z310,z4,z7]),(0,[z0,z1,z2,z786,z9,z7])],[(0,[z20,z715,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z864]),(0,[z0,z1,z2,z3,z121,z4]),(0,[z0,z1,z43,z477,z3,z4]),(0,[z116,z0,z1,z82,z2,z3])],[(0,[z238,z80,z1,z2,z38,z4]),(0,[z80,z1,z279,z2,z4,z7]),(0,[z0,z1,z123,z4,z865,z7])],[(0,[z80,z415,z1,z2,z3,z4]),(0,[z0,z1,z338,z3,z4,z34]),(0,[z14,z1,z2,z3,z4,z256]),(0,[z0,z59,z2,z8,z4,z34]),(0,[z0,z1,z2,z255,z4,z34])],[(0,[z30,z0,z1,z2,z866,z4]),(0,[z0,z1,z43,z2,z51,z4]),(0,[z367,z1,z2,z3,z4,z117])],[(0,[z0,z1,z867,z3,z4,z7]),(0,[z203,z14,z66,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z353]),(0,[z23,z1,z2,z3,z24,z34]),(0,[z0,z1,z2,z3,z4,z868]),(0,[z0,z1,z2,z3,z844,z7]),(0,[z0,z1,z2,z3,z4,z157]),(0,[z0,z1,z123,z4,z34,z102]),(0,[z0,z1,z848,z43,z3,z4])],[(0,[z0,z1,z2,z3,z4,z869]),(0,[z0,z1,z2,z3,z4,z870]),(0,[z343,z0,z1,z25,z3,z4]),(0,[z0,z1,z871,z2,z3,z4]),(0,[z0,z672,z2,z8,z4,z7]),(0,[z0,z1,z29,z2,z4,z34]),(0,[z0,z257,z151,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z872,z4,z7]),(0,[z873,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z874])],[(0,[z0,z1,z2,z310,z4,z34]),(0,[z0,z1,z875,z3,z4,z7]),(0,[z0,z1,z2,z576,z4,z34])],[(0,[z0,z1,z2,z3,z4,z876]),(0,[z30,z0,z1,z2,z810,z4]),(0,[z0,z1,z2,z206,z4,z34]),(0,[z0,z877,z1,z2,z3,z4]),(0,[z0,z1,z171,z2,z4,z7])],[(0,[z0,z1,z2,z3,z4,z878]),(0,[z0,z1,z2,z3,z764,z4]),(0,[z0,z1,z2,z3,z4,z879]),(0,[z30,z619,z1,z2,z3,z4]),(0,[z880,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z881,z3,z4]),(0,[z882,z367,z1,z2,z3,z4]),(0,[z0,z1,z883,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z884]),(0,[z0,z1,z2,z620,z4,z34]),(0,[z0,z1,z2,z3,z885,z7]),(0,[z461,z0,z1,z2,z121,z4]),(0,[z0,z1,z2,z886,z4,z7]),(0,[z0,z2,z3,z4,z844,z7])],[(0,[z0,z1,z2,z3,z4,z350]),(0,[z0,z1,z455,z2,z4,z34]),(0,[z405,z0,z432,z2,z3,z4]),(0,[z30,z0,z1,z2,z28,z4]),(0,[z0,z1,z187,z3,z4,z200])],[(0,[z0,z887,z2,z3,z4,z7]),(0,[z30,z408,z1,z2,z3,z4]),(0,[z0,z1,z2,z121,z4,z114]),(0,[z0,z1,z2,z51,z4,z34]),(0,[z0,z139,z73,z3,z4,z434]),(0,[z1,z2,z3,z4,z888,z7]),(0,[z0,z1,z131,z221,z2,z7])],[(0,[z0,z1,z2,z680,z4,z34]),(0,[z41,z1,z29,z2,z4,z7]),(0,[z367,z1,z2,z28,z4,z7]),(0,[z0,z2,z3,z4,z709,z81]),(0,[z0,z1,z2,z889,z3,z4])]],
   [[(0,[z0,z20,z1,z2,z121,z4]),(0,[z71,z1,z57,z3,z105,z7]),(0,[z0,z1,z2,z379,z3,z4]),(0,[z197,z0,z1,z2,z121,z4]),(1,[z1,z2,z716,z4,z7]),(0,[z0,z1,z2,z890,z3,z4]),(0,[z0,z1,z131,z2,z121,z4])],[(0,[z0,z1,z891,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z892]),(0,[z893,z0,z1,z2,z3,z4]),(0,[z0,z1,z894,z3,z4,z7]),(0,[z0,z1,z895,z3,z4,z7])],[(0,[z0,z1,z896,z2,z3,z4]),(0,[z0,z67,z2,z68,z4,z34]),(0,[z0,z1,z123,z4,z170,z34])],[(0,[z197,z1,z98,z3,z4,z7]),(0,[z0,z1,z98,z3,z249,z7]),(0,[z71,z1,z57,z3,z4,z34]),(0,[z0,z1,z897,z2,z3,z4]),(0,[z14,z30,z1,z2,z51,z4]),(0,[z63,z0,z477,z3,z94,z7])],[(0,[z0,z0,z1,z2,z121,z4])],[(0,[z46,z1,z2,z310,z4,z7]),(0,[z0,z1,z2,z3,z206,z4]),(0,[z42,z1,z305,z3,z31,z7]),(0,[z0,z1,z898,z2,z3,z4]),(0,[z23,z1,z323,z2,z3,z24]),(0,[z30,z1,z2,z3,z597,z4]),(0,[z0,z1,z43,z302,z3,z4]),(0,[z0,z1,z2,z74,z4,z423]),(0,[z0,z1,z3,z4,z865,z7]),(0,[z0,z1,z91,z3,z4,z34])],[(0,[z0,z1,z2,z899,z4,z7]),(0,[z0,z1,z159,z4,z170,z7]),(0,[z30,z0,z1,z2,z3,z900]),(0,[z30,z1,z529,z2,z3,z4]),(0,[z30,z1,z2,z3,z4,z754]),(0,[z901,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z902,z4,z7]),(0,[z1,z98,z782,z3,z4,z7]),(0,[z0,z1,z2,z121,z4,z170]),(0,[z175,z0,z1,z2,z121,z4]),(0,[z0,z1,z212,z2,z4,z34]),(0,[z0,z1,z2,z3,z4,z213])]],
   [[(0,[z0,z1,z2,z3,z4,z903]),(0,[z0,z1,z904,z2,z3,z4]),(0,[z0,z1,z43,z56,z2,z4]),(0,[z0,z1,z905,z2,z3,z4]),(0,[z30,z0,z1,z338,z3,z4]),(0,[z0,z1,z906,z2,z3,z4]),(0,[z0,z1,z131,z95,z43,z2])],[(0,[z0,z1,z2,z3,z907,z7]),(0,[z0,z1,z43,z2,z3,z105]),(0,[z0,z1,z79,z2,z4,z34]),(0,[z224,z0,z437,z2,z3,z4]),(0,[z0,z1,z908,z2,z3,z4]),(0,[z505,z0,z2,z3,z4,z83]),(0,[z175,z0,z1,z172,z180,z4]),(0,[z0,z1,z43,z2,z166,z9]),(0,[z46,z1,z2,z3,z4,z375])],[(0,[z0,z1,z909,z2,z3,z4]),(0,[z42,z0,z1,z2,z121,z4]),(0,[z0,z1,z437,z2,z121,z4]),(0,[z0,z59,z2,z8,z4,z152]),(0,[z0,z1,z624,z2,z4,z34]),(0,[z0,z1,z84,z2,z4,z34]),(0,[z910,z1,z2,z3,z4,z34])],[(0,[z0,z1,z911,z2,z4,z7]),(0,[z80,z1,z37,z2,z38,z4]),(0,[z0,z1,z2,z3,z4,z912]),(0,[z0,z2,z68,z913,z4,z7]),(0,[z63,z0,z2,z3,z844,z7]),(0,[z0,z1,z2,z914,z3,z4]),(0,[z0,z1,z427,z2,z4,z34])],[(0,[z0,z1,z915,z2,z3,z4]),(0,[z14,z0,z1,z916,z2,z4])],[(0,[z0,z1,z2,z704,z4,z34]),(0,[z0,z69,z260,z2,z3,z4]),(0,[z0,z1,z171,z43,z2,z4])],[(0,[z917,z0,z1,z2,z3,z4]),(0,[z0,z918,z2,z3,z4,z7]),(0,[z46,z1,z2,z3,z310,z4]),(0,[z110,z0,z1,z37,z2,z4]),(0,[z0,z1,z2,z121,z4,z167]),(0,[z14,z183,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z919]),(0,[z0,z1,z123,z111,z4,z34])],[(0,[z0,z1,z178,z2,z121,z4]),(0,[z0,z1,z2,z3,z920,z7]),(0,[z921,z1,z2,z3,z4,z7]),(0,[z922,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z923,z4,z7]),(0,[z0,z924,z2,z3,z4,z7]),(0,[z0,z1,z847,z3,z4,z7]),(0,[z0,z1,z131,z95,z2,z34]),(0,[z0,z1,z925,z2,z3,z7])],[(0,[z0,z1,z2,z926,z4,z7]),(0,[z0,z1,z2,z3,z4,z927]),(0,[z46,z23,z1,z2,z3,z4]),(0,[z0,z59,z1,z2,z121,z4]),(0,[z30,z0,z1,z123,z4,z102]),(0,[z30,z1,z2,z3,z414,z4]),(0,[z0,z1,z2,z3,z4,z928]),(0,[z0,z1,z929,z3,z4,z7]),(0,[z0,z1,z279,z2,z4,z34])],[(0,[z0,z1,z930,z3,z4,z7]),(0,[z71,z1,z56,z57,z4,z7]),(0,[z0,z931,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z932]),(0,[z0,z1,z123,z2,z4,z933])],[(0,[z30,z0,z1,z428,z3,z4]),(0,[z175,z0,z1,z381,z3,z4]),(0,[z0,z1,z131,z2,z786,z7])],[(0,[z0,z1,z2,z3,z249,z7]),(0,[z0,z1,z2,z3,z4,z934]),(0,[z0,z1,z2,z3,z4,z935]),(0,[z0,z1,z2,z3,z4,z423]),(0,[z0,z1,z43,z2,z4,z313])],[(0,[z0,z1,z648,z2,z4,z34]),(0,[z466,z0,z294,z2,z3,z4]),(0,[z186,z0,z1,z2,z301,z4]),(0,[z936,z1,z2,z3,z4,z7])],[(0,[z0,z1,z43,z2,z3,z4]),(1,[z0,z1,z278,z4,z34]),(0,[z0,z1,z2,z3,z4,z937])],[(0,[z197,z1,z782,z3,z4,z7]),(0,[z0,z1,z2,z121,z4,z7]),(0,[z141,z0,z1,z2,z121,z4]),(0,[z63,z0,z43,z2,z3,z94]),(0,[z0,z1,z2,z4,z64,z34]),(0,[z653,z0,z1,z123,z4,z7])]],
   [[(0,[z164,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z938,z4]),(0,[z30,z0,z1,z75,z162,z3]),(0,[z0,z1,z2,z3,z4,z939]),(0,[z0,z1,z2,z3,z4,z940]),(0,[z0,z67,z89,z2,z68,z4]),(0,[z0,z1,z2,z28,z4,z423]),(0,[z463,z0,z1,z82,z2,z3])],[(0,[z0,z1,z2,z3,z4,z941]),(0,[z0,z1,z332,z3,z170,z7]),(0,[z0,z1,z159,z2,z4,z34]),(0,[z0,z1,z2,z3,z4,z942]),(0,[z0,z1,z2,z172,z121,z4]),(0,[z292,z0,z1,z2,z3,z433]),(0,[z63,z0,z302,z3,z94,z7])],[(0,[z80,z0,z1,z2,z206,z4]),(0,[z76,z1,z2,z3,z31,z7]),(0,[z14,z0,z1,z2,z121,z4]),(0,[z0,z1,z111,z2,z121,z4]),(0,[z14,z0,z1,z477,z3,z4]),(0,[z14,z681,z1,z2,z3,z4]),(0,[z0,z1,z43,z111,z205,z4]),(0,[z0,z1,z364,z847,z3,z4])],[(0,[z0,z1,z782,z3,z4,z7]),(0,[z943,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z944,z3,z4]),(0,[z0,z1,z477,z74,z4,z7]),(0,[z0,z1,z2,z847,z3,z4])],[(0,[z0,z1,z945,z2,z3,z4]),(0,[z0,z1,z946,z2,z3,z4]),(0,[z30,z0,z1,z305,z3,z4]),(0,[z46,z1,z2,z3,z4,z31]),(0,[z0,z1,z947,z2,z121,z4]),(0,[z0,z1,z2,z948,z4,z7])],[(0,[z0,z1,z2,z38,z4,z253]),(0,[z30,z0,z1,z169,z3,z170]),(0,[z30,z1,z2,z626,z3,z4]),(0,[z949,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z4,z933,z34])],[(0,[z0,z1,z2,z950,z4,z7]),(0,[z14,z482,z1,z2,z3,z4]),(0,[z0,z1,z111,z2,z4,z34])],[(0,[z14,z15,z20,z2,z3,z4]),(0,[z0,z1,z556,z2,z4,z34])]],
   [[(0,[z0,z1,z951,z2,z3,z4]),(0,[z46,z0,z1,z2,z310,z4]),(0,[z1,z2,z38,z716,z4,z7]),(0,[z30,z0,z1,z952,z3,z4])],[(0,[z0,z1,z953,z2,z3,z4]),(0,[z0,z2,z3,z4,z954,z7]),(0,[z0,z1,z2,z955,z4,z7]),(0,[z0,z1,z2,z3,z4,z956]),(0,[z0,z1,z131,z95,z2,z148])],[(0,[z203,z120,z66,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z957]),(0,[z30,z1,z2,z3,z4,z605]),(0,[z63,z0,z2,z3,z94,z117]),(0,[z0,z1,z2,z180,z4,z7]),(0,[z0,z1,z825,z3,z4,z7])],[(0,[z0,z1,z2,z958,z121,z4]),(0,[z0,z1,z43,z843,z3,z4])],[(0,[z0,z715,z2,z3,z4,z7]),(0,[z0,z1,z959,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z960]),(0,[z197,z1,z98,z3,z4,z34]),(0,[z415,z0,z1,z2,z3,z4]),(0,[z0,z1,z961,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z962]),(0,[z0,z1,z477,z3,z4,z117]),(0,[z963,z0,z1,z2,z3,z4]),(0,[z0,z1,z650,z2,z4,z34]),(0,[z0,z1,z403,z3,z4,z70])],[(0,[z203,z30,z66,z2,z3,z4]),(0,[z0,z1,z2,z126,z4,z34]),(0,[z30,z1,z670,z2,z3,z4]),(0,[z149,z0,z1,z187,z3,z4]),(0,[z14,z96,z1,z2,z3,z4]),(0,[z0,z1,z2,z301,z4,z34]),(0,[z0,z1,z75,z3,z227,z7]),(0,[z0,z103,z1,z2,z47,z3])],[(0,[z71,z0,z1,z123,z4,z34]),(0,[z14,z0,z1,z964,z3,z4]),(0,[z0,z1,z2,z965,z3,z4])],[(0,[z0,z1,z2,z3,z4,z966]),(0,[z0,z1,z123,z2,z4,z253]),(0,[z30,z1,z2,z3,z4,z526]),(0,[z360,z0,z1,z2,z3,z349])]],
   [[(0,[z0,z1,z2,z967,z4,z7]),(0,[z0,z1,z57,z3,z249,z7]),(0,[z132,z30,z1,z2,z3,z4])],[(0,[z0,z1,z278,z3,z4,z34]),(0,[z0,z1,z952,z3,z4,z7]),(0,[z0,z1,z2,z121,z4,z83]),(0,[z968,z0,z1,z2,z3,z4]),(0,[z14,z0,z1,z131,z95,z2]),(0,[z0,z1,z2,z3,z4,z969]),(0,[z0,z1,z2,z3,z4,z970]),(0,[z0,z1,z492,z205,z4,z7])],[(0,[z1,z2,z3,z4,z746,z7]),(0,[z0,z1,z2,z74,z4,z34]),(0,[z971,z1,z2,z3,z4,z7])],[(0,[z203,z715,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z972]),(0,[z0,z1,z973,z2,z4,z7]),(0,[z197,z1,z98,z3,z4,z350]),(0,[z485,z41,z1,z2,z310,z4]),(0,[z0,z1,z323,z2,z3,z4]),(0,[z0,z1,z2,z974,z3,z4])],[(0,[z0,z1,z2,z3,z975,z7]),(0,[z30,z0,z1,z2,z976,z4]),(0,[z0,z1,z2,z3,z4,z977])],[(0,[z0,z1,z2,z978,z3,z4]),(0,[z0,z1,z2,z979,z3,z4]),(0,[z30,z1,z2,z51,z4,z167]),(0,[z14,z0,z139,z73,z3,z4]),(0,[z14,z0,z1,z302,z3,z4]),(0,[z14,z504,z1,z2,z3,z4]),(0,[z0,z2,z913,z3,z4,z7]),(0,[z0,z93,z2,z3,z226,z7]),(0,[z0,z1,z2,z370,z4,z34]),(0,[z0,z69,z2,z3,z4,z709]),(0,[z0,z1,z131,z95,z2,z573])],[(0,[z0,z1,z980,z2,z3,z4]),(0,[z40,z0,z649,z2,z3,z4]),(0,[z0,z1,z477,z28,z4,z7]),(0,[z0,z1,z981,z2,z3,z4]),(0,[z0,z1,z2,z334,z3,z4]),(0,[z0,z1,z201,z2,z4,z34])],[(0,[z0,z1,z2,z3,z4,z982]),(0,[z0,z837,z2,z3,z4,z7]),(0,[z46,z1,z98,z2,z3,z4]),(0,[z558,z1,z2,z3,z24,z7]),(0,[z0,z1,z43,z2,z271,z4]),(0,[z983,z1,z2,z3,z4,z7])]],
   [[(0,[z15,z20,z2,z3,z4,z446]),(0,[z14,z0,z1,z56,z2,z4]),(0,[z0,z1,z2,z3,z4,z984]),(0,[z0,z1,z2,z73,z121,z4]),(0,[z14,z569,z1,z2,z3,z4]),(0,[z0,z1,z205,z4,z865,z7]),(0,[z0,z1,z961,z43,z3,z4])],[(0,[z0,z1,z2,z985,z3,z4]),(0,[z0,z1,z2,z3,z4,z986]),(0,[z14,z0,z1,z2,z3,z105]),(0,[z30,z0,z1,z2,z854,z4]),(0,[z30,z263,z1,z2,z3,z4]),(0,[z14,z0,z1,z2,z166,z9]),(0,[z0,z1,z2,z3,z4,z987]),(0,[z0,z1,z2,z225,z4,z34]),(0,[z988,z1,z2,z3,z4,z7]),(0,[z0,z1,z763,z3,z4,z7]),(0,[z0,z1,z428,z3,z4,z34])],[(0,[z0,z1,z989,z2,z3,z4]),(0,[z0,z1,z43,z2,z74,z4]),(0,[z990,z1,z2,z3,z4,z7]),(0,[z991,z1,z2,z3,z4,z7]),(0,[z0,z1,z43,z2,z502,z4])],[(0,[z23,z1,z43,z2,z3,z24]),(0,[z1,z2,z3,z4,z754,z7]),(1,[z0,z2,z913,z4,z7]),(0,[z0,z1,z2,z992,z3,z4]),(0,[z175,z0,z1,z847,z3,z4]),(0,[z0,z1,z2,z166,z9,z34]),(0,[z0,z1,z82,z925,z2,z3])],[(0,[z0,z1,z159,z2,z4,z993]),(0,[z0,z1,z2,z121,z121,z4]),(0,[z994,z0,z1,z2,z3,z4]),(0,[z995,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z180,z4,z83]),(0,[z0,z1,z84,z452,z3,z4])],[(0,[z203,z66,z2,z3,z4,z7]),(0,[z996,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z997]),(0,[z0,z1,z56,z2,z379,z4]),(0,[z186,z0,z1,z2,z310,z4]),(0,[z0,z1,z43,z2,z121,z4]),(0,[z30,z0,z1,z2,z180,z4]),(0,[z14,z0,z1,z2,z3,z975]),(0,[z402,z0,z1,z354,z3,z4])],[(0,[z0,z1,z2,z3,z105,z7]),(0,[z0,z1,z2,z998,z4,z7]),(0,[z0,z1,z2,z380,z4,z34]),(0,[z30,z0,z1,z791,z3,z4]),(0,[z0,z1,z718,z2,z3,z4])],[(0,[z238,z0,z1,z2,z51,z4]),(0,[z0,z1,z82,z2,z121,z4]),(0,[z0,z2,z3,z844,z94,z7])]],
   [[(0,[z0,z1,z2,z121,z4,z34]),(0,[z0,z1,z2,z3,z4,z999]),(0,[z0,z1000,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z34]),(0,[z0,z1,z21,z3,z4,z7]),(0,[z30,z0,z67,z2,z68,z4]),(0,[z0,z1,z2,z3,z1001,z7]),(0,[z164,z1,z2,z3,z4,z34]),(0,[z1002,z0,z1,z2,z3,z4]),(0,[z0,z1,z43,z2,z4,z34])],[(0,[z14,z0,z59,z2,z8,z4]),(0,[z0,z1,z302,z3,z4,z117]),(0,[z0,z1,z925,z2,z3,z114])],[(0,[z0,z1,z1003,z3,z4,z7]),(0,[z1004,z0,z1,z2,z3,z4]),(0,[z0,z1,z25,z2,z121,z4]),(0,[z0,z1,z111,z205,z4,z157])],[(0,[z46,z1,z2,z3,z4,z167]),(0,[z0,z1,z2,z479,z4,z34])],[(0,[z0,z1,z2,z28,z4,z34]),(0,[z0,z1,z75,z162,z3,z7]),(0,[z0,z1,z43,z91,z3,z4])],[(0,[z14,z0,z1,z2,z3,z4]),(0,[z367,z1,z2,z3,z4,z7]),(0,[z80,z0,z1,z278,z4,z7]),(0,[z1,z2,z3,z24,z746,z7]),(0,[z1005,z0,z1,z2,z3,z4])],[(0,[z0,z1,z120,z2,z3,z4]),(0,[z1006,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1007])]],
   [[(0,[z41,z0,z1,z2,z206,z4]),(0,[z1008,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1009]),(0,[z0,z1,z2,z3,z4,z1010]),(0,[z0,z1,z2,z3,z456,z114]),(0,[z1011,z0,z1,z2,z3,z4]),(0,[z0,z1,z1012,z3,z4,z7])],[(0,[z0,z1,z1013,z3,z4,z7]),(0,[z0,z1,z1014,z2,z3,z4]),(0,[z0,z1,z2,z1015,z3,z4]),(0,[z0,z1,z159,z2,z379,z4]),(0,[z0,z1,z1016,z3,z4,z7]),(0,[z0,z1,z512,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1017]),(0,[z30,z0,z924,z2,z3,z4]),(0,[z14,z0,z1,z111,z205,z4]),(0,[z0,z1,z2,z3,z4,z1018]),(0,[z1019,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z866,z4,z7]),(0,[z14,z30,z1,z2,z121,z4]),(0,[z1020,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1021]),(0,[z1022,z0,z1,z2,z3,z4])],[(0,[z41,z1,z2,z310,z4,z7]),(0,[z0,z69,z1,z2,z121,z4]),(0,[z0,z1,z2,z1023,z3,z4]),(0,[z1024,z0,z1,z2,z3,z4])],[(0,[z41,z30,z1,z2,z310,z4]),(0,[z0,z1025,z1,z2,z3,z4]),(0,[z0,z1,z1026,z3,z4,z7]),(0,[z0,z1,z1027,z3,z4,z7]),(0,[z0,z1,z2,z90,z4,z34]),(0,[z0,z1,z1028,z2,z3,z4]),(0,[z0,z1,z1029,z2,z3,z4])],[(0,[z0,z1,z1030,z3,z4,z7]),(0,[z14,z0,z1,z159,z2,z4]),(0,[z197,z1,z612,z3,z4,z7]),(0,[z0,z1,z2,z716,z4,z7]),(0,[z186,z0,z1,z2,z121,z4]),(0,[z0,z1,z403,z3,z4,z200])],[(0,[z1031,z1,z2,z3,z4,z7]),(1,[z0,z1,z4,z865,z7]),(0,[z0,z1,z43,z2,z336,z4])]],
   [[(0,[z0,z1032,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1033])],[(0,[z0,z1,z2,z162,z121,z4])],[(0,[z80,z0,z1,z2,z121,z4]),(0,[z30,z415,z1,z2,z3,z4]),(0,[z0,z1,z2,z121,z128,z4]),(0,[z0,z67,z2,z68,z4,z101]),(0,[z0,z1,z2,z3,z4,z148])],[(0,[z30,z0,z1,z2,z1034,z4]),(0,[z1035,z0,z1,z2,z3,z4])],[(0,[z0,z1,z1036,z3,z4,z7]),(0,[z0,z1,z2,z1037,z4,z7]),(0,[z0,z1,z2,z282,z4,z34]),(0,[z0,z1,z710,z3,z4,z7]),(0,[z0,z1,z1038,z2,z3,z4]),(0,[z40,z0,z2,z3,z4,z541]),(0,[z0,z1,z2,z1039,z4,z7])],[(0,[z0,z1,z1040,z2,z3,z4]),(0,[z1,z2,z716,z310,z4,z7]),(0,[z41,z1,z43,z2,z310,z4]),(0,[z0,z1,z1041,z2,z4,z7]),(0,[z0,z1,z537,z2,z4,z34])],[(0,[z203,z0,z1,z2,z121,z4]),(0,[z0,z1,z1042,z3,z4,z7]),(0,[z1043,z0,z1,z2,z3,z4]),(0,[z0,z1,z1044,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1045]),(0,[z0,z1,z2,z3,z4,z1046]),(0,[z14,z0,z1,z278,z3,z4]),(0,[z0,z1,z2,z205,z121,z4]),(0,[z14,z0,z1,z2,z3,z885]),(0,[z0,z1,z2,z3,z4,z152]),(0,[z0,z125,z2,z3,z4,z81]),(0,[z0,z394,z2,z3,z4,z83]),(0,[z0,z1,z2,z3,z4,z1047]),(0,[z0,z1,z2,z567,z4,z34])]],
   [[(0,[z0,z1,z2,z3,z4,z1048]),(0,[z186,z0,z1,z123,z2,z4]),(0,[z1,z2,z3,z746,z31,z7]),(0,[z1049,z0,z1,z2,z3,z4])],[(0,[z46,z20,z1,z2,z3,z4]),(0,[z0,z1,z790,z3,z4,z7])],[(0,[z0,z1,z2,z3,z1050,z7]),(0,[z0,z1,z1051,z2,z3,z4]),(0,[z0,z1,z2,z1052,z4,z7]),(0,[z0,z1,z43,z2,z258,z4])],[(0,[z0,z1,z43,z2,z3,z249]),(0,[z0,z1,z2,z3,z4,z1053]),(0,[z0,z1,z2,z121,z4,z94]),(0,[z30,z0,z1,z2,z1054,z4]),(0,[z0,z1,z2,z274,z4,z34])],[(0,[z0,z1,z2,z3,z4,z993]),(0,[z0,z1,z111,z512,z205,z4])],[(0,[z0,z1,z2,z3,z4,z1055]),(0,[z46,z0,z1,z2,z3,z4]),(0,[z511,z0,z1,z2,z3,z4]),(0,[z0,z1,z1056,z2,z121,z4]),(0,[z1057,z0,z1,z2,z3,z4]),(0,[z175,z0,z1,z172,z3,z4]),(0,[z0,z1,z172,z847,z3,z4])],[(0,[z203,z66,z2,z3,z4,z34]),(0,[z0,z1,z1058,z3,z4,z7]),(0,[z80,z1,z2,z38,z4,z397]),(0,[z0,z1,z2,z1054,z4,z7]),(0,[z14,z164,z1,z2,z3,z4]),(0,[z14,z1,z2,z3,z4,z471]),(0,[z0,z1,z1059,z3,z4,z7])],[(0,[z0,z1,z1060,z2,z3,z7]),(0,[z0,z1,z1061,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1062]),(0,[z15,z20,z2,z3,z4,z163]),(0,[z0,z1,z2,z3,z4,z1063]),(0,[z0,z1,z2,z3,z1064,z4]),(0,[z164,z1,z2,z3,z4,z423]),(0,[z0,z1,z1065,z3,z4,z7]),(0,[z1066,z0,z1,z2,z3,z4])]],
   [[(0,[z30,z0,z1,z2,z955,z4]),(0,[z0,z1,z2,z1067,z4,z7]),(0,[z0,z1,z1068,z2,z3,z4]),(0,[z110,z0,z1,z711,z2,z4])],[(0,[z0,z1,z1069,z3,z4,z7]),(0,[z186,z0,z1,z2,z206,z4]),(0,[z30,z0,z1,z1003,z3,z4]),(0,[z0,z1,z2,z121,z4,z200]),(0,[z164,z1,z43,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1070]),(0,[z0,z1,z364,z3,z4,z200])],[(0,[z0,z1,z2,z581,z4,z34]),(0,[z1,z2,z310,z4,z471,z34]),(0,[z275,z0,z1,z2,z206,z4]),(0,[z14,z0,z1,z2,z74,z4])],[(0,[z297,z66,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z1071,z4]),(0,[z0,z1,z2,z1072,z3,z4]),(0,[z0,z1,z2,z1073,z3,z4]),(0,[z0,z1,z2,z3,z4,z1074]),(0,[z0,z1,z2,z3,z4,z204])],[(0,[z0,z1,z1075,z2,z4,z7]),(0,[z0,z1,z2,z1076,z4,z7]),(0,[z63,z0,z2,z74,z94,z7]),(0,[z0,z1,z2,z1077,z4,z7])],[(0,[z289,z1,z98,z3,z4,z7]),(0,[z0,z1,z1078,z2,z3,z4]),(0,[z0,z1,z21,z310,z4,z34]),(0,[z0,z1,z37,z2,z51,z4]),(0,[z30,z0,z1,z477,z3,z4]),(0,[z0,z1,z585,z3,z4,z200]),(0,[z0,z1,z111,z205,z4,z7])],[(0,[z0,z1,z2,z1034,z4,z7]),(0,[z15,z140,z2,z3,z4,z7]),(0,[z30,z0,z1,z2,z3,z805]),(0,[z14,z362,z1,z2,z3,z4]),(0,[z0,z1,z169,z3,z170,z7]),(0,[z0,z1,z171,z2,z4,z34])],[(0,[z0,z1,z1079,z3,z4,z7]),(0,[z110,z0,z1,z2,z386,z4]),(0,[z0,z1,z364,z452,z3,z4]),(0,[z880,z1,z2,z3,z4,z34]),(0,[z0,z1,z883,z3,z4,z34])]],
   [[(0,[z30,z0,z1,z2,z51,z4]),(0,[z0,z1,z2,z3,z4,z1080]),(0,[z0,z1,z2,z3,z4,z1081]),(0,[z0,z1,z2,z320,z4,z34]),(0,[z0,z1,z925,z2,z3,z4])],[(0,[z71,z1,z159,z57,z4,z7]),(0,[z0,z1,z205,z704,z4,z7]),(0,[z30,z207,z1,z2,z3,z4]),(0,[z0,z1,z75,z145,z3,z7]),(0,[z0,z1,z1082,z3,z4,z7]),(0,[z0,z1,z1012,z3,z4,z34])],[(0,[z30,z15,z20,z2,z3,z4]),(0,[z1083,z0,z1,z2,z3,z4]),(0,[z0,z1084,z1,z2,z3,z4]),(0,[z0,z514,z2,z3,z4,z81]),(0,[z1085,z1,z2,z3,z4,z7]),(0,[z1,z2,z3,z4,z888,z34])],[(0,[z0,z1,z2,z3,z4,z1086]),(0,[z0,z1,z1087,z3,z4,z7]),(0,[z0,z1,z1088,z3,z4,z7]),(0,[z0,z1,z2,z3,z128,z546])],[(0,[z41,z0,z1,z278,z4,z7]),(0,[z0,z1,z278,z3,z386,z4]),(0,[z238,z415,z1,z2,z3,z4]),(0,[z0,z1,z1089,z2,z3,z4]),(0,[z30,z1,z201,z2,z3,z4]),(0,[z0,z139,z73,z3,z4,z7]),(0,[z110,z0,z1,z2,z4,z64])],[(0,[z41,z1,z21,z310,z4,z7]),(0,[z41,z1,z2,z310,z4,z34]),(0,[z14,z0,z1,z91,z3,z4]),(0,[z0,z1,z2,z3,z4,z1090])],[(0,[z0,z1,z1091,z2,z4,z7]),(0,[z0,z1,z1027,z3,z4,z34])],[(0,[z0,z1,z753,z2,z99,z4]),(0,[z14,z30,z1,z2,z3,z4]),(0,[z0,z1092,z1,z2,z121,z4]),(0,[z1093,z0,z1,z2,z3,z4]),(0,[z30,z1,z2,z121,z4,z167]),(1,[z1,z2,z3,z4,z754]),(0,[z0,z1,z111,z442,z4,z7])]],
   [[(0,[z0,z1,z338,z3,z31,z7]),(0,[z30,z1,z2,z3,z4,z167]),(0,[z0,z1,z2,z3,z4,z1094])],[(0,[z46,z1,z2,z310,z4,z34]),(0,[z0,z1,z95,z2,z121,z4]),(0,[z1095,z0,z1,z2,z3,z4]),(0,[z40,z0,z2,z3,z4,z709])],[(0,[z0,z1,z305,z3,z4,z7]),(0,[z186,z0,z1,z2,z3,z4]),(0,[z23,z1,z2,z3,z746,z7]),(0,[z0,z1,z1096,z2,z3,z4]),(0,[z0,z1,z123,z2,z121,z4]),(0,[z0,z1,z2,z3,z4,z1097]),(0,[z0,z1,z2,z3,z4,z1098])],[(0,[z14,z23,z1,z2,z3,z24]),(0,[z63,z0,z2,z3,z94,z7]),(0,[z0,z1,z2,z1099,z3,z4])],[(0,[z15,z0,z1,z2,z121,z4]),(0,[z1,z2,z782,z3,z4,z7]),(0,[z197,z0,z1,z123,z4,z34]),(0,[z0,z1,z2,z386,z121,z4]),(0,[z30,z0,z1,z131,z95,z2]),(0,[z1100,z1,z2,z3,z4,z7]),(0,[z1101,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z26,z121,z4]),(0,[z1,z2,z3,z4,z754,z167]),(0,[z0,z1,z477,z3,z4,z7]),(0,[z164,z1,z477,z3,z4,z7]),(0,[z0,z1,z711,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1102]),(0,[z0,z1,z1103,z2,z3,z4]),(0,[z42,z1,z338,z3,z31,z7]),(0,[z0,z1,z123,z2,z4,z157]),(0,[z1,z2,z3,z4,z789,z7]),(0,[z0,z1,z2,z377,z4,z34])],[(0,[z1104,z0,z1,z2,z3,z4]),(0,[z0,z1,z123,z48,z4,z7]),(0,[z0,z1,z2,z310,z4,z253]),(0,[z0,z1,z1105,z2,z3,z4]),(0,[z0,z1,z2,z351,z4,z34]),(0,[z115,z30,z1,z2,z3,z4]),(0,[z63,z0,z2,z28,z94,z7]),(0,[z0,z1,z711,z2,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z1106]),(0,[z41,z0,z1,z2,z121,z4]),(0,[z30,z0,z1,z302,z3,z4]),(0,[z0,z1,z169,z825,z3,z7])],[(0,[z0,z1,z2,z3,z4,z1107]),(0,[z0,z1,z2,z3,z4,z374]),(0,[z405,z0,z1,z2,z121,z4]),(0,[z0,z1108,z1,z2,z3,z4]),(0,[z30,z1,z2,z317,z3,z4]),(0,[z1109,z0,z1,z2,z3,z4]),(0,[z1110,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1111]),(0,[z0,z1,z2,z26,z4,z34]),(0,[z0,z1,z2,z3,z33,z114])],[(0,[z0,z1,z2,z3,z1112,z7]),(0,[z14,z0,z1,z21,z3,z4]),(0,[z0,z1,z2,z1113,z3,z4]),(0,[z0,z1,z2,z3,z4,z1114]),(0,[z30,z0,z1115,z2,z3,z4]),(0,[z0,z1,z1116,z2,z3,z4])],[(0,[z30,z0,z1,z56,z2,z4]),(0,[z0,z1,z2,z1117,z3,z4]),(0,[z0,z1,z1118,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1119]),(0,[z0,z1,z2,z3,z4,z1120]),(0,[z0,z245,z2,z3,z4,z81]),(0,[z46,z0,z1,z111,z2,z4])],[(0,[z30,z0,z1,z2,z3,z105]),(0,[z0,z1,z2,z3,z386,z4]),(0,[z80,z46,z1,z2,z3,z4]),(0,[z46,z0,z1,z2,z121,z4]),(0,[z30,z0,z1,z2,z166,z9]),(0,[z0,z1,z302,z74,z4,z7]),(0,[z0,z1,z2,z3,z4,z1121])],[(0,[z1122,z0,z1,z56,z2,z4]),(0,[z0,z1,z1123,z2,z3,z4]),(0,[z14,z564,z1,z2,z3,z4]),(0,[z0,z2,z1124,z3,z4,z7])],[(0,[z15,z20,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z900,z7]),(0,[z203,z66,z43,z2,z3,z4]),(0,[z0,z1,z2,z368,z4,z34]),(0,[z461,z0,z1,z2,z3,z119]),(1,[z0,z1,z825,z3,z7]),(0,[z0,z1,z131,z95,z91,z7])],[(0,[z0,z1,z1125,z2,z3,z7]),(0,[z238,z0,z1,z2,z121,z4]),(1,[z0,z1,z925,z2,z3])]],
   [[(0,[z203,z46,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1126]),(0,[z0,z1,z2,z3,z249,z34]),(1,[z1,z2,z3,z746,z7]),(0,[z0,z1,z2,z121,z24,z4]),(0,[z0,z1,z631,z2,z4,z34]),(0,[z0,z1,z123,z4,z7,z102]),(0,[z0,z1,z2,z4,z865,z7]),(0,[z0,z1,z43,z2,z12,z4])],[(0,[z0,z1,z2,z3,z1127,z7]),(0,[z0,z1,z2,z1128,z3,z4]),(0,[z0,z2,z3,z4,z709,z7]),(0,[z0,z1,z2,z3,z4,z64]),(0,[z0,z1,z1129,z2,z3,z4]),(0,[z0,z1,z1130,z3,z4,z7]),(0,[z0,z1,z925,z2,z3,z128])],[(0,[z0,z1,z1131,z3,z4,z7]),(0,[z0,z1,z1132,z2,z3,z4]),(0,[z1133,z1,z2,z3,z4,z7]),(0,[z0,z1,z123,z75,z4,z34]),(0,[z0,z1,z162,z825,z3,z7]),(0,[z0,z1,z82,z2,z47,z3])],[(0,[z14,z0,z1,z2,z3,z249]),(0,[z0,z1,z2,z1134,z3,z4]),(0,[z0,z1,z1135,z2,z74,z4])],[(0,[z0,z1,z2,z3,z4,z1136]),(0,[z0,z1137,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1138]),(0,[z0,z1,z2,z3,z4,z1139]),(0,[z0,z1,z95,z2,z786,z7]),(1,[z0,z1,z711,z2,z4])],[(0,[z0,z1,z2,z1140,z4,z7]),(0,[z14,z197,z1,z98,z3,z4]),(0,[z0,z1,z2,z3,z1141,z4]),(0,[z30,z0,z1,z2,z3,z812]),(0,[z304,z0,z1,z587,z3,z4]),(0,[z30,z0,z59,z2,z8,z4]),(0,[z367,z1,z2,z3,z4,z423]),(0,[z0,z1,z2,z74,z4,z117])],[(0,[z0,z1,z2,z3,z4,z1142]),(0,[z0,z1,z37,z2,z3,z4]),(0,[z1143,z0,z1,z2,z3,z4]),(0,[z0,z1,z43,z2,z4,z286]),(0,[z0,z1124,z73,z3,z4,z7]),(0,[z46,z0,z1,z123,z2,z4]),(0,[z0,z1,z111,z205,z4,z34]),(0,[z0,z1,z1144,z2,z3,z4]),(0,[z0,z1,z86,z2,z4,z34]),(0,[z238,z1,z201,z2,z3,z4])],[(0,[z0,z1,z123,z126,z4,z7]),(0,[z71,z1,z43,z57,z3,z4]),(0,[z0,z1,z964,z3,z4,z7]),(0,[z1145,z0,z1,z2,z3,z4]),(0,[z1146,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z913,z4,z7]),(0,[z367,z1,z43,z2,z3,z4]),(0,[z1093,z164,z1,z2,z3,z4]),(0,[z0,z1,z169,z3,z170,z34]),(0,[z0,z1,z2,z1147,z3,z4])]],
   [[(0,[z0,z1,z1078,z2,z4,z34]),(0,[z0,z1,z2,z121,z4,z102]),(0,[z40,z0,z1,z2,z121,z4]),(0,[z14,z376,z1,z2,z3,z4]),(0,[z1148,z0,z1,z2,z3,z4]),(0,[z0,z257,z2,z3,z4,z83]),(0,[z1149,z0,z1,z2,z3,z4])],[(0,[z30,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z101]),(0,[z0,z1,z830,z2,z3,z7]),(0,[z0,z1,z2,z1150,z3,z4])],[(0,[z45,z30,z1,z2,z3,z4]),(0,[z0,z1,z2,z1151,z4,z7]),(0,[z0,z1,z43,z2,z4,z551]),(0,[z0,z1,z428,z131,z95,z7]),(0,[z186,z1,z2,z3,z4,z471])],[(0,[z1122,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z348]),(0,[z0,z1,z302,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1152]),(0,[z164,z1,z302,z3,z4,z7]),(0,[z63,z164,z2,z3,z94,z7]),(0,[z0,z1,z2,z74,z4,z1153]),(0,[z0,z1,z364,z2,z180,z4])],[(0,[z0,z1,z2,z1154,z3,z7]),(0,[z41,z1,z2,z386,z310,z4]),(0,[z0,z1,z916,z2,z4,z7]),(0,[z0,z139,z1124,z3,z4,z7]),(0,[z0,z1,z2,z3,z841,z7]),(0,[z0,z1,z75,z825,z3,z7])],[(0,[z343,z0,z1,z2,z121,z4]),(0,[z30,z0,z1,z111,z205,z4]),(0,[z0,z139,z73,z3,z4,z34]),(0,[z1155,z0,z1,z2,z3,z4])],[(0,[z0,z1,z1156,z3,z4,z7]),(0,[z30,z0,z1,z2,z769,z4]),(0,[z1157,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z349,z114]),(0,[z0,z1,z2,z3,z4,z1158]),(0,[z0,z59,z2,z913,z4,z7]),(0,[z0,z1,z2,z180,z4,z34]),(0,[z849,z1,z2,z3,z4,z7])],[(0,[z0,z1159,z1,z2,z121,z4]),(0,[z14,z46,z1,z2,z3,z4]),(0,[z0,z1,z302,z28,z4,z7])]],
   [[(0,[z0,z1,z1160,z2,z3,z4]),(0,[z186,z0,z1,z111,z2,z4]),(0,[z0,z1,z2,z3,z4,z1161]),(0,[z0,z1,z2,z3,z4,z1162]),(0,[z0,z1,z2,z3,z4,z1163]),(0,[z0,z1,z2,z3,z4,z1164]),(0,[z0,z1,z2,z414,z4,z34])],[(0,[z30,z0,z1,z159,z2,z4]),(0,[z80,z1,z2,z38,z4,z7]),(0,[z0,z1,z25,z172,z3,z4]),(0,[z0,z93,z43,z2,z3,z226])],[(0,[z1,z715,z2,z3,z4,z7]),(0,[z0,z1,z1165,z2,z3,z4]),(0,[z0,z1115,z2,z3,z4,z7]),(0,[z0,z1166,z1,z2,z3,z4]),(0,[z153,z0,z649,z2,z3,z4]),(0,[z0,z1,z1124,z3,z4,z7]),(0,[z18,z0,z1,z442,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1167]),(0,[z71,z14,z1,z57,z3,z4]),(0,[z1168,z0,z1,z2,z3,z4]),(0,[z1169,z0,z1,z2,z3,z4]),(0,[z0,z59,z2,z8,z4,z497]),(0,[z0,z1,z2,z3,z4,z1170])],[(0,[z0,z1,z1171,z3,z4,z7]),(0,[z15,z715,z2,z3,z4,z7]),(0,[z0,z1,z2,z1172,z3,z4]),(0,[z80,z1,z2,z716,z4,z7]),(0,[z1173,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1174]),(0,[z0,z1,z75,z43,z162,z3])],[(0,[z1,z2,z716,z3,z4,z7]),(0,[z0,z1,z43,z21,z3,z4]),(0,[z0,z1,z2,z3,z4,z1175]),(0,[z0,z1,z2,z121,z4,z1176]),(0,[z1177,z0,z1,z2,z3,z4]),(0,[z853,z0,z1,z2,z3,z4]),(0,[z1178,z0,z1,z2,z3,z4]),(0,[z0,z1,z169,z43,z3,z170])],[(0,[z30,z0,z1,z2,z1076,z4]),(0,[z0,z1,z2,z1179,z4,z7])],[(0,[z0,z1,z1180,z3,z4,z7]),(0,[z0,z1,z123,z3,z249,z7]),(0,[z71,z1,z29,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1181])]],
   [[(0,[z0,z1,z2,z3,z4,z1182]),(0,[z1,z782,z57,z3,z4,z7]),(0,[z0,z1,z2,z764,z4,z7]),(0,[z0,z1,z2,z28,z4,z117]),(0,[z0,z1,z711,z2,z4,z34])],[(0,[z0,z1,z2,z1183,z4,z7]),(0,[z0,z1,z2,z99,z764,z4]),(0,[z485,z0,z1,z2,z3,z4]),(0,[z1184,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1185,z7]),(0,[z0,z93,z2,z3,z226,z34])],[(0,[z0,z1,z2,z3,z1186,z7]),(0,[z0,z1,z82,z2,z3,z50]),(0,[z0,z1,z43,z2,z28,z4]),(0,[z0,z1,z2,z3,z4,z1153]),(0,[z0,z1,z2,z3,z4,z1187])],[(0,[z0,z1188,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1189]),(0,[z0,z1,z2,z3,z4,z1190]),(0,[z0,z1,z2,z3,z4,z1191]),(0,[z367,z1,z477,z3,z4,z7]),(0,[z983,z1,z2,z3,z4,z34]),(0,[z0,z1,z43,z1130,z3,z4])],[(0,[z0,z1,z66,z2,z121,z4]),(0,[z0,z1,z111,z2,z4,z253]),(0,[z0,z139,z43,z73,z3,z4]),(0,[z1192,z0,z1,z2,z3,z4]),(0,[z116,z0,z1,z925,z2,z3])],[(0,[z0,z1,z2,z1193,z4,z7]),(0,[z23,z1,z2,z3,z133,z7]),(0,[z0,z67,z2,z913,z4,z7]),(0,[z0,z1,z1194,z3,z4,z7]),(0,[z0,z1,z847,z3,z4,z200])],[(0,[z0,z1,z2,z3,z4,z1195]),(0,[z0,z1,z1196,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1197]),(0,[z0,z1,z2,z3,z4,z1198]),(0,[z14,z80,z1,z2,z38,z4]),(0,[z30,z0,z1,z2,z926,z4]),(0,[z518,z30,z1,z2,z3,z4]),(0,[z1199,z0,z1,z2,z3,z4]),(0,[z63,z14,z0,z2,z3,z94]),(0,[z0,z1,z1200,z2,z3,z4]),(0,[z1201,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z1202,z7]),(0,[z197,z1,z98,z99,z3,z4]),(0,[z14,z321,z1,z2,z3,z4])]],
   [[(0,[z107,z0,z1,z56,z2,z4])],[(0,[z0,z1,z2,z3,z1203,z7]),(0,[z76,z1,z57,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1204]),(0,[z30,z164,z1,z2,z3,z4]),(0,[z1205,z1,z2,z3,z4,z7]),(0,[z1206,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z573])],[(0,[z0,z1,z2,z3,z4,z1207]),(0,[z0,z1,z2,z3,z105,z34]),(0,[z0,z1,z2,z51,z4,z7]),(0,[z0,z1,z2,z121,z8,z4]),(0,[z1208,z1,z2,z3,z4,z7]),(0,[z0,z1,z1209,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z933]),(0,[z0,z393,z260,z2,z3,z4])],[(0,[z0,z1,z1210,z3,z4,z7]),(0,[z238,z0,z1,z2,z3,z4]),(0,[z80,z30,z1,z2,z38,z4]),(0,[z30,z0,z767,z2,z3,z4]),(0,[z722,z0,z1,z2,z3,z4]),(0,[z882,z0,z1,z2,z3,z4]),(0,[z1211,z0,z1,z2,z3,z4]),(0,[z0,z1,z84,z2,z180,z4])],[(0,[z1212,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z1213,z3,z4]),(0,[z0,z1,z1214,z3,z4,z7]),(0,[z49,z0,z1,z2,z121,z4]),(0,[z175,z0,z1,z2,z180,z4]),(0,[z0,z1215,z1,z2,z3,z4])],[(0,[z0,z1216,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1217]),(0,[z41,z1,z2,z310,z4,z374]),(0,[z0,z1,z2,z3,z1218,z4]),(0,[z0,z1,z21,z3,z4,z34]),(0,[z0,z1,z43,z338,z3,z4]),(0,[z0,z1,z1219,z2,z121,z4]),(0,[z30,z0,z1,z2,z74,z4]),(0,[z0,z1,z2,z121,z4,z81]),(0,[z1220,z1,z2,z3,z4,z7]),(0,[z0,z1,z4,z865,z7,z102])],[(0,[z14,z367,z1,z2,z3,z4]),(0,[z0,z2,z913,z8,z4,z7]),(0,[z0,z1,z171,z2,z4,z64])],[(0,[z71,z1,z57,z3,z4,z7]),(0,[z0,z1,z2,z3,z1221,z4]),(0,[z0,z1,z1222,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1223]),(0,[z14,z0,z1,z721,z2,z4]),(0,[z0,z1,z2,z3,z4,z1224]),(0,[z0,z1,z1225,z2,z3,z4]),(0,[z0,z341,z1,z43,z2,z4])]],
   [[(0,[z0,z1,z1226,z2,z4,z7]),(0,[z30,z0,z1,z2,z121,z4]),(0,[z14,z0,z93,z2,z3,z226]),(0,[z1227,z0,z1,z2,z3,z4])],[(0,[z71,z0,z1,z159,z4,z7]),(0,[z0,z1,z37,z2,z4,z34]),(0,[z30,z653,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z128,z119]),(0,[z0,z1,z1228,z2,z3,z4]),(0,[z0,z179,z73,z3,z4,z7]),(0,[z0,z1,z91,z3,z4,z7]),(0,[z0,z1,z75,z162,z3,z34])],[(0,[z71,z1,z379,z57,z3,z4]),(0,[z0,z1,z2,z57,z121,z4]),(0,[z0,z1,z75,z155,z3,z7]),(0,[z0,z1,z2,z3,z4,z397]),(0,[z485,z0,z1,z278,z3,z4]),(0,[z42,z1,z2,z3,z5,z31]),(0,[z0,z1,z1229,z2,z4,z7]),(0,[z0,z59,z43,z2,z8,z4]),(0,[z367,z1,z2,z3,z4,z34]),(0,[z0,z1,z1135,z2,z3,z4])],[(0,[z80,z1,z43,z2,z38,z4]),(0,[z0,z1,z2,z38,z121,z4]),(0,[z0,z1,z2,z1230,z3,z4]),(0,[z0,z1,z111,z4,z865,z7]),(0,[z0,z1,z2,z3,z33,z32]),(0,[z0,z1,z273,z2,z3,z546])],[(0,[z0,z1,z2,z3,z4,z1231]),(0,[z0,z1,z1078,z2,z38,z4]),(0,[z1232,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1233])],[(0,[z0,z1,z278,z4,z7,z34])],[(0,[z107,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1234]),(0,[z910,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z38,z4,z34]),(0,[z0,z1,z2,z3,z4,z1235]),(0,[z0,z432,z1,z2,z121,z4]),(0,[z14,z555,z1,z2,z3,z4]),(0,[z14,z0,z1,z171,z2,z4]),(1,[z0,z2,z3,z4,z709]),(0,[z0,z1,z2,z825,z3,z7]),(0,[z248,z0,z1,z251,z2,z3])]],
   [[(0,[z0,z1,z2,z3,z1236,z4]),(0,[z0,z1,z339,z162,z3,z7]),(0,[z30,z0,z1,z91,z3,z4]),(0,[z1237,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1238]),(0,[z0,z1,z2,z180,z4,z81]),(0,[z0,z1,z2,z686,z4,z34])],[(0,[z0,z1,z56,z2,z4,z7]),(0,[z0,z1,z2,z976,z4,z7]),(0,[z0,z1,z2,z3,z4,z1239]),(0,[z0,z1,z2,z3,z4,z1240]),(0,[z0,z1,z494,z2,z4,z34])],[(0,[z1241,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1242,z4]),(0,[z63,z0,z2,z3,z94,z423])],[(0,[z1243,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1244]),(0,[z0,z1,z2,z1245,z3,z4]),(0,[z30,z0,z1,z1214,z3,z4]),(0,[z0,z69,z437,z2,z3,z4]),(0,[z356,z0,z1,z381,z3,z4])],[(0,[z0,z1,z2,z99,z3,z4]),(0,[z30,z1,z228,z2,z3,z4]),(0,[z0,z1,z1246,z2,z3,z4]),(0,[z0,z1,z477,z3,z4,z423]),(0,[z0,z1,z131,z95,z2,z7])],[(0,[z0,z1,z2,z1247,z3,z4]),(0,[z0,z1,z1248,z2,z3,z4]),(0,[z30,z0,z1,z2,z736,z4]),(0,[z30,z0,z1,z2,z3,z851]),(0,[z35,z30,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z754]),(0,[z110,z0,z1,z2,z206,z4]),(0,[z14,z1,z2,z3,z4,z198])],[(0,[z0,z1,z2,z1249,z3,z4]),(0,[z107,z0,z1,z159,z2,z4]),(0,[z0,z1,z1250,z2,z3,z4]),(0,[z30,z23,z1,z2,z3,z24]),(0,[z0,z1,z2,z121,z50,z4]),(0,[z0,z93,z2,z3,z844,z7]),(0,[z0,z1,z2,z3,z4,z1251])],[(0,[z0,z1,z2,z3,z4,z253]),(0,[z42,z14,z1,z2,z3,z31]),(0,[z0,z1,z2,z3,z4,z1252]),(0,[z14,z0,z1,z832,z3,z4]),(0,[z14,z0,z1,z2,z180,z4])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 512).take 513) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1025).take 307) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1332)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [512, 513, 307] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 64).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 64).take 69).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 133).take 77).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 210).take 46).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [64, 69, 77, 46] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_43096

theorem PEqualNP.Outside.L_meta_43096 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677352 * 2 ^ 32 + 4276668608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4276668608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43096.solve