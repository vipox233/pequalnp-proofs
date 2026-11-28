import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47028

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
  Nat.testBit (4008241320 * 2 ^ 32 + 3974686880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00070a14b301616a#64 ++ 0x0003850a5980b0b5#64 ++ 0xf68f1e3ff703e3ff#64 ++ 0x7b478f1ffb81f1ff#64 : BitVec 256),
   (0x023064ca506cacb8#64 ++ 0x011832652836565c#64 ++ 0xff70e7ce79fcfcf9#64 ++ 0xffb873e73cfe7e7c#64 : BitVec 256),
   (0x1580b1630c161614#64 ++ 0x0ac058b1860b0b0a#64 ++ 0xbf80f9f38e1f1f1f#64 ++ 0xdfc07cf9c70f8f8f#64 : BitVec 256),
   (0x49db01bc0fa01bc0#64 ++ 0x24ed80de07d00de0#64 ++ 0xdbff01fc0fe01fe1#64 ++ 0xedff80fe07f00ff0#64 : BitVec 256),
   (0xa1edde000fdbc000#64 ++ 0x50f6ef0007ede000#64 ++ 0xedfffe000fffe001#64 ++ 0xf6ffff0007fff000#64 : BitVec 256),
   (0x71feffffe0000000#64 ++ 0xb8ff7ffff0000000#64 ++ 0x71fffffff0000001#64 ++ 0xb8fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000010002028 0x0000000008001014 0xf600060e7100e0f9 0x7b0003073880707c

def z1 : W := mkw 0x02376edef36dedfa 0x011bb76f79b6f6fd 0xffffffffffffffff 0xffffffffffffffff

def z2 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z3 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z4 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x71fffffff0000001 0xb8fffffff8000000

def z5 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xedfffe000fffe001 0xf6ffff0007fff000

def z6 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0xf68f1e3ff703e3ff 0x7b478f1ffb81f1ff

def z7 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0xff70e7ce79fcfcf9 0xffb873e73cfe7e7c

def z8 : W := mkw 0x41de0bbca0000000 0x20ef05de50000000 0x71ff1ffff0000001 0xb8ff8ffff8000000

def z9 : W := mkw 0x49df0bbcbfa17bea 0x24ef85de5fd0bdf5 0xffff1fffffe3ffff 0xffff8ffffff1ffff

def z10 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x860000000703e3fe 0x430000000381f1ff

def z11 : W := mkw 0xa3fdfeca5fffecb8 0x51feff652ffff65c 0xffffffce7ffffcf9 0xffffffe73ffffe7c

def z12 : W := mkw 0x003064ca40000000 0x0018326520000000 0x7170e7ce70000001 0xb8b873e738000000

def z13 : W := mkw 0x73fefffff06cacb8 0xb9ff7ffff836565c 0xfffffffff9fcfcf9 0xfffffffffcfe7e7c

def z14 : W := mkw 0x71debbffe0000000 0xb8ef5dfff0000000 0x108f19fff0000000 0x08478cfff8000000

def z15 : W := mkw 0x607e4e9ce0000000 0xb03f274e70000000 0x407f060c70000000 0x203f830638000000

def z16 : W := mkw 0xe9ffdfbc0ffbdbc0 0x74ffefde07fdede0 0xfffffffc0fffffe1 0xfffffffe07fffff0

def z17 : W := mkw 0xb1edfe43efdbc000 0xd8f6ff21f7ede000 0xedfffe03ffffe001 0xf6ffff01fffff000

def z18 : W := mkw 0x21ecde0000000000 0x10f66f0000000000 0x61fffe0000000001 0xb0ffff0000000000

def z19 : W := mkw 0xf1ffffffefdbc000 0xf8fffffff7ede000 0xfdffffffffffe001 0xfefffffffffff000

def z20 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x708f1e3ff0000001 0x38478f1ff8000000

def z21 : W := mkw 0x71fffffff301616a 0xb8fffffff980b0b5 0xf7fffffff703e3ff 0xfbfffffffb81f1ff

def z22 : W := mkw 0x800000000cda8000 0x40000000066d4000 0x0800000008fc0000 0x04000000047e0000

def z23 : W := mkw 0x0000204200040410 0x0000102100020208 0xbf00e1c2081c1c19 0xdf8070e1040e0e0c

def z24 : W := mkw 0x71feffffe0040410 0xb8ff7ffff0020208 0xfffffffff81c1c19 0xfffffffffc0e0e0c

def z25 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x128019f386031f1e 0x09400cf9c3018f8f

def z26 : W := mkw 0x3234fecbf06cacb8 0x991a7f65f836565c 0xff70ffcff9fcfcf9 0xffb87fe7fcfe7e7c

def z27 : W := mkw 0xf1feffffe05bc000 0xf8ff7ffff02de000 0x75fffffff01fe001 0xbafffffff80ff000

def z28 : W := mkw 0x00070a14a3014142 0x0003850a5180a0a1 0x008f183186030306 0x00478c18c3018183

def z29 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x0900e1c0081c1c00 0x848070e0040e0e00

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0x3080183380000001 0x18400c19c0000000

def z31 : W := mkw 0xa1cd9a000f934000 0x50e6cd0007c9a000 0x008f180006030000 0x00478c0003018000

def z32 : W := mkw 0x01d900880fa00880 0x00ec804407d00440 0xdbff01cc0fe01ce1 0xedff80e607f00e70

def z33 : W := mkw 0x49d801a80ca01a80 0x24ec00d406500d40 0xdb7001cc09e01ce1 0xedb800e604f00e70

def z34 : W := mkw 0x01cd0a000f814000 0x00e6850007c0a000 0xedff1e000fe3e001 0xf6ff8f0007f1f000

def z35 : W := mkw 0x00040a00a0000000 0x0002050050000000 0x20001e03f0000000 0x10000f01f8000000

def z36 : W := mkw 0x00050a0003014000 0x000285000180a000 0xe48f1e000703e001 0x72478f000381f000

def z37 : W := mkw 0xa1e8d4000cda8000 0x50f46a00066d4000 0x0970e00008fc0000 0x84b87000047e0000

def z38 : W := mkw 0x0010008800200880 0x0008004400100440 0xdb7001cc09e01ce1 0xedb800e604f00e70

def z39 : W := mkw 0x02206442504ca438 0x011032212826521c 0x2400e602701ce018 0x12007301380e700c

def z40 : W := mkw 0x0020440000488000 0x0010220000244000 0xed70e60009fce001 0xf6b8730004fe7000

def z41 : W := mkw 0x71feffffe0488000 0xb8ff7ffff0244000 0xfdfffffff9fce001 0xfefffffffcfe7000

def z42 : W := mkw 0xb5edff630fdfd614 0x5af6ffb187efeb0a 0xfffffff38fffff1f 0xfffffff9c7ffff8f

def z43 : W := mkw 0x21fcfeca40000000 0x10fe7f6520000000 0x71ffffce70000001 0xb8ffffe738000000

def z44 : W := mkw 0x13b0f5eb506cacb8 0x09d87af5a836565c 0xfff0fffff9fcfcf9 0xfff87ffffcfe7e7c

def z45 : W := mkw 0x75feffffec161614 0xbaff7ffff60b0b0a 0xfffffffffe1f1f1f 0xffffffffff0f8f8f

def z46 : W := mkw 0xa06d4e0003c9c000 0x5036a70001e4e000 0x407f060001e0e000 0x203f830000f07000

def z47 : W := mkw 0x058001200c161614 0x02c00090060b0b0a 0x9f8001f00e1f1f1f 0xcfc000f8070f8f8f

def z48 : W := mkw 0x4bff6ffeffedfffa 0x25ffb7ff7ff6fffd 0xffffffffffffffff 0xffffffffffffffff

def z49 : W := mkw 0xa3fffedeffffedfa 0x51ffff6f7ffff6fd 0xffffffffffffffff 0xffffffffffffffff

def z50 : W := mkw 0x0001000003000140 0x00008000018000a0 0x82000000070003e0 0x41000000038001f0

def z51 : W := mkw 0x1400b04300160414 0x0a005821800b020a 0xbf00f9c3881f1c1f 0xdf807ce1c40f8e0f

def z52 : W := mkw 0x0000000010002028 0x0000000008001014 0x240006027000e018 0x120003013800700c

def z53 : W := mkw 0x018301340f001340 0x00c1809a078009a0 0xdb8f01fc0f001fe1 0xedc780fe07800ff0

def z54 : W := mkw 0x0001000003014000 0x000080000180a000 0x840000000703e000 0x420000000381f000

def z55 : W := mkw 0x71ce9b35a0000000 0xb8e74d9ad0000000 0x008f183180000000 0x00478c18c0000000

def z56 : W := mkw 0x02002042106cacb8 0x010010210836565c 0xbf00e1c209fcfcf9 0xdf8070e104fe7e7c

def z57 : W := mkw 0x00030014b301616a 0x0001800a5980b0b5 0x9600003ff703e3fe 0x4b00001ffb81f1ff

def z58 : W := mkw 0x023044885068a8a8 0x0118224428345454 0xf670060e71e0e0f9 0x7b38030738f0707c

def z59 : W := mkw 0x21edde0003014000 0x10f6ef000180a000 0xe5fffe000703e001 0xf2ffff000381f000

def z60 : W := mkw 0x01c900000f800000 0x00e4800007c00000 0xc9ff00000fe00001 0xe4ff800007f00000

def z61 : W := mkw 0x0000000010002028 0x0000000008001014 0xf6801e3ff703e3ff 0x7b400f1ffb81f1ff

def z62 : W := mkw 0x023064ca406c8c90 0x0118326520364648 0x0970e1c008fc1c00 0x84b870e0047e0e00

def z63 : W := mkw 0x003064ca50002028 0x0018326528001014 0xf770e7ce7100e0f9 0xfbb873e73880707c

def z64 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0x40ff1e0007e3e000 0x207f8f0003f1f000

def z65 : W := mkw 0x020000001068a8a8 0x0100000008345454 0x0000000001e0e0e0 0x0000000000f07070

def z66 : W := mkw 0x49cb01340f801340 0x24e5809a07c009a0 0xc9ff00300fe00301 0xe4ff801807f00180

def z67 : W := mkw 0xe9ffde9c0ffbc9c0 0x74ffef4e07fde4e0 0xedfffe0c0fffe0e1 0xf6ffff0607fff070

def z68 : W := mkw 0x41df0bbcb301616a 0x20ef85de5980b0b5 0xf7ff1ffff703e3ff 0xfbff8ffffb81f1ff

def z69 : W := mkw 0x02206442504ca438 0x011032212826521c 0xed70e60279fce019 0xf6b873013cfe700c

def z70 : W := mkw 0x484b001403800140 0x2425800a01c000a0 0x000f000000000000 0x0007800000000000

def z71 : W := mkw 0x41da01bc00200880 0x20ed00de00100440 0xdbff01fc09e01ce1 0xedff80fe04f00e70

def z72 : W := mkw 0x75ffffffff17777e 0xbaffffffff8bbbbf 0xffffffffff1fffff 0xffffffffff8fffff

def z73 : W := mkw 0xe1ffde9cefdbc000 0xf0ffef4e77ede000 0xedfffe0c7fffe001 0xf6ffff063ffff000

def z74 : W := mkw 0x040000000c161614 0x02000000060b0b0a 0x8e0000000e1f1f1e 0x47000000070f8f8f

def z75 : W := mkw 0x1630f4cb507eacbc 0x0b187a65a83f565e 0xff70ffcff9fffcff 0xffb87fe7fcfffe7f

def z76 : W := mkw 0x02000000106cacb8 0x010000000836565c 0x8e00000009fcfcf8 0x4700000004fe7e7c

def z77 : W := mkw 0x0000000000000000 0x0000000000000000 0xd200000c010000e1 0x6900000600800070

def z78 : W := mkw 0x1400b04300160414 0x0a005821800b020a 0x2400f803801f001e 0x12007c01c00f800f

def z79 : W := mkw 0x485b009c03a009c0 0x242d804e01d004e0 0x407f000c01e000e0 0x203f800600f00070

def z80 : W := mkw 0x021020ca40240c90 0x0108106520120648 0x000001c000001c00 0x000000e000000e00

def z81 : W := mkw 0x00040a00b001602a 0x000205005800b015 0x24001e03f003e01e 0x12000f01f801f00f

def z82 : W := mkw 0x49d801a80ca01a80 0x24ec00d406500d40 0x097001c008e01c00 0x84b800e004700e00

def z83 : W := mkw 0x49da01bc0ca01bc0 0x24ed00de06500de0 0x1b7001fc08e01fe0 0x8db800fe04700ff0

def z84 : W := mkw 0xb5e8f5630cde9614 0x5af47ab1866f4b0a 0xbff0f9f38eff1f1f 0xdff87cf9c77f8f8f

def z85 : W := mkw 0x08070a14bfa17bea 0x0403850a5fd0bdf5 0xfe8f1e3fffe3ffff 0x7f478f1ffff1ffff

def z86 : W := mkw 0x823164ca5fffecb8 0x4118b2652ffff65c 0xff70e7ce7ffffcf9 0xffb873e73ffffe7c

def z87 : W := mkw 0x023044885068a8a8 0x0118224428345454 0x4070060c71e0e0e0 0x2038030638f07070

def z88 : W := mkw 0x71feffffe0200880 0xb8ff7ffff0100440 0xfbfffffff9e01ce1 0xfdfffffffcf00e70

def z89 : W := mkw 0x30049a01a0000000 0x98024d00d0000000 0x0000180180000000 0x00000c00c0000000

def z90 : W := mkw 0x000000000c001200 0x0000000006000900 0x8a0000000e001f00 0x4500000007000f80

def z91 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0xf68f1e3ff603031f 0x7b478f1ffb01818f

def z92 : W := mkw 0x79ffffffefa01bc0 0xbcfffffff7d00de0 0xfbffffffffe01fe1 0xfdfffffffff00ff0

def z93 : W := mkw 0x0003001403000140 0x0001800a018000a0 0xd28f003c070003e1 0x6947801e038001f0

def z94 : W := mkw 0x018021620c041610 0x00c010b106020b08 0xbf80e1f20e1c1f19 0xdfc070f9070e0f8c

def z95 : W := mkw 0x41da01bc0c001200 0x20ed00de06000900 0xdbff01fc0e001f01 0xedff80fe07000f80

def z96 : W := mkw 0xa5edde000fdfd614 0x52f6ef0007efeb0a 0xeffffe000fffff1f 0xf7ffff0007ffff8f

def z97 : W := mkw 0x485b01bc03a01bc0 0x242d80de01d00de0 0x527f01fc01e01fe0 0x293f80fe00f00ff0

def z98 : W := mkw 0x2024de0000000000 0x10126f0000000000 0x2000fe0000000000 0x10007f0000000000

def z99 : W := mkw 0x17a0f5635c5eb63c 0x0bd07ab1ae2f5b1e 0xbf80fff3fe1fff1f 0xdfc07ff9ff0fff8f

def z100 : W := mkw 0x02204400106cacb8 0x011022000836565c 0xef70e60009fcfcf9 0xf7b8730004fe7e7c

def z101 : W := mkw 0x71f8f5eb40000000 0xb8fc7af5a0000000 0x0170e1c000000000 0x80b870e000000000

def z102 : W := mkw 0x31ecfe43e0000000 0x98f67f21f0000000 0x61fffe03f0000001 0xb0ffff01f8000000

def z103 : W := mkw 0xa1efde14afdbc142 0x50f7ef0a57ede0a1 0xedfffe318fffe307 0xf6ffff18c7fff183

def z104 : W := mkw 0x75f8f5eb4c161614 0xbafc7af5a60b0b0a 0xbff0f9f38e1f1f1f 0xdff87cf9c70f8f8f

def z105 : W := mkw 0x00020014b000216a 0x0001000a580010b5 0x1200003ff00003fe 0x0900001ff80001ff

def z106 : W := mkw 0xa27d6eca53edecb8 0x513eb76529f6f65c 0xff7fe7ce79fcfcf9 0xffbff3e73cfe7e7c

def z107 : W := mkw 0x71f8f5eb40000000 0xb8fc7af5a0000000 0x31f0f9f380000001 0x98f87cf9c0000000

def z108 : W := mkw 0x02206442504ca438 0x011032212826521c 0xf600e60e711ce0f9 0x7b007307388e707c

def z109 : W := mkw 0x75feffffec121204 0xbaff7ffff6090902 0x71fffffff6030307 0xb8fffffffb018183

def z110 : W := mkw 0x49cb01340fa01bc0 0x24e5809a07d00de0 0x8a8f00300fe01fe0 0x4547801807f00ff0

def z111 : W := mkw 0x77fefffffc7ebebc 0xbbff7ffffe3f5f5e 0xffffffffffffffff 0xffffffffffffffff

def z112 : W := mkw 0x627e6edef06cacb8 0xb13f376f7836565c 0xff7fe7ce79fcfcf9 0xffbff3e73cfe7e7c

def z113 : W := mkw 0x080100000fa01bc0 0x0400800007d00de0 0x8a0000000fe01fe0 0x4500000007f00ff0

def z114 : W := mkw 0x501221ffe0000000 0xa80910fff0000000 0x100001fff0000000 0x080000fff8000000

def z115 : W := mkw 0xe07f4e9ce3c9c000 0xf03fa74e71e4e000 0x407f060c71e0e000 0x203f830638f07000

def z116 : W := mkw 0x040000000c121204 0x0200000006090902 0x0000000006030306 0x0000000003018183

def z117 : W := mkw 0x1590b1eb0c361e94 0x0ac858f5861b0f4a 0xfff0f9ff8fff1fff 0xfff87cffc7ff8fff

def z118 : W := mkw 0x3024fe43e0000000 0x98127f21f0000000 0x2000fe03f0000000 0x10007f01f8000000

def z119 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0x520f063ff100e3fe 0x2907831ff88071ff

def z120 : W := mkw 0x1400216300041614 0x0a0010b180020b0a 0x120001f380001f1e 0x090000f9c0000f8f

def z121 : W := mkw 0x5192b1ffe0000000 0xa8c958fff0000000 0x3180f9fff0000001 0x98c07cfff8000000

def z122 : W := mkw 0x401201bc00000000 0x200900de00000000 0x100001fc00000000 0x080000fe00000000

def z123 : W := mkw 0x21eede14a0000000 0x10f76f0a50000000 0x71fffe3ff0000001 0xb8ffff1ff8000000

def z124 : W := mkw 0xa1efde14bfdbe16a 0x50f7ef0a5fedf0b5 0xfffffe3fffffe3ff 0xffffff1ffffff1ff

def z125 : W := mkw 0x01a0d4000c5a8000 0x00d06a00062d4000 0xedf0fe000fffe001 0xf6f87f0007fff000

def z126 : W := mkw 0x0000012000001200 0x0000009000000900 0x120001f000001f00 0x090000f800000f80

def z127 : W := mkw 0x001020ca00240c90 0x0008106500120648 0xff70e1ce09fc1cf9 0xffb870e704fe0e7c

def z128 : W := mkw 0x003064ca40040410 0x0018326520020208 0xff70e7ce781c1c19 0xffb873e73c0e0e0c

def z129 : W := mkw 0x481201bc00201bc0 0x240900de00100de0 0x120001fc00001fe0 0x090000fe00000ff0

def z130 : W := mkw 0x0013009c032009c0 0x0009804e019004e0 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z131 : W := mkw 0x79feffffeca01a80 0xbcff7ffff6500d40 0x79fffffff8e01c01 0xbcfffffffc700e00

def z132 : W := mkw 0x1180b16300000000 0x08c058b180000000 0x3180f9f380000001 0x98c07cf9c0000000

def z133 : W := mkw 0x3424fe43e0160414 0x9a127f21f00b020a 0x2400fe03f01f001e 0x12007f01f80f800f

def z134 : W := mkw 0x687f4e9ce3a009c0 0xb43fa74e71d004e0 0x407f060c71e000e0 0x203f830638f00070

def z135 : W := mkw 0xa024de00005bc000 0x50126f00002de000 0x2400fe00001fe000 0x12007f00000ff000

def z136 : W := mkw 0x02366edef06cacb8 0x011b376f7836565c 0xfffffffff9fcfcf9 0xfffffffffcfe7e7c

def z137 : W := mkw 0x0010008800200880 0x0008004400100440 0x4070000c01e000e0 0x2038000600f00070

def z138 : W := mkw 0x49cb01340f801340 0x24e5809a07c009a0 0x008f003006000300 0x0047801803000180

def z139 : W := mkw 0x41fa65fe40000000 0x20fd32ff20000000 0x71ffe7fe70000001 0xb8fff3ff38000000

def z140 : W := mkw 0xebfffffe5ffffff8 0x75ffffff2ffffffc 0xfffffffe7ffffff9 0xffffffff3ffffffc

def z141 : W := mkw 0x1407ba57b317657e 0x0a03dd2bd98bb2bf 0xf68ffe3ff71fe3ff 0x7b47ff1ffb8ff1ff

def z142 : W := mkw 0x00070a1403014140 0x0003850a0180a0a0 0xf68f1e3c0703e3e1 0x7b478f1e0381f1f0

def z143 : W := mkw 0xa1edde00bfdbe02a 0x50f6ef005fedf015 0xedfffe03ffffe01f 0xf6ffff01fffff00f

def z144 : W := mkw 0x3024fe43f001602a 0x98127f21f800b015 0x2400fe03f003e01e 0x12007f01f801f00f

def z145 : W := mkw 0x17b0f5eb5c7ebebc 0x0bd87af5ae3f5f5e 0xfff0ffffffffffff 0xfff87fffffffffff

def z146 : W := mkw 0x158091210c121204 0x0ac0489086090902 0x0080183186030306 0x00400c18c3018183

def z147 : W := mkw 0x485b009c03a009c0 0x242d804e01d004e0 0xdb7f01cc09e01ce1 0xedbf80e604f00e70

def z148 : W := mkw 0x485b009c0fa01bc0 0x242d804e07d00de0 0xca7f000c0fe01fe0 0x653f800607f00ff0

def z149 : W := mkw 0x158091210c161614 0x0ac04890860b0b0a 0x8e8018318e1f1f1e 0x47400c18c70f8f8f

def z150 : W := mkw 0x018001200c001200 0x00c0009006000900 0x9b8001f00e001f01 0xcdc000f807000f80

def z151 : W := mkw 0x5ddbb1ff0fb61fd4 0x2eedd8ff87db0fea 0xfffff9ff8fff1fff 0xfffffcffc7ff8fff

def z152 : W := mkw 0x018090000c120000 0x00c0480006090000 0xad80f8000e1f0001 0xd6c07c00070f8000

def z153 : W := mkw 0x800100001fdbe16a 0x400080000fedf0b5 0x8e0000000fffe3fe 0x4700000007fff1ff

def z154 : W := mkw 0x4bdb01bc1fecbff8 0x25ed80de0ff65ffc 0xdfff01fc0ffcfff9 0xefff80fe07fe7ffc

def z155 : W := mkw 0x607f4e9cf301616a 0xb03fa74e7980b0b5 0xf6ff1e3ff703e3ff 0x7b7f8f1ffb81f1ff

def z156 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0x400f060c7100e0e0 0x2007830638807070

def z157 : W := mkw 0x1584bb63bc17763e 0x0ac25db1de0bbb1f 0xbf80fff3fe1fff1f 0xdfc07ff9ff0fff8f

def z158 : W := mkw 0x00020014b000216a 0x0001000a580010b5 0xf600063ff100e3ff 0x7b00031ff88071ff

def z159 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0xbf00e1c2081c1c19 0xdf8070e1040e0e0c

def z160 : W := mkw 0x71ffffffe3014142 0xb8fffffff180a0a1 0x71fffffff6030307 0xb8fffffffb018183

def z161 : W := mkw 0x71fefffff0002028 0xb8ff7ffff8001014 0xf7fffffff100e0f9 0xfbfffffff880707c

def z162 : W := mkw 0x49cb01340f801340 0x24e5809a07c009a0 0xd28f003c070003e1 0x6947801e038001f0

def z163 : W := mkw 0x41da01bc00000000 0x20ed00de00000000 0x51ff01fc00000001 0xa8ff80fe00000000

def z164 : W := mkw 0x7036ffffe0000000 0xb81b7ffff0000000 0x3000fffff0000000 0x18007ffff8000000

def z165 : W := mkw 0x4bfb65fe5fecbff8 0x25fdb2ff2ff65ffc 0xffffe7fe7ffcfff9 0xfffff3ff3ffe7ffc

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0xad00e000081c0001 0xd6807000040e0000

def z167 : W := mkw 0x1400900100120004 0x0a00480080090002 0x0000180180030006 0x00000c00c0018003

def z168 : W := mkw 0x0000000010002028 0x0000000008001014 0x4000060c7100e0e0 0x2000030638807070

def z169 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0x09ff01f00ee01f00 0x84ff80f807700f80

def z170 : W := mkw 0x0000204210042438 0x000010210802121c 0xff00e7ce791cfcf9 0xff8073e73c8e7e7c

def z171 : W := mkw 0x485f0a9cb3a169ea 0x242f854e59d0b4f5 0x407f060c71e0e0e0 0x203f830638f07070

def z172 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0x40ff003c07e003e0 0x207f801e03f001f0

def z173 : W := mkw 0x021020ca50242cb8 0x010810652812165c 0x120001ce70001cf8 0x090000e738000e7c

def z174 : W := mkw 0x3026fe57e0000000 0x98137f2bf0000000 0x708ffe3ff0000001 0x3847ff1ff8000000

def z175 : W := mkw 0x01c900000f800000 0x00e4800007c00000 0x008f000006000000 0x0047800003000000

def z176 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080183186030306 0x00400c18c3018183

def z177 : W := mkw 0x14022177b004377e 0x0a0110bbd8021bbf 0x120001fff0001ffe 0x090000fff8000fff

def z178 : W := mkw 0x0000000000200880 0x0000000000100440 0x8a00000009e01ce0 0x4500000004f00e70

def z179 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x9b80e1f00e1c1f01 0xcdc070f8070e0f80

def z180 : W := mkw 0x71cf9b35a3014142 0xb8e7cd9ad180a0a1 0x008f183186030306 0x00478c18c3018183

def z181 : W := mkw 0x71fefffff000216a 0xb8ff7ffff80010b5 0x73fffffff00003ff 0xb9fffffff80001ff

def z182 : W := mkw 0x021020ca506cacb8 0x010810652836565c 0x9e0001ce79fcfcf8 0x4f0000e73cfe7e7c

def z183 : W := mkw 0x1400216300041614 0x0a0010b180020b0a 0x000001c000001c00 0x000000e000000e00

def z184 : W := mkw 0x080100001fa17bea 0x040080000fd0bdf5 0x8e0000000fe3fffe 0x4700000007f1ffff

def z185 : W := mkw 0x49d901a80fa01bc0 0x24ec80d407d00de0 0x8b7001c00fe01fe0 0xc5b800e007f00ff0

def z186 : W := mkw 0x02356eca536decb8 0x011ab76529b6f65c 0xffffffce7ffffcf9 0xffffffe73ffffe7c

def z187 : W := mkw 0x000100001301616a 0x000080000980b0b5 0xb68018338703e3ff 0x5b400c19c381f1ff

def z188 : W := mkw 0x0020440000488000 0x0010220000244000 0x0970e00008fc0000 0x84b87000047e0000

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x860000000603031e 0x430000000301818f

def z190 : W := mkw 0x0010008800000000 0x0008004400000000 0x517001cc00000001 0xa8b800e600000000

def z191 : W := mkw 0xe9efdf340fdbd340 0x74f7ef9a07ede9a0 0xedfffe300fffe301 0xf6ffff1807fff180

def z192 : W := mkw 0x00070a14a3014142 0x0003850a5180a0a1 0xe48f1e318703e307 0x72478f18c381f183

def z193 : W := mkw 0x800100000fdbc000 0x4000800007ede000 0x8c0000000fffe000 0x4600000007fff000

def z194 : W := mkw 0x3224fe43f04ca438 0x99127f21f826521c 0x2400fe03f01ce018 0x12007f01f80e700c

def z195 : W := mkw 0x49db009c0fa009c0 0x24ed804e07d004e0 0xc9ff000c0fe000e1 0xe4ff800607f00070

def z196 : W := mkw 0x00366edee0000000 0x001b376f70000000 0x71fffffff0000001 0xb8fffffff8000000

def z197 : W := mkw 0x02376edef36dedfa 0x011bb76f79b6f6fd 0xff7fe7ce79fcfcf9 0xffbff3e73cfe7e7c

def z198 : W := mkw 0x0400000000160414 0x02000000000b020a 0x04000000001f001e 0x02000000000f800f

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0xb68018338603031f 0x5b400c19c301818f

def z200 : W := mkw 0x75f8f5eb4c161614 0xbafc7af5a60b0b0a 0x0970e1c0081c1c00 0x84b870e0040e0e00

def z201 : W := mkw 0xa1e8d4000cda8000 0x50f46a00066d4000 0xed70e60009fce001 0xf6b8730004fe7000

def z202 : W := mkw 0x0002001400000140 0x0001000a000000a0 0x1200003c000003e0 0x0900001e000001f0

def z203 : W := mkw 0xa3f8f4ca5cfeacb8 0x51fc7a652e7f565c 0xff70e7ce79fcfcf9 0xffb873e73cfe7e7c

def z204 : W := mkw 0x71feffffec120000 0xb8ff7ffff6090000 0xfdfffffffe1f0001 0xfeffffffff0f8000

def z205 : W := mkw 0x00050a0003014000 0x000285000180a000 0xf68f1e338703e31f 0x7b478f19c381f18f

def z206 : W := mkw 0xf1cf9b35af934000 0xf8e7cd9ad7c9a000 0x008f183186030000 0x00478c18c3018000

def z207 : W := mkw 0x0002001400000000 0x0001000a00000000 0x508f003c00000001 0x2847801e00000000

def z208 : W := mkw 0x0001000003014142 0x000080000180a0a1 0x0000000006030306 0x0000000003018183

def z209 : W := mkw 0x5ddb21ff0fa41fd4 0x2eed90ff87d20fea 0xdbff01ff8fe01fff 0xedff80ffc7f00fff

def z210 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0x497fe60009fce000 0xa4bff30004fe7000

def z211 : W := mkw 0xa1cd9a000fdbc000 0x50e6cd0007ede000 0x8c8f18000fffe000 0x46478c0007fff000

def z212 : W := mkw 0x49df0bbcafa15bc2 0x24ef85de57d0ade1 0xdbff19fd8fe31fe7 0xedff8cfec7f18ff3

def z213 : W := mkw 0x71fffffff301616a 0xb8fffffff980b0b5 0x71fffffff100e0e1 0xb8fffffff8807070

def z214 : W := mkw 0x607e4e9ce0000000 0xb03f274e70000000 0x70ff1e3ff0000001 0x387f8f1ff8000000

def z215 : W := mkw 0x1400216300041614 0x0a0010b180020b0a 0xb68019f386031f1f 0x5b400cf9c3018f8f

def z216 : W := mkw 0xa1edde000f934000 0x50f6ef0007c9a000 0x61fffe0006030001 0xb0ffff0003018000

def z217 : W := mkw 0x1587bb77af175756 0x0ac3ddbbd78babab 0xbf8ff9f38e1f1f1f 0xdfc7fcf9c70f8f8f

def z218 : W := mkw 0x1587bb77bf17777e 0x0ac3ddbbdf8bbbbf 0xff8fffffff1fffff 0xffc7ffffff8fffff

def z219 : W := mkw 0x79ffffffffa17bea 0xbcffffffffd0bdf5 0xffffffffffe3ffff 0xfffffffffff1ffff

def z220 : W := mkw 0x8001000003c9c000 0x4000800001e4e000 0x0000000001e0e000 0x0000000000f07000

def z221 : W := mkw 0x71ffffffef800000 0xb8fffffff7c00000 0xf9ffffffffe00001 0xfcfffffffff00000

def z222 : W := mkw 0x49d801a80ca01a80 0x24ec00d406500d40 0x9bf001f00ee01f01 0xcdf800f807700f80

def z223 : W := mkw 0x00254e000349c000 0x0012a70001a4e000 0xedfffe000fffe001 0xf6ffff0007fff000

def z224 : W := mkw 0x21e8d40000000000 0x10f46a0000000000 0x0170e00000000000 0x80b8700000000000

def z225 : W := mkw 0x158091210c121204 0x0ac0489086090902 0xad80f8318e1f0307 0xd6c07c18c70f8183

def z226 : W := mkw 0x040100001f17777e 0x020080000f8bbbbf 0x8e0000000f1ffffe 0x47000000078fffff

def z227 : W := mkw 0x7bffffffffecbff8 0xbdfffffffff65ffc 0xfffffffffffcfff9 0xfffffffffffe7ffc

def z228 : W := mkw 0x00170a9cb32169ea 0x000b854e5990b4f5 0xffff1fffffe3ffff 0xffff8ffffff1ffff

def z229 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x000000000100e0e0 0x0000000000807070

def z230 : W := mkw 0x00206442004c8410 0x0010322100264208 0xff70e7c209fcfc19 0xffb873e104fe7e0c

def z231 : W := mkw 0x6078448840000000 0xb03c224420000000 0x0070000000000000 0x0038000000000000

def z232 : W := mkw 0x019001a80c201a80 0x00c800d406100d40 0xdbf001fc0fe01fe1 0xedf800fe07f00ff0

def z233 : W := mkw 0x0020440000488000 0x0010220000244000 0x4070060001e0e000 0x2038030000f07000

def z234 : W := mkw 0x71de9bbda0000000 0xb8ef4dded0000000 0x51ff19fd80000001 0xa8ff8cfec0000000

def z235 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0x128f01fc06001fe0 0x094780fe03000ff0

def z236 : W := mkw 0x61fede9ce0000000 0xb0ff6f4e70000000 0x61fffe0c70000001 0xb0ffff0638000000

def z237 : W := mkw 0x158091210c121204 0x0ac0489086090902 0x0000000000000000 0x0000000000000000

def z238 : W := mkw 0x00020014a0000142 0x0001000a500000a1 0x0000003180000306 0x00000018c0000183

def z239 : W := mkw 0x5dd8b1eb0cb61e94 0x2eec58f5865b0f4a 0xbff0f9f38eff1f1f 0xdff87cf9c77f8f8f

def z240 : W := mkw 0xa06d4e0003c9c000 0x5036a70001e4e000 0xed7fe60009fce001 0xf6bff30004fe7000

def z241 : W := mkw 0x01e944000fc88000 0x00f4a20007e44000 0xedffe6000ffce001 0xf6fff30007fe7000

def z242 : W := mkw 0x17b0f5eb4c7e9e94 0x0bd87af5a63f4f4a 0x0970e1c008fc1c00 0x84b870e0047e0e00

def z243 : W := mkw 0xa06dde0003dbc000 0x5036ef0001ede000 0x647ffe0001ffe000 0x323fff0000fff000

def z244 : W := mkw 0x501021eb40000000 0xa80810f5a0000000 0x000001c000000000 0x000000e000000000

def z245 : W := mkw 0x73fefffff068a8a8 0xb9ff7ffff8345454 0x71fffffff1e0e0e1 0xb8fffffff8f07070

def z246 : W := mkw 0xb5eddf210fdbd204 0x5af6ef9087ede902 0xedfffe318fffe307 0xf6ffff18c7fff183

def z247 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x3980f9f3881c1c01 0x9cc07cf9c40e0e00

def z248 : W := mkw 0x17b7ffffff7ffffe 0x0bdbffffffbfffff 0xffffffffffffffff 0xffffffffffffffff

def z249 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0xf7fffffff603031f 0xfbfffffffb01818f

def z250 : W := mkw 0x49cf0b34bf81736a 0x24e7859a5fc0b9b5 0xf68f1e3ff703e3ff 0x7b478f1ffb81f1ff

def z251 : W := mkw 0x021020ca50242cb8 0x010810652812165c 0xbf00e1ce781c1cf9 0xdf8070e73c0e0e7c

def z252 : W := mkw 0x55dab1ff0c161614 0x2aed58ff860b0b0a 0xfffff9ff8e1f1f1f 0xfffffcffc70f8f8f

def z253 : W := mkw 0x040020420c161614 0x02001021060b0b0a 0xbf00e1c20e1f1f1f 0xdf8070e1070f8f8f

def z254 : W := mkw 0x4012009ce0000000 0xa009004e70000000 0x0000000c70000000 0x0000000638000000

def z255 : W := mkw 0x499201bc0c201bc0 0x24c900de06100de0 0x9b8001fc0e001fe1 0xcdc000fe07000ff0

def z256 : W := mkw 0x35a4ff63ec161614 0x9ad27fb1f60b0b0a 0xbf80fff3fe1f1f1f 0xdfc07ff9ff0f8f8f

def z257 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0x3600e7ce701cfcf8 0x1b0073e7380e7e7c

def z258 : W := mkw 0xa1edfe420fdfc410 0x50f6ff2107efe208 0xffffffc20ffffc19 0xffffffe107fffe0c

def z259 : W := mkw 0x1620f443505ea43c 0x0b107a21a82f521e 0x2400fe03f01fe01e 0x12007f01f80ff00f

def z260 : W := mkw 0xa024de00005bc000 0x50126f00002de000 0xed70fe0009ffe001 0xf6b87f0004fff000

def z261 : W := mkw 0x481301bc03201bc0 0x240980de01900de0 0xd28f01fc07001fe1 0x694780fe03800ff0

def z262 : W := mkw 0x02070a14b36dedfa 0x0103850a59b6f6fd 0xfe8f1e3fffffffff 0x7f478f1fffffffff

def z263 : W := mkw 0x79cf9b35af801340 0xbce7cd9ad7c009a0 0x008f183186000300 0x00478c18c3000180

def z264 : W := mkw 0x158091210c121204 0x0ac0489086090902 0xb68018338603031f 0x5b400c19c301818f

def z265 : W := mkw 0xa1efde14bfdbe16a 0x50f7ef0a5fedf0b5 0xedfffe0c7fffe0e1 0xf6ffff063ffff070

def z266 : W := mkw 0x00072a56b305657a 0x0003952b5982b2bd 0xff8fffffff1fffff 0xffc7ffffff8fffff

def z267 : W := mkw 0x0a0100001fecbff8 0x050080000ff65ffc 0x8e0000000ffcfff8 0x4700000007fe7ffc

def z268 : W := mkw 0x02374e9cf369e9ea 0x011ba74e79b4f4f5 0x407f060c71e0e0e0 0x203f830638f07070

def z269 : W := mkw 0x4a7b449c53e8a9e8 0x253da24e29f454f4 0x407f060c71e0e0e0 0x203f830638f07070

def z270 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z271 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x1b00e1f3881c1f1e 0x8d8070f9c40e0f8f

def z272 : W := mkw 0x00050a0003014000 0x000285000180a000 0x400f06000100e000 0x2007830000807000

def z273 : W := mkw 0x485b009c03a009c0 0x242d804e01d004e0 0xd2ff003c07e003e1 0x697f801e03f001f0

def z274 : W := mkw 0xf9ffffffeffbdbc0 0xfcfffffff7fdede0 0xffffffffffffffe1 0xfffffffffffffff0

def z275 : W := mkw 0x00070a14a3014000 0x0003850a5180a000 0xf48f1e3ff703e001 0x7a478f1ffb81f000

def z276 : W := mkw 0x0000900000120000 0x0000480000090000 0x2400f800001f0000 0x12007c00000f8000

def z277 : W := mkw 0x541221ffe0041614 0xaa0910fff0020b0a 0x120001fff0001f1e 0x090000fff8000f8f

def z278 : W := mkw 0xa1ecde000cda8000 0x50f66f00066d4000 0x69fffe0008fc0001 0xb4ffff00047e0000

def z279 : W := mkw 0x1400b04300160414 0x0a005821800b020a 0x0000e000001c0000 0x00007000000e0000

def z280 : W := mkw 0x1d81b1630fb61fd4 0x0ec0d8b187db0fea 0xbf80f9f38fff1fff 0xdfc07cf9c7ff8fff

def z281 : W := mkw 0x15879b35af135346 0x0ac3cd9ad789a9a3 0x008f183186030306 0x00478c18c3018183

def z282 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x400f060c70000000 0x2007830638000000

def z283 : W := mkw 0x707efedfe0000000 0xb83f7f6ff0000000 0x607ffe0ff0000000 0x303fff07f8000000

def z284 : W := mkw 0x04070a14bf17777e 0x0203850a5f8bbbbf 0xfe8f1e3fff1fffff 0x7f478f1fff8fffff

def z285 : W := mkw 0x604e0a14a0000000 0xb027050a50000000 0x000f000000000000 0x0007800000000000

def z286 : W := mkw 0x02246e42f04de43a 0x011237217826f21d 0x2400fe03f01fe01e 0x12007f01f80ff00f

def z287 : W := mkw 0x49df0bbcafa01bc0 0x24ef85de57d00de0 0xfbff1fffffe01fe1 0xfdff8ffffff00ff0

def z288 : W := mkw 0x581221ffe0201bc0 0xac0910fff0100de0 0x120001fff0001fe0 0x090000fff8000ff0

def z289 : W := mkw 0x79feffffe0201bc0 0xbcff7ffff0100de0 0x73fffffff0001fe1 0xb9fffffff8000ff0

def z290 : W := mkw 0x0000000000000000 0x0000000000000000 0xe40006000100e001 0x7200030000807000

def z291 : W := mkw 0x71eeff77e0000000 0xb8f77fbbf0000000 0x208ffe33f0000000 0x1047ff19f8000000

def z292 : W := mkw 0x21ecde0000488000 0x10f66f0000244000 0xedfffe0009fce001 0xf6ffff0004fe7000

def z293 : W := mkw 0x4bf865ea5cecbeb8 0x25fc32f52e765f5c 0xff70e7ce79fcfcf9 0xffb873e73cfe7e7c

def z294 : W := mkw 0xa1edde001fdbe16a 0x50f6ef000fedf0b5 0xeffffe000fffe3ff 0xf7ffff0007fff1ff

def z295 : W := mkw 0x02374e9cf369e9ea 0x011ba74e79b4f4f5 0xf6ff1e3ff7e3e3ff 0x7b7f8f1ffbf1f1ff

def z296 : W := mkw 0x03b0f4ca5c7eacb8 0x01d87a652e3f565c 0xfff0ffce7ffffcf9 0xfff87fe73ffffe7c

def z297 : W := mkw 0x0003001403000140 0x0001800a018000a0 0x008f003006000300 0x0047801803000180

def z298 : W := mkw 0x501221fff000216a 0xa80910fff80010b5 0x120001fff00003fe 0x090000fff80001ff

def z299 : W := mkw 0x4802013400001340 0x2401009a000009a0 0x0000003000000300 0x0000001800000180

def z300 : W := mkw 0x1180b16300040410 0x08c058b180020208 0xbf80f9f3881c1c19 0xdfc07cf9c40e0e0c

def z301 : W := mkw 0x80070a14bfdbe16a 0x4003850a5fedf0b5 0xfe8f1e3fffffe3ff 0x7f478f1ffffff1ff

def z302 : W := mkw 0xa1cd9a000f934000 0x50e6cd0007c9a000 0xe48f1e000703e001 0x72478f000381f000

def z303 : W := mkw 0x0020440000000000 0x0010220000000000 0x6170e60000000001 0xb0b8730000000000

def z304 : W := mkw 0x79ffffffe3a009c0 0xbcfffffff1d004e0 0x71fffffff1e000e1 0xb8fffffff8f00070

def z305 : W := mkw 0x20244e00e0000000 0x9012270070000000 0x0000060070000000 0x0000030038000000

def z306 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0x09fff8000eff0000 0x84fffc00077f8000

def z307 : W := mkw 0x01c990000f920000 0x00e4c80007c90000 0xedfff8000fff0001 0xf6fffc0007ff8000

def z308 : W := mkw 0x707e6fffe0000000 0xb83f37fff0000000 0x507f07fff0000000 0x283f83fff8000000

def z309 : W := mkw 0x1580b0430c160414 0x0ac05821860b020a 0xad80f8038e1f001f 0xd6c07c01c70f800f

def z310 : W := mkw 0x4a1221fe50243ff8 0x250910ff28121ffc 0x120001fe70001ff8 0x090000ff38000ffc

def z311 : W := mkw 0x31a4ff63e0000000 0x98d27fb1f0000000 0x3180fff3f0000001 0x98c07ff9f8000000

def z312 : W := mkw 0x1400b04300160414 0x0a005821800b020a 0xb680f833861f031f 0x5b407c19c30f818f

def z313 : W := mkw 0x0000204200040410 0x0000102100020208 0x120001c200001c18 0x090000e100000e0c

def z314 : W := mkw 0x00040a00b001602a 0x000205005800b015 0xb6801e33f603e31f 0x5b400f19fb01f18f

def z315 : W := mkw 0xb1edff630fdbc000 0x58f6ffb187ede000 0xfdfffff38fffe001 0xfefffff9c7fff000

def z316 : W := mkw 0xa3fdfeca4fffcc90 0x51feff6527ffe648 0xedffffc00ffffc01 0xf6ffffe007fffe00

def z317 : W := mkw 0x098101200fa01bc0 0x04c0809007d00de0 0x9b8001f00fe01fe1 0xcdc000f807f00ff0

def z318 : W := mkw 0x1586bb77ac161614 0x0ac35dbbd60b0b0a 0xff8ffffffe1f1f1f 0xffc7ffffff0f8f8f

def z319 : W := mkw 0x0000000010002028 0x0000000008001014 0x860000000100e0f8 0x430000000080707c

def z320 : W := mkw 0xa1cd9a000f934000 0x50e6cd0007c9a000 0xad8ff8000e1f0001 0xd6c7fc00070f8000

def z321 : W := mkw 0x1400b0430c161614 0x0a005821860b0b0a 0xae00f8038e1f1f1e 0x57007c01c70f8f8f

def z322 : W := mkw 0x00050a001301616a 0x000285000980b0b5 0xe68f1e000703e3ff 0x73478f000381f1ff

def z323 : W := mkw 0x018001200c001200 0x00c0009006000900 0x0080003006000300 0x0040001803000180

def z324 : W := mkw 0xa1fdde880ffbc880 0x50feef4407fde440 0xffffffcc0ffffce1 0xffffffe607fffe70

def z325 : W := mkw 0x79df9bbdafa01bc0 0xbcefcdded7d00de0 0xdbff19fd8fe01fe1 0xedff8cfec7f00ff0

def z326 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0x4970e7cc79fcfce0 0xa4b873e63cfe7e70

def z327 : W := mkw 0x607f4e9cf301616a 0xb03fa74e7980b0b5 0x407f060c7100e0e0 0x203f830638807070

def z328 : W := mkw 0x3034fecbe0000000 0x981a7f65f0000000 0x7170ffcff0000001 0xb8b87fe7f8000000

def z329 : W := mkw 0xb5a4ff630c5fd614 0x5ad27fb1862feb0a 0xbf80fff38e1fff1f 0xdfc07ff9c70fff8f

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0x240018038003001e 0x12000c01c001800f

def z331 : W := mkw 0x01cb00140f800140 0x00e5800a07c000a0 0xdbff003c0fe003e1 0xedff801e07f001f0

def z332 : W := mkw 0xa224fe42505fe438 0x51127f21282ff21c 0x2400fe02701fe018 0x12007f01380ff00c

def z333 : W := mkw 0x01c8000000000000 0x00e4000000000000 0x41ff000000000001 0xa0ff800000000000

def z334 : W := mkw 0x00070a14a3000140 0x0003850a518000a0 0xf28f1e3ff70003e1 0x79478f1ffb8001f0

def z335 : W := mkw 0x0003001403000140 0x0001800a018000a0 0x400f000c010000e0 0x2007800600800070

def z336 : W := mkw 0xb7fdffeb5ffffebc 0x5bfefff5afffff5e 0xffffffffffffffff 0xffffffffffffffff

def z337 : W := mkw 0x49db91bc0fb21bc0 0x24edc8de07d90de0 0xfffff9fc0fff1fe1 0xfffffcfe07ff8ff0

def z338 : W := mkw 0x481301bc0fa01bc0 0x240980de07d00de0 0x9a0001fc0fe01fe0 0x4d0000fe07f00ff0

def z339 : W := mkw 0x140021630c161614 0x0a0010b1860b0b0a 0x9e0001f38e1f1f1e 0x4f0000f9c70f8f8f

def z340 : W := mkw 0x71ffffffe3014000 0xb8fffffff180a000 0xf5fffffff703e001 0xfafffffffb81f000

def z341 : W := mkw 0x00376edef301616a 0x001bb76f7980b0b5 0xf7fffffff703e3ff 0xfbfffffffb81f1ff

def z342 : W := mkw 0x481001a800201a80 0x240800d400100d40 0x000001c000001c00 0x000000e000000e00

def z343 : W := mkw 0x481201bc00201bc0 0x240900de00100de0 0xdb7001fc09e01fe1 0xedb800fe04f00ff0

def z344 : W := mkw 0x75feffffe0160414 0xbaff7ffff00b020a 0x75fffffff01f001f 0xbafffffff80f800f

def z345 : W := mkw 0x02206442504ca438 0x011032212826521c 0xbf00e7c2781cfc19 0xdf8073e13c0e7e0c

def z346 : W := mkw 0xe9ffdfbcbffbfbea 0x74ffefde5ffdfdf5 0xffffffffffffffff 0xffffffffffffffff

def z347 : W := mkw 0x1580b16300041614 0x0ac058b180020b0a 0x3380f9f380001f1f 0x99c07cf9c0000f8f

def z348 : W := mkw 0xa06d4e0003c9c000 0x5036a70001e4e000 0xe4ff1e0007e3e001 0x727f8f0003f1f000

def z349 : W := mkw 0x023064ca406c8c90 0x0118326520364648 0x7970e7ce78fc1c01 0xbcb873e73c7e0e00

def z350 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0x868f18318703e3fe 0x43478c18c381f1ff

def z351 : W := mkw 0x800100000f934000 0x4000800007c9a000 0x0000000006030000 0x0000000003018000

def z352 : W := mkw 0x48170bbcb3217bea 0x240b85de5990bdf5 0xf68f1ffff703ffff 0x7b478ffffb81ffff

def z353 : W := mkw 0x0010008800200880 0x0008004400100440 0x097001c008e01c00 0x84b800e004700e00

def z354 : W := mkw 0x4858008800a00880 0x242c004400500440 0x0070000000e00000 0x0038000000700000

def z355 : W := mkw 0x71feffffec001200 0xb8ff7ffff6000900 0xfbfffffffe001f01 0xfdffffffff000f80

def z356 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0xfff0ffffffffffff 0xfff87fffffffffff

def z357 : W := mkw 0x71faf5ffe0000000 0xb8fd7afff0000000 0x1170e1fff0000000 0x88b870fff8000000

def z358 : W := mkw 0x15b0f5eb4c161614 0x0ad87af5a60b0b0a 0xfff0fffffe1f1f1f 0xfff87fffff0f8f8f

def z359 : W := mkw 0x001020ca40000000 0x0008106520000000 0x100001ce70000000 0x080000e738000000

def z360 : W := mkw 0x50172bfff301616a 0xa80b95fff980b0b5 0xf68f1ffff703e3ff 0x7b478ffffb81f1ff

def z361 : W := mkw 0xa0049a0000134000 0x50024d000009a000 0x0000180000030000 0x00000c0000018000

def z362 : W := mkw 0x1000216300000000 0x080010b180000000 0x100001f380000000 0x080000f9c0000000

def z363 : W := mkw 0x1581b1631f17777e 0x0ac0d8b18f8bbbbf 0xbf80f9f38f1fffff 0xdfc07cf9c78fffff

def z364 : W := mkw 0x0030448840000000 0x0018224420000000 0x4070060c70000000 0x2038030638000000

def z365 : W := mkw 0x0000204200040410 0x0000102100020208 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z366 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xfffffe338fffe31f 0xffffff19c7fff18f

def z367 : W := mkw 0x002044001048a028 0x0010220008245014 0xff70e60e79fce0f9 0xffb873073cfe707c

def z368 : W := mkw 0xa06f4e14b3c9e16a 0x5037a70a59e4f0b5 0x407f060c71e0e0e0 0x203f830638f07070

def z369 : W := mkw 0x023064ca406c8c90 0x0118326520364648 0xed70e7c009fcfc01 0xf6b873e004fe7e00

def z370 : W := mkw 0x523265fff06cacb8 0xa91932fff836565c 0xff70e7fff9fcfcf9 0xffb873fffcfe7e7c

def z371 : W := mkw 0x0000000000000000 0x0000000000000000 0x7000060e70000001 0x3800030738000000

def z372 : W := mkw 0x1180912100000000 0x08c0489080000000 0x0080183180000000 0x00400c18c0000000

def z373 : W := mkw 0x880100000ffbdbc0 0x4400800007fdede0 0x8e0000000fffffe0 0x4700000007fffff0

def z374 : W := mkw 0x840100000fdfd614 0x4200800007efeb0a 0x8e0000000fffff1e 0x4700000007ffff8f

def z375 : W := mkw 0x00070a14a3014142 0x0003850a5180a0a1 0x708f1e3ff6030307 0x38478f1ffb018183

def z376 : W := mkw 0x00040a00b001602a 0x000205005800b015 0x000006007000e000 0x0000030038007000

def z377 : W := mkw 0x0010008800200880 0x0008004400100440 0x120001cc00001ce0 0x090000e600000e70

def z378 : W := mkw 0xe9cf9b340f935340 0x74e7cd9a07c9a9a0 0x008f183006030300 0x00478c1803018180

def z379 : W := mkw 0x4812009c002009c0 0x2409004e001004e0 0x0000000c000000e0 0x0000000600000070

def z380 : W := mkw 0x7dffffffefb61fd4 0xbefffffff7db0fea 0xffffffffffff1fff 0xffffffffffff8fff

def z381 : W := mkw 0xe9f8d5a80cfa9a80 0x74fc6ad4067d4d40 0x0970e1c008fc1c00 0x84b870e0047e0e00

def z382 : W := mkw 0x71faf5ff40000000 0xb8fd7affa0000000 0x51ffe1fc00000001 0xa8fff0fe00000000

def z383 : W := mkw 0x0801000003a009c0 0x0400800001d004e0 0x0000000001e000e0 0x0000000000f00070

def z384 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0xe48f1e0c7703e0e1 0x72478f063b81f070

def z385 : W := mkw 0x81c900000fdbc000 0x40e4800007ede000 0xcdff00000fffe001 0xe6ff800007fff000

def z386 : W := mkw 0x060000001c7ebebc 0x030000000e3f5f5e 0x8e0000000ffffffe 0x4700000007ffffff

def z387 : W := mkw 0x820100001fffecb8 0x410080000ffff65c 0x8e0000000ffffcf8 0x4700000007fffe7c

def z388 : W := mkw 0xc9db01bc0ffbdbc0 0x64ed80de07fdede0 0xdfff01fc0fffffe1 0xefff80fe07fffff0

def z389 : W := mkw 0x00020014a0000000 0x0001000a50000000 0x1000003ff0000000 0x0800001ff8000000

def z390 : W := mkw 0xb424fe43005fc414 0x5a127f21802fe20a 0x2400fe03801fe01e 0x12007f01c00ff00f

def z391 : W := mkw 0x023364de536cadf8 0x0119b26f29b656fc 0xffffe7fe7ffcfff9 0xfffff3ff3ffe7ffc

def z392 : W := mkw 0x71cebb77a0000000 0xb8e75dbbd0000000 0x318ff9f380000001 0x98c7fcf9c0000000

def z393 : W := mkw 0xa3edde001fffecb8 0x51f6ef000ffff65c 0xeffffe000ffffcf9 0xf7ffff0007fffe7c

def z394 : W := mkw 0x00050a0013016028 0x000285000980b014 0xf68f1e0e7703e0f9 0x7b478f073b81f07c

def z395 : W := mkw 0x02304488506cacb8 0x011822442836565c 0xce70060c79fcfcf8 0x673803063cfe7e7c

def z396 : W := mkw 0x75feffffe0041614 0xbaff7ffff0020b0a 0x73fffffff0001f1f 0xb9fffffff8000f8f

def z397 : W := mkw 0x607e6edee0000000 0xb03f376f70000000 0x717fe7ce70000001 0xb8bff3e738000000

def z398 : W := mkw 0xa1eddf200fdbd200 0x50f6ef9007ede900 0xfffffff00fffff01 0xfffffff807ffff80

def z399 : W := mkw 0x5dd8b1eb0cb61e94 0x2eec58f5865b0f4a 0x0970e1c008fc1c00 0x84b870e0047e0e00

def z400 : W := mkw 0x161021eb50243ebc 0x0b0810f5a8121f5e 0x120001fff0001ffe 0x090000fff8000fff

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0xc970000009e00001 0xe4b8000004f00000

def z402 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0x248ffe00061fe000 0x1247ff00030ff000

def z403 : W := mkw 0x71fcffebe0000000 0xb8fe7ff5f0000000 0x2170ffc3f0000000 0x90b87fe1f8000000

def z404 : W := mkw 0xfdffffff0fffdfd4 0x7effffff87ffefea 0xffffffff8fffffff 0xffffffffc7ffffff

def z405 : W := mkw 0xf5ffffffefdfd614 0xfafffffff7efeb0a 0xffffffffffffff1f 0xffffffffffffff8f

def z406 : W := mkw 0xe9fbd5bc0ffa9bc0 0x74fdeade07fd4de0 0xdbffe1fc0ffc1fe1 0xedfff0fe07fe0ff0

def z407 : W := mkw 0x49db01bcbfa03bea 0x24ed80de5fd01df5 0xdbff01ffffe01fff 0xedff80fffff00fff

def z408 : W := mkw 0x21efde14b301616a 0x10f7ef0a5980b0b5 0xf7fffe3ff703e3ff 0xfbffff1ffb81f1ff

def z409 : W := mkw 0x040000000c161614 0x02000000060b0b0a 0x08000000081c1c00 0x04000000040e0e00

def z410 : W := mkw 0xa04d0a0003814000 0x5026850001c0a000 0x000f000000000000 0x0007800000000000

def z411 : W := mkw 0xa1e8d4000cda8000 0x50f46a00066d4000 0xadf0f8000eff0001 0xd6f87c00077f8000

def z412 : W := mkw 0xa020d400005a8000 0x50106a00002d4000 0x0000e000001c0000 0x00007000000e0000

def z413 : W := mkw 0x000000001000216a 0x00000000080010b5 0x02000000000003fe 0x01000000000001ff

def z414 : W := mkw 0x50162bffe0000000 0xa80b15fff0000000 0x708f1ffff0000001 0x38478ffff8000000

def z415 : W := mkw 0x71fedfbde0000000 0xb8ff6fdef0000000 0x40ff1e3df0000000 0x207f8f1ef8000000

def z416 : W := mkw 0x21cc9a0000000000 0x10e64d0000000000 0x008f180000000000 0x00478c0000000000

def z417 : W := mkw 0xa1a4de000c5bc000 0x50d26f00062de000 0xad80fe000e1fe001 0xd6c07f00070ff000

def z418 : W := mkw 0x17b0f5eb4c7e9e94 0x0bd87af5a63f4f4a 0xbff0f9f38eff1f1f 0xdff87cf9c77f8f8f

def z419 : W := mkw 0x5dcbb1770f961754 0x2ee5d8bb87cb0baa 0xbf8ff9f38e1f1f1f 0xdfc7fcf9c70f8f8f

def z420 : W := mkw 0x61fe4fbce0000000 0xb0ff27de70000000 0x51ff07fc70000001 0xa8ff83fe38000000

def z421 : W := mkw 0xb5e8f5630cde9614 0x5af47ab1866f4b0a 0x0970e1c008fc1c00 0x84b870e0047e0e00

def z422 : W := mkw 0x01870b34bf01736a 0x00c3859a5f80b9b5 0xff8f1fffff03ffff 0xffc78fffff81ffff

def z423 : W := mkw 0x80050a000fdbc000 0x4002850007ede000 0xec8f1e000fffe001 0x76478f0007fff000

def z424 : W := mkw 0x1180b1630c001200 0x08c058b186000900 0xbb80f9f38e001f01 0xddc07cf9c7000f80

def z425 : W := mkw 0x75feffffec161614 0xbaff7ffff60b0b0a 0x79fffffff81c1c01 0xbcfffffffc0e0e00

def z426 : W := mkw 0x0000204200040410 0x0000102100020208 0x0900e1c0081c1c00 0x848070e0040e0e00

def z427 : W := mkw 0x00020014b000216a 0x0001000a580010b5 0x0000000c700000e0 0x0000000638000070

def z428 : W := mkw 0xf1f8f5eb4cda8000 0xf8fc7af5a66d4000 0x0970e1c008fc0000 0x84b870e0047e0000

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x120000338000031e 0x09000019c000018f

def z430 : W := mkw 0x00050a00b301602a 0x000285005980b015 0xe48f1e03f703e01f 0x72478f01fb81f00f

def z431 : W := mkw 0x080000000ca01a80 0x0400000006500d40 0x0800000008e01c00 0x0400000004700e00

def z432 : W := mkw 0x73f8f5eb506cacb8 0xb9fc7af5a836565c 0xff70e7ce79fcfcf9 0xffb873e73cfe7e7c

def z433 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0x1b70e1ce78fc1cf8 0x8db870e73c7e0e7c

def z434 : W := mkw 0x49fb65fe4fa01bc0 0x24fdb2ff27d00de0 0xfbffe7fe7fe01fe1 0xfdfff3ff3ff00ff0

def z435 : W := mkw 0x023044885068a8a8 0x0118224428345454 0xdb7007cc79e0fce1 0xedb803e63cf07e70

def z436 : W := mkw 0x023064ca406c8c90 0x0118326520364648 0xbf70e1c208fc1c19 0xdfb870e1047e0e0c

def z437 : W := mkw 0x71fcffeb40000000 0xb8fe7ff5a0000000 0x61ffffc000000001 0xb0ffffe000000000

def z438 : W := mkw 0x02100088502028a8 0x0108004428101454 0x0000000c700000e0 0x0000000638000070

def z439 : W := mkw 0x0003001403000140 0x0001800a018000a0 0xf68f183f870303ff 0x7b478c1fc38181ff

def z440 : W := mkw 0x01879a14bf13616a 0x00c3cd0a5f89b0b5 0xff8ffe3fff1fe3ff 0xffc7ff1fff8ff1ff

def z441 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x8f00e1c00e1f1f1e 0xc78070e0070f8f8f

def z442 : W := mkw 0x040000000c161614 0x02000000060b0b0a 0xbe8018338e1f1f1f 0x5f400c19c70f8f8f

def z443 : W := mkw 0x000100000f800000 0x0000800007c00000 0x880000000fe00000 0x4400000007f00000

def z444 : W := mkw 0xa027de14b35be16a 0x5013ef0a59adf0b5 0xf68ffe3ff71fe3ff 0x7b47ff1ffb8ff1ff

def z445 : W := mkw 0xb024fe43e05bc000 0xd8127f21f02de000 0x2400fe03f01fe000 0x12007f01f80ff000

def z446 : W := mkw 0x163065eb506cbebc 0x0b1832f5a8365f5e 0xff70e7fff9fcffff 0xffb873fffcfe7fff

def z447 : W := mkw 0x0a3164ca5fecbff8 0x0518b2652ff65ffc 0xff70e7ce7ffcfff9 0xffb873e73ffe7ffc

def z448 : W := mkw 0x49db21fe0fa41fd0 0x24ed90ff07d20fe8 0xffffe1fe0ffc1ff9 0xfffff0ff07fe0ffc

def z449 : W := mkw 0x1790b1eb5c363ebc 0x0bc858f5ae1b1f5e 0xbf80f9fffe1f1fff 0xdfc07cffff0f8fff

def z450 : W := mkw 0x51da21ffe0000000 0xa8ed10fff0000000 0x51ff01fff0000001 0xa8ff80fff8000000

def z451 : W := mkw 0x1186bb77a0000000 0x08c35dbbd0000000 0x718ffffff0000001 0xb8c7fffff8000000

def z452 : W := mkw 0x5592b1ffec161614 0xaac958fff60b0b0a 0xbf80f9fffe1f1f1f 0xdfc07cffff0f8f8f

def z453 : W := mkw 0x081100880fa01bc0 0x0408804407d00de0 0xdb7001cc0fe01fe1 0xedb800e607f00ff0

def z454 : W := mkw 0x21edde000f800000 0x10f6ef0007c00000 0xe9fffe000fe00001 0xf4ffff0007f00000

def z455 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0x8f70e1c009fcfcf8 0xc7b870e004fe7e7c

def z456 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0xad80f9c00e1f1c01 0xd6c07ce0070f8e00

def z457 : W := mkw 0xa06d4e000fdbc000 0x5036a70007ede000 0xcc7f06000fffe000 0x663f830007fff000

def z458 : W := mkw 0x405a009c00000000 0x202d004e00000000 0x407f000c00000000 0x203f800600000000

def z459 : W := mkw 0x35ecff630c161614 0x1af67fb1860b0b0a 0xfffffff38e1f1f1f 0xfffffff9c70f8f8f

def z460 : W := mkw 0x5ddb91bd0fb21bc4 0x2eedc8de87d90de2 0xdbff19fd8fe31fe7 0xedff8cfec7f18ff3

def z461 : W := mkw 0x0180012000000000 0x00c0009000000000 0x118001f000000001 0x88c000f800000000

def z462 : W := mkw 0x41db01bc0f800000 0x20ed80de07c00000 0xd9ff01fc0fe00001 0xecff80fe07f00000

def z463 : W := mkw 0x41ca013400000000 0x20e5009a00000000 0x008f003000000000 0x0047801800000000

def z464 : W := mkw 0x01c901200f801200 0x00e4809007c00900 0xdbff01f00fe01f01 0xedff80f807f00f80

def z465 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xffff19ff8fe31fff 0xffff8cffc7f18fff

def z466 : W := mkw 0x5ddbb1ff0fb61fd4 0x2eedd8ff87db0fea 0xdbffe1fc0ffc1fe1 0xedfff0fe07fe0ff0

def z467 : W := mkw 0x021020ca50242cb8 0x010810652812165c 0xf60007ce7100fcf9 0x7b0003e738807e7c

def z468 : W := mkw 0x02206442506cacb8 0x011032212836565c 0xae00e60279fcfcf8 0x570073013cfe7e7c

def z469 : W := mkw 0xa1c890000c920000 0x50e4480006490000 0x0000000000000000 0x0000000000000000

def z470 : W := mkw 0x73feffffe06c8c90 0xb9ff7ffff0364648 0x79fffffff8fc1c01 0xbcfffffffc7e0e00

def z471 : W := mkw 0x5ffbf5ff5ffebffc 0x2ffdfaffafff5ffe 0xffffffffffffffff 0xffffffffffffffff

def z472 : W := mkw 0x00060a14b0002028 0x0003050a58001014 0xf68f1e3ff100e0f9 0x7b478f1ff880707c

def z473 : W := mkw 0x000000001001602a 0x000000000800b015 0x040000000003e01e 0x020000000001f00f

def z474 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0xd28f063c7700e3e1 0x6947831e3b8071f0

def z475 : W := mkw 0x02346ecaf06decba 0x011a37657836f65d 0xff70ffcff9fffcff 0xffb87fe7fcfffe7f

def z476 : W := mkw 0x023164ca536dedfa 0x0118b26529b6f6fd 0xff70e7ce7fffffff 0xffb873e73fffffff

def z477 : W := mkw 0x0000000000040410 0x0000000000020208 0x8e000000081c1c18 0x47000000040e0e0c

def z478 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0x708f1e3ff100e0e1 0x38478f1ff8807070

def z479 : W := mkw 0x023044885068a8a8 0x0118224428345454 0xed70e60c79fce0e1 0xf6b873063cfe7070

def z480 : W := mkw 0x49da01bc0ca01a80 0x24ed00de06500d40 0x59ff01fc08e01c01 0xacff80fe04700e00

def z481 : W := mkw 0x818190000fdbc000 0x40c0c80007ede000 0xad80f8000fffe001 0xd6c07c0007fff000

def z482 : W := mkw 0x00050a00b301616a 0x000285005980b0b5 0xa6001e03f703e3fe 0x53000f01fb81f1ff

def z483 : W := mkw 0x018001200c001200 0x00c0009006000900 0xbf8019f38e031f1f 0xdfc00cf9c7018f8f

def z484 : W := mkw 0x0400000000041614 0x0200000000020b0a 0x0200000000001f1e 0x0100000000000f8f

def z485 : W := mkw 0x5ddfbbffbfb77ffe 0x2eefddffdfdbbfff 0xffffffffffffffff 0xffffffffffffffff

def z486 : W := mkw 0x49cf0b34af815342 0x24e7859a57c0a9a1 0x008f183186030306 0x00478c18c3018183

def z487 : W := mkw 0x49df0bbc0fa15bc0 0x24ef85de07d0ade0 0xffff1ffc0fe3ffe1 0xffff8ffe07f1fff0

def z488 : W := mkw 0xf1feffffecda8000 0xf8ff7ffff66d4000 0x79fffffff8fc0001 0xbcfffffffc7e0000

def z489 : W := mkw 0x206c4e0000000000 0x1036270000000000 0x407f060000000000 0x203f830000000000

def z490 : W := mkw 0xe1ffdfbc0fdbc000 0x70ffefde07ede000 0xfdfffffc0fffe001 0xfefffffe07fff000

def z491 : W := mkw 0xa1efde14afdbc000 0x50f7ef0a57ede000 0xfdfffe3fffffe001 0xfeffff1ffffff000

def z492 : W := mkw 0x31ecff6300000000 0x18f67fb180000000 0x71fffff380000001 0xb8fffff9c0000000

def z493 : W := mkw 0xa068440000c88000 0x5034220000644000 0x0070000000e00000 0x0038000000700000

def z494 : W := mkw 0x00100088102028a8 0x0008004408101454 0xff7007ce79e0fcf9 0xffb803e73cf07e7c

def z495 : W := mkw 0xa0244e000049c000 0x501227000024e000 0x000006000000e000 0x0000030000007000

def z496 : W := mkw 0x71ce9b35a0000000 0xb8e74d9ad0000000 0x708f1e3ff0000001 0x38478f1ff8000000

def z497 : W := mkw 0x018090000c120000 0x00c0480006090000 0xbf80f8338e1f031f 0xdfc07c19c70f818f

def z498 : W := mkw 0x022044005048a028 0x0110220028245014 0x000006007000e000 0x0000030038007000

def z499 : W := mkw 0x00040a00b001602a 0x000205005800b015 0xf6001e0ff103e0ff 0x7b000f07f881f07f

def z500 : W := mkw 0x0800000000201bc0 0x0400000000100de0 0x0200000000001fe0 0x0100000000000ff0

def z501 : W := mkw 0x15a0f5630c5e9614 0x0ad07ab1862f4b0a 0xfff0fff38fffff1f 0xfff87ff9c7ffff8f

def z502 : W := mkw 0x1000b04300000000 0x0800582180000000 0x2000f80380000000 0x10007c01c0000000

def z503 : W := mkw 0x49db01bc1fa03be8 0x24ed80de0fd01df4 0xffff07fe7fe0fff9 0xffff83ff3ff07ffc

def z504 : W := mkw 0x73f8f5eb406c8c90 0xb9fc7af5a0364648 0x0970e1c008fc1c00 0x84b870e0047e0e00

def z505 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0x128f183ff60303fe 0x09478c1ffb0181ff

def z506 : W := mkw 0x50020135a0000000 0xa801009ad0000000 0x0000003180000000 0x00000018c0000000

def z507 : W := mkw 0x21ecde000c120000 0x10f66f0006090000 0xedfffe000e1f0001 0xf6ffff00070f8000

def z508 : W := mkw 0x79ffffffef801340 0xbcfffffff7c009a0 0x71fffffff6000301 0xb8fffffffb000180

def z509 : W := mkw 0x485f0a9cb3a169ea 0x242f854e59d0b4f5 0xf6ff1e3ff7e3e3ff 0x7b7f8f1ffbf1f1ff

def z510 : W := mkw 0x018001200c001200 0x00c0009006000900 0x090001c008001c00 0x848000e004000e00

def z511 : W := mkw 0xa1e9d4000fdbc000 0x50f4ea0007ede000 0x8d70e0000fffe000 0xc6b8700007fff000

def z512 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x417fe7cc70000000 0xa0bff3e638000000

def z513 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x2d00f9c3881f1c1e 0x96807ce1c40f8e0f

def z514 : W := mkw 0x02276e56f34de57a 0x0113b72b79a6f2bd 0xf68ffe3ff71fe3ff 0x7b47ff1ffb8ff1ff

def z515 : W := mkw 0x69ff4fbcefa01bc0 0xb4ffa7de77d00de0 0xdbff07fc7fe01fe1 0xedff83fe3ff00ff0

def z516 : W := mkw 0x00020014b000216a 0x0001000a580010b5 0xb680183ff60303ff 0x5b400c1ffb0181ff

def z517 : W := mkw 0x021220def0242dfa 0x0109106f781216fd 0x120001fff0001ffe 0x090000fff8000fff

def z518 : W := mkw 0xe9fddfa80ffbda80 0x74feefd407fded40 0xedffffc00ffffc01 0xf6ffffe007fffe00

def z519 : W := mkw 0x11b0f5eb40000000 0x08d87af5a0000000 0x71f0fffff0000001 0xb8f87ffff8000000

def z520 : W := mkw 0x1580b1631c16363c 0x0ac058b18e0b1b1e 0xff80ffffff1fffff 0xffc07fffff8fffff

def z521 : W := mkw 0x627e4e9cf068a8a8 0xb13f274e78345454 0x407f060c71e0e0e0 0x203f830638f07070

def z522 : W := mkw 0x000000000c120000 0x0000000006090000 0x8c0000000e1f0000 0x46000000070f8000

def z523 : W := mkw 0xb5cd9b210f935204 0x5ae6cd9087c9a902 0x008f183186030306 0x00478c18c3018183

def z524 : W := mkw 0x018090000c120000 0x00c0480006090000 0x0900e000081c0000 0x84807000040e0000

def z525 : W := mkw 0x0000204200040410 0x0000102100020208 0x2400e002001c0018 0x12007001000e000c

def z526 : W := mkw 0x71c8912100000000 0xb8e4489080000000 0x0000000000000000 0x0000000000000000

def z527 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x008f183180000000 0x00478c18c0000000

def z528 : W := mkw 0x02000000006c8c90 0x0100000000364648 0x0800000008fc1c00 0x04000000047e0e00

def z529 : W := mkw 0xb5efff77bfdff77e 0x5af7ffbbdfeffbbf 0xffffffffffffffff 0xffffffffffffffff

def z530 : W := mkw 0x1187bb77b301616a 0x08c3ddbbd980b0b5 0xf78ffffff703e3ff 0xfbc7fffffb81f1ff

def z531 : W := mkw 0x003064ca40200880 0x0018326520100440 0xfb70e7ce79e01ce1 0xfdb873e73cf00e70

def z532 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x0980f9f18e1f1f06 0x84c07cf8c70f8f83

def z533 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0x497f01cc09e01ce0 0xa4bf80e604f00e70

def z534 : W := mkw 0x23fcfeca506cacb8 0x11fe7f652836565c 0xffffffce79fcfcf9 0xffffffe73cfe7e7c

def z535 : W := mkw 0x71fefffff001602a 0xb8ff7ffff800b015 0x75fffffff003e01f 0xbafffffff801f00f

def z536 : W := mkw 0xf1ffffffffdbe16a 0xf8ffffffffedf0b5 0xffffffffffffe3ff 0xfffffffffffff1ff

def z537 : W := mkw 0xf1ffffffef934000 0xf8fffffff7c9a000 0x71fffffff6030001 0xb8fffffffb018000

def z538 : W := mkw 0x063064ca5c7ebebc 0x031832652e3f5f5e 0xff70e7ce7fffffff 0xffb873e73fffffff

def z539 : W := mkw 0x15c9b1630f961614 0x0ae4d8b187cb0b0a 0xfffff9f38fff1f1f 0xfffffcf9c7ff8f8f

def z540 : W := mkw 0x79fbf5ff4fa01bc0 0xbcfdfaffa7d00de0 0xdbffe1fc0fe01fe1 0xedfff0fe07f00ff0

def z541 : W := mkw 0xa27d4e8853e9e8a8 0x513ea74429f4f454 0x407f060c71e0e0e0 0x203f830638f07070

def z542 : W := mkw 0x1400216300041614 0x0a0010b180020b0a 0xbf00e1f3881c1f1f 0xdf8070f9c40e0f8f

def z543 : W := mkw 0x0049000003800000 0x0024800001c00000 0x407f000001e00000 0x203f800000f00000

def z544 : W := mkw 0xa024de00b05be02a 0x50126f00582df015 0x2400fe03f01fe01e 0x12007f01f80ff00f

def z545 : W := mkw 0x9581b1630fdfd614 0x4ac0d8b187efeb0a 0xbf80f9f38fffff1f 0xdfc07cf9c7ffff8f

def z546 : W := mkw 0x73fefffff04ca438 0xb9ff7ffff826521c 0x75fffffff01ce019 0xbafffffff80e700c

def z547 : W := mkw 0xa025de000fdbc000 0x5012ef0007ede000 0xac00fe000fffe000 0x56007f0007fff000

def z548 : W := mkw 0x023064ca504ca438 0x011832652826521c 0x7570e7ce701ce019 0xbab873e7380e700c

def z549 : W := mkw 0xa1fdfeca4fdbc000 0x50feff6527ede000 0xfdffffce7fffe001 0xfeffffe73ffff000

def z550 : W := mkw 0x0c0100000fb61fd4 0x0600800007db0fea 0x8e0000000fff1ffe 0x4700000007ff8fff

def z551 : W := mkw 0x69ffdfbc0fa01bc0 0x34ffefde07d00de0 0xfbfffffc0fe01fe1 0xfdfffffe07f00ff0

def z552 : W := mkw 0x00060a14b000216a 0x0003050a580010b5 0x728f1e3ff00003ff 0x39478f1ff80001ff

def z553 : W := mkw 0x01859a000f134000 0x00c2cd000789a000 0xed8ffe000f1fe001 0xf6c7ff00078ff000

def z554 : W := mkw 0x61fedfbc00000000 0x30ff6fde00000000 0x71fffffc00000001 0xb8fffffe00000000

def z555 : W := mkw 0x4ddb01bc0fb61fd4 0x26ed80de07db0fea 0xdfff01fc0fff1fff 0xefff80fe07ff8fff

def z556 : W := mkw 0x0180b0420c160410 0x00c05821060b0208 0xbf80f9c20e1f1c19 0xdfc07ce1070f8e0c

def z557 : W := mkw 0x5c1221ff00241fd4 0x2e0910ff80120fea 0x120001ff80001ffe 0x090000ffc0000fff

def z558 : W := mkw 0x003064ca40488000 0x0018326520244000 0xfd70e7ce79fce001 0xfeb873e73cfe7000

def z559 : W := mkw 0x59db21ffefa01bc0 0xaced90fff7d00de0 0xdbff01ffffe01fe1 0xedff80fffff00ff0

def z560 : W := mkw 0xa1e9d4000fda8000 0x50f4ea0007ed4000 0xc9ffe0000ffc0001 0xe4fff00007fe0000

def z561 : W := mkw 0x018090000c120000 0x00c0480006090000 0x0080180006030000 0x00400c0003018000

def z562 : W := mkw 0x00030014b300216a 0x0001800a598010b5 0xd28f003ff70003ff 0x6947801ffb8001ff

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x9280003006000301 0x4940001803000180

def z564 : W := mkw 0xa1ecde000cdbc000 0x50f66f00066de000 0x2d70fe0008ffe000 0x96b87f00047ff000

def z565 : W := mkw 0x10002043e0000000 0x88001021f0000000 0x00000003f0000000 0x00000001f8000000

def z566 : W := mkw 0x00060a14b001616a 0x0003050a5800b0b5 0x36001e3ff003e3fe 0x1b000f1ff801f1ff

def z567 : W := mkw 0x1583b1770f161754 0x0ac1d8bb878b0baa 0xff8ff9ff8f1f1fff 0xffc7fcffc78f8fff

def z568 : W := mkw 0x00040a0000000000 0x0002050000000000 0x608f1e0000000001 0x30478f0000000000

def z569 : W := mkw 0x49db01bc1fa17bea 0x24ed80de0fd0bdf5 0xdfff01fc0fe3ffff 0xefff80fe07f1ffff

def z570 : W := mkw 0x000300141301616a 0x0001800a0980b0b5 0xd68f003c0703e3ff 0x6b47801e0381f1ff

def z571 : W := mkw 0x41d801a800000000 0x20ec00d400000000 0x017001c000000000 0x80b800e000000000

def z572 : W := mkw 0x4bdb21fe5fa43ff8 0x25ed90ff2fd21ffc 0xdbff01fe7fe01ff9 0xedff80ff3ff00ffc

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x9b0001c008001c01 0xcd8000e004000e00

def z574 : W := mkw 0x02000000104ca438 0x010000000826521c 0x04000000001ce018 0x02000000000e700c

def z575 : W := mkw 0x43fa65fe506cacb8 0x21fd32ff2836565c 0xffffe7fe79fcfcf9 0xfffff3ff3cfe7e7c

def z576 : W := mkw 0x0030448800688880 0x0018224400344440 0xff70e7cc09fcfce1 0xffb873e604fe7e70

def z577 : W := mkw 0x02010000136dedfa 0x0100800009b6f6fd 0x8e0000000ffffffe 0x4700000007ffffff

def z578 : W := mkw 0x1780b1631c7ebebc 0x0bc058b18e3f5f5e 0xbf80f9f38fffffff 0xdfc07cf9c7ffffff

def z579 : W := mkw 0x0000000010002028 0x0000000008001014 0x1200000e700000f8 0x090000073800007c

def z580 : W := mkw 0x0230448840688880 0x0118224420344440 0x0070000000e00000 0x0038000000700000

def z581 : W := mkw 0x0180900000000000 0x00c0480000000000 0x2180f80000000001 0x90c07c0000000000

def z582 : W := mkw 0x158021630c041614 0x0ac010b186020b0a 0x9b8001f38e001f1f 0xcdc000f9c7000f8f

def z583 : W := mkw 0x003064ca40000000 0x0018326520000000 0x0170e1c000000000 0x80b870e000000000

def z584 : W := mkw 0xb5cdbb630f975614 0x5ae6ddb187cbab0a 0xbf8ff9f38e1f1f1f 0xdfc7fcf9c70f8f8f

def z585 : W := mkw 0x1180b1630c120000 0x08c058b186090000 0xbd80f9f38e1f0001 0xdec07cf9c70f8000

def z586 : W := mkw 0x0000000000488000 0x0000000000244000 0x8c00000009fce000 0x4600000004fe7000

def z587 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0xf60f060e7100e0f9 0x7b0783073880707c

def z588 : W := mkw 0x59dbb1ff0fa01bc0 0x2cedd8ff87d00de0 0xfbfff9ff8fe01fe1 0xfdfffcffc7f00ff0

def z589 : W := mkw 0x1404ba43b017643e 0x0a025d21d80bb21f 0x2400fe03f01fe01e 0x12007f01f80ff00f

def z590 : W := mkw 0x51dab1ff00000000 0x28ed58ff80000000 0x71fff9ff80000001 0xb8fffcffc0000000

def z591 : W := mkw 0x71ffffffe3000140 0xb8fffffff18000a0 0xf3fffffff70003e1 0xf9fffffffb8001f0

def z592 : W := mkw 0x481201bcb0203bea 0x240900de58101df5 0x120001fff0001ffe 0x090000fff8000fff

def z593 : W := mkw 0x00070a14a3014142 0x0003850a5180a0a1 0xb68f18338603031f 0x5b478c19c301818f

def z594 : W := mkw 0x1400012100001204 0x0a00009080000902 0x0000003180000306 0x00000018c0000183

def z595 : W := mkw 0x01cf0a14bf81616a 0x00e7850a5fc0b0b5 0xffff1e3fffe3e3ff 0xffff8f1ffff1f1ff

def z596 : W := mkw 0x080300140fa01bc0 0x0401800a07d00de0 0xda8f003c0fe01fe1 0x6d47801e07f00ff0

def z597 : W := mkw 0x0020644240000000 0x0010322120000000 0x2000e60270000000 0x1000730138000000

def z598 : W := mkw 0x5dcb91350f921344 0x2ee5c89a87c909a2 0x008f183186030306 0x00478c18c3018183

def z599 : W := mkw 0xe87f4e9c03e9c9c0 0x743fa74e01f4e4e0 0x407f060c01e0e0e0 0x203f830600f07070

def z600 : W := mkw 0x00050a0003014000 0x000285000180a000 0x008f180006030000 0x00478c0003018000

def z601 : W := mkw 0xa1efde140fdbc140 0x50f7ef0a07ede0a0 0xfffffe3c0fffe3e1 0xffffff1e07fff1f0

def z602 : W := mkw 0xa3f8f4ca4cfe8c90 0x51fc7a65267f4648 0x0970e1c008fc1c00 0x84b870e0047e0e00

def z603 : W := mkw 0xa1edde0003c9c000 0x50f6ef0001e4e000 0x61fffe0001e0e001 0xb0ffff0000f07000

def z604 : W := mkw 0x49d901a80fa01a80 0x24ec80d407d00d40 0xc9ff01c00fe01c01 0xe4ff80e007f00e00

def z605 : W := mkw 0x521221fff0242cb8 0xa90910fff812165c 0x120001fff0001cf8 0x090000fff8000e7c

def z606 : W := mkw 0x021020ca50242cb8 0x010810652812165c 0xdb7001ce79e01cf9 0xedb800e73cf00e7c

def z607 : W := mkw 0x02206442404c8410 0x0110322120264208 0x0000e000001c0000 0x00007000000e0000

def z608 : W := mkw 0x4bfb45bc5fe8bbe8 0x25fda2de2ff45df4 0xdbff07fc7fe0ffe1 0xedff83fe3ff07ff0

def z609 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0x527007ce71e0fcf8 0x293803e738f07e7c

def z610 : W := mkw 0x00000000b000202a 0x0000000058001015 0x00000003f000001e 0x00000001f800000f

def z611 : W := mkw 0xa3edfe425fdfe438 0x51f6ff212feff21c 0xedfffe027fffe019 0xf6ffff013ffff00c

def z612 : W := mkw 0x71cf9b35b301616a 0xb8e7cd9ad980b0b5 0xf68f1e3ff703e3ff 0x7b478f1ffb81f1ff

def z613 : W := mkw 0x018091200c121200 0x00c0489006090900 0xbf80f9f00e1f1f01 0xdfc07cf8070f8f80

def z614 : W := mkw 0xa1edde001fdbe028 0x50f6ef000fedf014 0xfffffe0e7fffe0f9 0xffffff073ffff07c

def z615 : W := mkw 0x1580b1630c121204 0x0ac058b186090902 0x3180f9f386030307 0x98c07cf9c3018183

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0xa480180006030001 0x52400c0003018000

def z617 : W := mkw 0xf3ffffffffffecb8 0xf9fffffffffff65c 0xfffffffffffffcf9 0xfffffffffffffe7c

def z618 : W := mkw 0x0000204200000000 0x0000102100000000 0x3100e1c200000001 0x988070e100000000

def z619 : W := mkw 0x503265ffe0000000 0xa81932fff0000000 0x7170e7fff0000001 0xb8b873fff8000000

def z620 : W := mkw 0x17b0f5eb5c7ebebc 0x0bd87af5ae3f5f5e 0xff70e7ce79fcfcf9 0xffb873e73cfe7e7c

def z621 : W := mkw 0x49fb45bc0fe89bc0 0x24fda2de07f44de0 0xffffe7fc0ffcffe1 0xfffff3fe07fe7ff0

def z622 : W := mkw 0x49cb01340f801340 0x24e5809a07c009a0 0x9b8f01f00e001f01 0xcdc780f807000f80

def z623 : W := mkw 0x49db01bc03a009c0 0x24ed80de01d004e0 0x51ff01fc01e000e1 0xa8ff80fe00f00070

def z624 : W := mkw 0x49df0bbcbfa17bea 0x24ef85de5fd0bdf5 0xdbff07fc7fe0ffe1 0xedff83fe3ff07ff0

def z625 : W := mkw 0x4bf865ea4cec9e90 0x25fc32f526764f48 0x0970e1c008fc1c00 0x84b870e0047e0e00

def z626 : W := mkw 0xa1cf9a14bf93616a 0x50e7cd0a5fc9b0b5 0xf68f1e3ff703e3ff 0x7b478f1ffb81f1ff

def z627 : W := mkw 0xa9edde000ffbdbc0 0x54f6ef0007fdede0 0xeffffe000fffffe1 0xf7ffff0007fffff0

def z628 : W := mkw 0x1180b16300000000 0x08c058b180000000 0x0100e1c000000000 0x808070e000000000

def z629 : W := mkw 0xf1ffffffe3c9c000 0xf8fffffff1e4e000 0x71fffffff1e0e001 0xb8fffffff8f07000

def z630 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0x248f1e33f603e31e 0x12478f19fb01f18f

def z631 : W := mkw 0xa1ed4e000fc9c000 0x50f6a70007e4e000 0xc9ff06000fe0e001 0xe4ff830007f07000

def z632 : W := mkw 0x02172adef3256dfa 0x010b956f7992b6fd 0xf68f1ffff703ffff 0x7b478ffffb81ffff

def z633 : W := mkw 0x0020440000488000 0x0010220000244000 0x2400e600001ce000 0x12007300000e7000

def z634 : W := mkw 0x75ce9b35ac121204 0xbae74d9ad6090902 0x008f183186030306 0x00478c18c3018183

def z635 : W := mkw 0x71f8f5eb40000000 0xb8fc7af5a0000000 0x7170e7ce70000001 0xb8b873e738000000

def z636 : W := mkw 0x79f8f5eb4ca01a80 0xbcfc7af5a6500d40 0x0970e1c008e01c00 0x84b870e004700e00

def z637 : W := mkw 0x4a3265fe506cbff8 0x251932ff28365ffc 0xff70e7fe79fcfff9 0xffb873ff3cfe7ffc

def z638 : W := mkw 0x023264def06cadfa 0x0119326f783656fd 0xff70e7fff9fcffff 0xffb873fffcfe7fff

def z639 : W := mkw 0x00070a14a3014142 0x0003850a5180a0a1 0x000f000000000000 0x0007800000000000

def z640 : W := mkw 0xf1efdf35afdbc000 0xf8f7ef9ad7ede000 0xedfffe318fffe001 0xf6ffff18c7fff000

def z641 : W := mkw 0x00070a14a3014142 0x0003850a5180a0a1 0xd28f183d870303e7 0x69478c1ec38181f3

def z642 : W := mkw 0x080100000f801340 0x0400800007c009a0 0x0000000006000300 0x0000000003000180

def z643 : W := mkw 0x49db01bc0f801340 0x24ed80de07c009a0 0x51ff01fc06000301 0xa8ff80fe03000180

def z644 : W := mkw 0x018000000c000000 0x00c0000006000000 0x898000000e000001 0xc4c0000007000000

def z645 : W := mkw 0xa1cd9a000f934000 0x50e6cd0007c9a000 0xc9ff18000fe30001 0xe4ff8c0007f18000

def z646 : W := mkw 0x00060a14b001602a 0x0003050a5800b015 0x748f1e3ff003e01f 0x3a478f1ff801f00f

def z647 : W := mkw 0x02100088106cacb8 0x010800440836565c 0xdf7001cc09fcfcf9 0xefb800e604fe7e7c

def z648 : W := mkw 0xa234feca507fecb8 0x511a7f65283ff65c 0xff70ffce79fffcf9 0xffb87fe73cfffe7c

def z649 : W := mkw 0x1180b16300000000 0x08c058b180000000 0xb780f9f38603031f 0xdbc07cf9c301818f

def z650 : W := mkw 0x80000000005bc000 0x40000000002de000 0x04000000001fe000 0x02000000000ff000

def z651 : W := mkw 0x03f964ca5fecacb8 0x01fcb2652ff6565c 0xffffe7ce7ffcfcf9 0xfffff3e73ffe7e7c

def z652 : W := mkw 0x41db01bc03000140 0x20ed80de018000a0 0xd3ff01fc070003e1 0xe9ff80fe038001f0

def z653 : W := mkw 0x15879b35bf13736e 0x0ac3cd9adf89b9b7 0xf68f1e3ff703e3ff 0x7b478f1ffb81f1ff

def z654 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0xc60f060c7703e3fe 0x630783063b81f1ff

def z655 : W := mkw 0x1580b16300160414 0x0ac058b1800b020a 0x3580f9f3801f001f 0x9ac07cf9c00f800f

def z656 : W := mkw 0xa3fdde885ffbe8a8 0x51feef442ffdf454 0xedfffe0c7fffe0e1 0xf6ffff063ffff070

def z657 : W := mkw 0x71eedf35a0000000 0xb8f76f9ad0000000 0x61fffe3180000001 0xb0ffff18c0000000

def z658 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0x6470e60e71fce0f8 0x3238730738fe707c

def z659 : W := mkw 0x1400204300040414 0x0a0010218002020a 0x000000038000001e 0x00000001c000000f

def z660 : W := mkw 0xa06f4e14b3c9e16a 0x5037a70a59e4f0b5 0xf6ff1e3ff7e3e3ff 0x7b7f8f1ffbf1f1ff

def z661 : W := mkw 0x0001000003000000 0x0000800001800000 0xc08f000007000001 0x6047800003800000

def z662 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0x640f1e0ff103e0fe 0x32078f07f881f07f

def z663 : W := mkw 0x00040a0000014000 0x000205000000a000 0x24001e000003e000 0x12000f000001f000

def z664 : W := mkw 0x1582b177bc16377e 0x0ac158bbde0b1bbf 0xbf80f9fffe1f1fff 0xdfc07cffff0f8fff

def z665 : W := mkw 0x023064ca50242cb8 0x011832652812165c 0x7370e7ce70001cf9 0xb9b873e738000e7c

def z666 : W := mkw 0x73fffffff36dedfa 0xb9fffffff9b6f6fd 0xffffffffffffffff 0xffffffffffffffff

def z667 : W := mkw 0x02000000106cacb8 0x010000000836565c 0xfe00060e79fcfcf9 0x7f0003073cfe7e7c

def z668 : W := mkw 0x1585bb630f175614 0x0ac2ddb1878bab0a 0xff8ffff38f1fff1f 0xffc7fff9c78fff8f

def z669 : W := mkw 0x0003001413002168 0x0001800a098010b4 0xf68f063e7700e3f9 0x7b47831f3b8071fc

def z670 : W := mkw 0x4a7b64de53ecadf8 0x253db26f29f656fc 0xff7fe7ce79fcfcf9 0xffbff3e73cfe7e7c

def z671 : W := mkw 0x1400b16300161614 0x0a0058b1800b0b0a 0x3600f9f3801f1f1e 0x1b007cf9c00f8f8f

def z672 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0x2d70e7c278fcfc18 0x96b873e13c7e7e0c

def z673 : W := mkw 0xb5edfe430fdfc414 0x5af6ff2187efe20a 0xedfffe038fffe01f 0xf6ffff01c7fff00f

def z674 : W := mkw 0x09c900000fa01bc0 0x04e4800007d00de0 0xcbff00000fe01fe1 0xe5ff800007f00ff0

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0xb600000200000019 0x5b0000010000000c

def z676 : W := mkw 0x0200204250042438 0x010010212802121c 0x0000000270000018 0x000000013800000c

def z677 : W := mkw 0x75cebb77ac161614 0xbae75dbbd60b0b0a 0xbf8ff9f38e1f1f1f 0xdfc7fcf9c70f8f8f

def z678 : W := mkw 0xa025de00035bc000 0x5012ef0001ade000 0xe48ffe00071fe001 0x7247ff00038ff000

def z679 : W := mkw 0x73fefffff0242cb8 0xb9ff7ffff812165c 0x73fffffff0001cf9 0xb9fffffff8000e7c

def z680 : W := mkw 0x14072b77b305777e 0x0a0395bbd982bbbf 0xf68f1ffff703ffff 0x7b478ffffb81ffff

def z681 : W := mkw 0x49c801200c801200 0x24e4009006400900 0x0000000000000000 0x0000000000000000

def z682 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x2480f833861f031e 0x12407c19c30f818f

def z683 : W := mkw 0x49da01bc00201bc0 0x24ed00de00100de0 0x53ff01fc00001fe1 0xa9ff80fe00000ff0

def z684 : W := mkw 0x802144000fdbc000 0x4010a20007ede000 0xed70e6000fffe001 0xf6b8730007fff000

def z685 : W := mkw 0x023064ca406c8c90 0x0118326520364648 0xdb70e1cc09fc1ce1 0xedb870e604fe0e70

def z686 : W := mkw 0x01c800000c800000 0x00e4000006400000 0x0970000008e00000 0x84b8000004700000

def z687 : W := mkw 0xe9ff4fbc0fe9dbc0 0x74ffa7de07f4ede0 0xdbff07fc0fe0ffe1 0xedff83fe07f07ff0

def z688 : W := mkw 0x4bfb65fe4fec9fd0 0x25fdb2ff27f64fe8 0xdbffe1fc0ffc1fe1 0xedfff0fe07fe0ff0

def z689 : W := mkw 0x03b065ea5c6cbeb8 0x01d832f52e365f5c 0xfff0e7fe7ffcfff9 0xfff873ff3ffe7ffc

def z690 : W := mkw 0x023064ca5068a8a8 0x0118326528345454 0x7170e7ce71e0e0e1 0xb8b873e738f07070

def z691 : W := mkw 0x3020f44340000000 0x98107a21a0000000 0x0000e00000000000 0x0000700000000000

def z692 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0x408f1e3df703e3e6 0x20478f1efb81f1f3

def z693 : W := mkw 0x158091210c121204 0x0ac0489086090902 0x9b8019f18e031f07 0xcdc00cf8c7018f83

def z694 : W := mkw 0x0200000010242cb8 0x010000000812165c 0x0200000000001cf8 0x0100000000000e7c

def z695 : W := mkw 0x00274e14b349e16a 0x0013a70a59a4f0b5 0xfffffe3fffffe3ff 0xffffff1ffffff1ff

def z696 : W := mkw 0xb5edff630fdfd614 0x5af6ffb187efeb0a 0xedffffc00ffffc01 0xf6ffffe007fffe00

def z697 : W := mkw 0x000100001301616a 0x000080000980b0b5 0xf600060e7703e3ff 0x7b0003073b81f1ff

def z698 : W := mkw 0xe9df9bbc0fb35bc0 0x74efcdde07d9ade0 0xdbff19fc0fe31fe1 0xedff8cfe07f18ff0

def z699 : W := mkw 0xa1ecde00005bc000 0x50f66f00002de000 0x65fffe00001fe001 0xb2ffff00000ff000

def z700 : W := mkw 0x5d92b1ff0c361fd4 0x2ec958ff861b0fea 0xbf80f9ff8e1f1fff 0xdfc07cffc70f8fff

def z701 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x01fff9f180000000 0x80fffcf8c0000000

def z702 : W := mkw 0xa1cf9a14af934142 0x50e7cd0a57c9a0a1 0x008f183186030306 0x00478c18c3018183

def z703 : W := mkw 0x3027fe57f301616a 0x9813ff2bf980b0b5 0xf68ffe3ff703e3ff 0x7b47ff1ffb81f1ff

def z704 : W := mkw 0x00040a00a0014002 0x000205005000a001 0x0000180180030006 0x00000c00c0018003

def z705 : W := mkw 0x058090000c161614 0x02c04800060b0b0a 0xaf80f8000e1f1f1f 0xd7c07c00070f8f8f

def z706 : W := mkw 0xf1fdffeb4fdbc000 0xf8fefff5a7ede000 0xedffffc00fffe001 0xf6ffffe007fff000

def z707 : W := mkw 0xf1feffffecdbc000 0xf8ff7ffff66de000 0x7dfffffff8ffe001 0xbefffffffc7ff000

def z708 : W := mkw 0x098101201fa17bea 0x04c080900fd0bdf5 0xbf8019f38fe3ffff 0xdfc00cf9c7f1ffff

def z709 : W := mkw 0x003264de40000000 0x0019326f20000000 0x71ffe7fe70000001 0xb8fff3ff38000000

def z710 : W := mkw 0x7dfeffffecb61e94 0xbeff7ffff65b0f4a 0xfffffffffeff1f1f 0xffffffffff7f8f8f

def z711 : W := mkw 0x73ce9b35b06cacb8 0xb9e74d9ad836565c 0x8e8f183189fcfcf8 0x47478c18c4fe7e7c

def z712 : W := mkw 0x51da21ffe0000000 0xa8ed10fff0000000 0x108f01fff0000000 0x084780fff8000000

def z713 : W := mkw 0x75feffffe0161614 0xbaff7ffff00b0b0a 0x77fffffff01f1f1f 0xbbfffffff80f8f8f

def z714 : W := mkw 0xf1feffffecda8000 0xf8ff7ffff66d4000 0xfdfffffffeff0001 0xfeffffffff7f8000

def z715 : W := mkw 0x40160a9ce0000000 0xa00b054e70000000 0x708f1e3ff0000001 0x38478f1ff8000000

def z716 : W := mkw 0x607e4e9ce0000000 0xb03f274e70000000 0x507f063ff0000000 0x283f831ff8000000

def z717 : W := mkw 0x31ecff63e0000000 0x98f67fb1f0000000 0x71fffff3f0000001 0xb8fffff9f8000000

def z718 : W := mkw 0xe836dfbc007bdbc0 0x741b6fde003dede0 0x3600fffc001fffe0 0x1b007ffe000ffff0

def z719 : W := mkw 0x0012009c00200880 0x0009004e00100440 0xdbff01fc09e01ce1 0xedff80fe04f00e70

def z720 : W := mkw 0x75feffffe0041614 0xbaff7ffff0020b0a 0xf7fffffff6031f1f 0xfbfffffffb018f8f

def z721 : W := mkw 0x485b01bc03a01bc0 0x242d80de01d00de0 0x407f01cc01e01ce0 0x203f80e600f00e70

def z722 : W := mkw 0x17b0d5a95c7abaac 0x0bd86ad4ae3d5d56 0x40f01e3df7e3e3e6 0x20780f1efbf1f1f3

def z723 : W := mkw 0x647e4e9cec161614 0xb23f274e760b0b0a 0xce7f060c7e1f1f1e 0x673f83063f0f8f8f

def z724 : W := mkw 0x41de0bbcac001200 0x20ef05de56000900 0xffff1ffffe031f1f 0xffff8fffff018f8f

def z725 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0xf3fffffff10000e1 0xf9fffffff8800070

def z726 : W := mkw 0x687e4e9ce0a00880 0xb43f274e70500440 0x407f060c70e00000 0x203f830638700000

def z727 : W := mkw 0x0c0100001fb77ffe 0x060080000fdbbfff 0x8e0000000ffffffe 0x4700000007ffffff

def z728 : W := mkw 0xa1edde00efdbc000 0xd0f6ef0077ede000 0xedfffe007fffe001 0xf6ffff003ffff000

def z729 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0xf7fffffff0000019 0xfbfffffff800000c

def z730 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0xcf70e7cc79fcfcf8 0xe7b873e63cfe7e7c

def z731 : W := mkw 0x020100001369e9ea 0x0100800009b4f4f5 0x8600000007e3e3fe 0x4300000003f1f1ff

def z732 : W := mkw 0x2224fe42504ca438 0x11127f212826521c 0x2400fe02701ce018 0x12007f01380e700c

def z733 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0xf5fffffff100e001 0xfafffffff8807000

def z734 : W := mkw 0x707e4fbde0000000 0xb83f27def0000000 0x407f063df0000000 0x203f831ef8000000

def z735 : W := mkw 0xf9cf9b35af935340 0xfce7cd9ad7c9a9a0 0x008f183186030300 0x00478c18c3018180

def z736 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xffffffc00ffffc01 0xffffffe007fffe00

def z737 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xfffffe300fffe301 0xffffff1807fff180

def z738 : W := mkw 0x02012042136dedfa 0x0100902109b6f6fd 0xbf80f9f38fffffff 0xdfc07cf9c7ffffff

def z739 : W := mkw 0x1006ba57a0000000 0x08035d2bd0000000 0x708ffe3ff0000001 0x3847ff1ff8000000

def z740 : W := mkw 0x49da01bc0ca01bc0 0x24ed00de06500de0 0x5bff01fc08e01fe1 0xadff80fe04700ff0

def z741 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xfdfffe0e7fffe001 0xfeffff073ffff000

def z742 : W := mkw 0x75feffffec161614 0xbaff7ffff60b0b0a 0xfdfffffffe1f1c01 0xfeffffffff0f8e00

def z743 : W := mkw 0x71feffffe0000142 0xb8ff7ffff00000a1 0x71fffffff0000307 0xb8fffffff8000183

def z744 : W := mkw 0x1587bb77bf17777e 0x0ac3ddbbdf8bbbbf 0x490fe7cc791cfce0 0xa487f3e63c8e7e70

def z745 : W := mkw 0x0011008803200880 0x0008804401900440 0xdbff01cc0fe01ce1 0xedff80e607f00e70

def z746 : W := mkw 0x02246e42504de438 0x011237212826f21c 0x2400fe02701fe018 0x12007f01380ff00c

def z747 : W := mkw 0x75feffffec361e94 0xbaff7ffff61b0f4a 0xffffffffffff1fff 0xffffffffffff8fff

def z748 : W := mkw 0x8201000013edecb8 0x4100800009f6f65c 0x8e00000009fcfcf8 0x4700000004fe7e7c

def z749 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x75fffffff003001f 0xbafffffff801800f

def z750 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xffffe1fc0ffc1fe1 0xfffff0fe07fe0ff0

def z751 : W := mkw 0x75feffffe0160414 0xbaff7ffff00b020a 0xfffffffff81f1c1f 0xfffffffffc0f8e0f

def z752 : W := mkw 0x00162adee0000000 0x000b156f70000000 0x708f1ffff0000001 0x38478ffff8000000

def z753 : W := mkw 0x71feffffe0001200 0xb8ff7ffff0000900 0x73fffffff0001f01 0xb9fffffff8000f80

def z754 : W := mkw 0x11869b35a0000000 0x08c34d9ad0000000 0x708f1e3ff0000001 0x38478f1ff8000000

def z755 : W := mkw 0x000300141301616a 0x0001800a0980b0b5 0x9600003c0703e3fe 0x4b00001e0381f1ff

def z756 : W := mkw 0x607e4e9ce0488000 0xb03f274e70244000 0xed7fe60c79fce001 0xf6bff3063cfe7000

def z757 : W := mkw 0x51de2bffe0000000 0xa8ef15fff0000000 0x71ff1ffff0000001 0xb8ff8ffff8000000

def z758 : W := mkw 0xd01321ffefdbc000 0xe80990fff7ede000 0x9c0001ffffffe000 0x4e0000fffffff000

def z759 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xdbff19fd8fe31fe7 0xedff8cfec7f18ff3

def z760 : W := mkw 0x01869a14a0000000 0x00c34d0a50000000 0x718ffe3ff0000001 0xb8c7ff1ff8000000

def z761 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x728f1e3ff000031f 0x39478f1ff800018f

def z762 : W := mkw 0x71eedf35a0000000 0xb8f76f9ad0000000 0x71fffe3ff0000001 0xb8ffff1ff8000000

def z763 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0xfff0ffce7ffffcf9 0xfff87fe73ffffe7c

def z764 : W := mkw 0x61fe4fbce0000000 0xb0ff27de70000000 0x71ff1ffff0000001 0xb8ff8ffff8000000

def z765 : W := mkw 0x607e4e9ce0200880 0xb03f274e70100440 0x407f060c71e000e0 0x203f830638f00070

def z766 : W := mkw 0x023164ca536dedfa 0x0118b26529b6f6fd 0x8f70e1c00ffffffe 0xc7b870e007ffffff

def z767 : W := mkw 0x71ce9b35a0000000 0xb8e74d9ad0000000 0x408f1e3df0000000 0x20478f1ef8000000

def z768 : W := mkw 0x00060a14a0000142 0x0003050a500000a1 0x708f1e3ff0000307 0x38478f1ff8000183

def z769 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x020000000100e3fe 0x01000000008071ff

def z770 : W := mkw 0xf1feffffe0c88000 0xf8ff7ffff0644000 0x71fffffff0e00001 0xb8fffffff8700000

def z771 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xcb7f01cc0fe01fe0 0xe5bf80e607f00ff0

def z772 : W := mkw 0x71faf5ffe0000000 0xb8fd7afff0000000 0x51ffe1fff0000001 0xa8fff0fff8000000

def z773 : W := mkw 0xa1ed4e000fc9c000 0x50f6a70007e4e000 0xedffe6000ffce001 0xf6fff30007fe7000

def z774 : W := mkw 0xa5edde000fdbd204 0x52f6ef0007ede902 0xedfffe000fffe307 0xf6ffff0007fff183

def z775 : W := mkw 0xb46d6f6303cdd614 0x5a36b7b181e6eb0a 0x527f07f381e0ff1e 0x293f83f9c0f07f8f

def z776 : W := mkw 0x00040a0000000000 0x0002050000000000 0x708f1e0e70000001 0x38478f0738000000

def z777 : W := mkw 0x0201000013256dfa 0x010080000992b6fd 0x860000000703fffe 0x430000000381ffff

def z778 : W := mkw 0x81c990000fdbc000 0x40e4c80007ede000 0xedfff8000fffe001 0xf6fffc0007fff000

def z779 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0x59ff01fc09e01ce1 0xacff80fe04f00e70

def z780 : W := mkw 0x02376edee36dcdd2 0x011bb76f71b6e6e9 0x09fff9f18eff1f06 0x84fffcf8c77f8f83

def z781 : W := mkw 0x800100001f93616a 0x400080000fc9b0b5 0x860000000703e3fe 0x430000000381f1ff

def z782 : W := mkw 0x747efedfe0160414 0xba3f7f6ff00b020a 0x647ffe0ff01f001e 0x323fff07f80f800f

def z783 : W := mkw 0xf1feffffec5bc000 0xf8ff7ffff62de000 0xfdfffffffe1fe001 0xfeffffffff0ff000

def z784 : W := mkw 0x41da01bc0c201a80 0x20ed00de06100d40 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z785 : W := mkw 0x4beb65765fccb778 0x25f5b2bb2fe65bbc 0x248fe632761ce318 0x1247f3193b0e718c

def z786 : W := mkw 0x21ecde000c5a8000 0x10f66f00062d4000 0xedfffe000fffe001 0xf6ffff0007fff000

def z787 : W := mkw 0x71feffffec120000 0xb8ff7ffff6090000 0x71fffffff6030001 0xb8fffffffb018000

def z788 : W := mkw 0x407a449c40000000 0x203d224e20000000 0x407f060c70000000 0x203f830638000000

def z789 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0x6d70e7ce79fcfcf8 0xb6b873e73cfe7e7c

def z790 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x717fe7ce70000001 0xb8bff3e738000000

def z791 : W := mkw 0x31fcfecbe0000000 0x98fe7f65f0000000 0x71ffffcff0000001 0xb8ffffe7f8000000

def z792 : W := mkw 0x21ecde0000000000 0x10f66f0000000000 0x71fffe0e70000001 0xb8ffff0738000000

def z793 : W := mkw 0x018101201f01736a 0x00c080900f80b9b5 0x9f8001f00f03ffff 0xcfc000f80781ffff

def z794 : W := mkw 0xa06d4e000fdbc000 0x5036a70007ede000 0xed7fe6000fffe001 0xf6bff30007fff000

def z795 : W := mkw 0x4ddb01bc0fb21bc4 0x26ed80de07d90de2 0xdbff01fc0fe31fe7 0xedff80fe07f18ff3

def z796 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xfffffe020fffe019 0xffffff0107fff00c

def z797 : W := mkw 0x0180b0420c160410 0x00c05821060b0208 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z798 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xed7fe60009fce001 0xf6bff30004fe7000

def z799 : W := mkw 0x1581b1631f17777e 0x0ac0d8b18f8bbbbf 0x8f00e1c00f1ffffe 0xc78070e0078fffff

def z800 : W := mkw 0xb624fe43505fe43c 0x5b127f21a82ff21e 0x2400fe03f01fe01e 0x12007f01f80ff00f

def z801 : W := mkw 0x5ddb91bd0fb21bc4 0x2eedc8de87d90de2 0xfffff9fd8fff1fe7 0xfffffcfec7ff8ff3

def z802 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x41fffffdf0000000 0xa0fffffef8000000

def z803 : W := mkw 0x71feffffe0000140 0xb8ff7ffff00000a0 0x73fffffff00003e1 0xb9fffffff80001f0

def z804 : W := mkw 0x7036ffffe0000000 0xb81b7ffff0000000 0x708ffffff0000001 0x3847fffff8000000

def z805 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0x8dfff8000fffe000 0xc6fffc0007fff000

def z806 : W := mkw 0x4bf965ea5fecbff8 0x25fcb2f52ff65ffc 0x8f70e1c00ffcfff8 0xc7b870e007fe7ffc

def z807 : W := mkw 0x35ecff63ec161614 0x9af67fb1f60b0b0a 0xfffffff3fe1f1f1f 0xfffffff9ff0f8f8f

def z808 : W := mkw 0x8381b0421fffecb8 0x41c0d8210ffff65c 0xbf80f9c20ffffcf9 0xdfc07ce107fffe7c

def z809 : W := mkw 0x00364e9ce0000000 0x001b274e70000000 0x70ff1e3ff0000001 0x387f8f1ff8000000

def z810 : W := mkw 0x607ede9ce0000000 0xb03f6f4e70000000 0x607ffe0c70000000 0x303fff0638000000

def z811 : W := mkw 0x5dcf9b35af935346 0x2ee7cd9ad7c9a9a3 0x008f183186030306 0x00478c18c3018183

def z812 : W := mkw 0x481301bc03201bc0 0x240980de01900de0 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z813 : W := mkw 0x3036fedfe0000000 0x981b7f6ff0000000 0x71fffffff0000001 0xb8fffffff8000000

def z814 : W := mkw 0x020100001369e9ea 0x0100800009b4f4f5 0x0000000001e0e0e0 0x0000000000f07070

def z815 : W := mkw 0xa06d4e0003c9c000 0x5036a70001e4e000 0x497fe60009fce000 0xa4bff30004fe7000

def z816 : W := mkw 0xc9db01bc0fb35bc0 0x64ed80de07d9ade0 0xdbff01fc0fe31fe1 0xedff80fe07f18ff0

def z817 : W := mkw 0x000100001301616a 0x000080000980b0b5 0xe60006000703e3ff 0x730003000381f1ff

def z818 : W := mkw 0x003064ca40688880 0x0018326520344440 0xff70e7ce79fcfce1 0xffb873e73cfe7e70

def z819 : W := mkw 0xf1feffffe0134000 0xf8ff7ffff009a000 0x71fffffff0030001 0xb8fffffff8018000

def z820 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x500f063ff0000000 0x2807831ff8000000

def z821 : W := mkw 0x40160a9ce0000000 0xa00b054e70000000 0x400f060c70000000 0x2007830638000000

def z822 : W := mkw 0x0e0100001ffebffc 0x070080000fff5ffe 0x8e0000000ffffffe 0x4700000007ffffff

def z823 : W := mkw 0x7dfeffffecb61e94 0xbeff7ffff65b0f4a 0x79fffffff8fc1c01 0xbcfffffffc7e0e00

def z824 : W := mkw 0x00254e000349c000 0x0012a70001a4e000 0xed7fe60009fce001 0xf6bff30004fe7000

def z825 : W := mkw 0xa1e9d4000fdbc000 0x50f4ea0007ede000 0xcdffe0000fffe001 0xe6fff00007fff000

def z826 : W := mkw 0x3024fe43e0000000 0x98127f21f0000000 0x608ffe03f0000001 0x3047ff01f8000000

def z827 : W := mkw 0x01d8008800200880 0x00ec004400100440 0xdbff01cc09e01ce1 0xedff80e604f00e70

def z828 : W := mkw 0x49db91bc0fb21bc0 0x24edc8de07d90de0 0xdbff19fc0fe31fe1 0xedff8cfe07f18ff0

def z829 : W := mkw 0x561221fff0243ebc 0xab0910fff8121f5e 0x120001fff0001ffe 0x090000fff8000fff

def z830 : W := mkw 0x71feffffe0488000 0xb8ff7ffff0244000 0x79fffffff8fc0001 0xbcfffffffc7e0000

def z831 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0x6d7ffe0009ffe000 0xb6bfff0004fff000

def z832 : W := mkw 0x75feffffe0041614 0xbaff7ffff0020b0a 0x71fffffff0001c01 0xb8fffffff8000e00

def z833 : W := mkw 0xf5feffffe05fc414 0xfaff7ffff02fe20a 0x75fffffff01fe01f 0xbafffffff80ff00f

def z834 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0x7970e7ce79fcfce1 0xbcb873e73cfe7e70

def z835 : W := mkw 0x51faf5ff40000000 0x28fd7affa0000000 0x71fffffff0000001 0xb8fffffff8000000

def z836 : W := mkw 0x0b8121621fecbff8 0x05c090b10ff65ffc 0xbf80e1f20ffcfff9 0xdfc070f907fe7ffc

def z837 : W := mkw 0xf1feffffe049c000 0xf8ff7ffff024e000 0x71fffffff000e001 0xb8fffffff8007000

def z838 : W := mkw 0x14062b77a0041614 0x0a0315bbd0020b0a 0x728f1ffff0001f1f 0x39478ffff8000f8f

def z839 : W := mkw 0x49db91bc0fa01bc0 0x24edc8de07d00de0 0xfbfff9fc0fe01fe1 0xfdfffcfe07f00ff0

def z840 : W := mkw 0xa1edde00afdbc000 0x50f6ef0057ede000 0xedfffe03ffffe001 0xf6ffff01fffff000

def z841 : W := mkw 0x61fede9ce0000000 0xb0ff6f4e70000000 0x417fe60c70000000 0xa0bff30638000000

def z842 : W := mkw 0x49dc0ba8bca17aaa 0x24ee05d45e50bd55 0x2d701fc3f8e3fc1e 0x96b80fe1fc71fe0f

def z843 : W := mkw 0x71f9f5eb5301616a 0xb8fcfaf5a980b0b5 0x8770e1c00703e3fe 0xc3b870e00381f1ff

def z844 : W := mkw 0x49de0bbcaca01a80 0x24ef05de56500d40 0x79ff1ffff8e01c01 0xbcff8ffffc700e00

def z845 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xfdfffe338fffe001 0xfeffff19c7fff000

def z846 : W := mkw 0x49d901a80fa01bc0 0x24ec80d407d00de0 0xcbff01c00fe01fe1 0xe5ff80e007f00ff0

def z847 : W := mkw 0x49db01bc0fb21bc0 0x24ed80de07d90de0 0xdfff01fc0fff1fe1 0xefff80fe07ff8ff0

def z848 : W := mkw 0x51dab1ffe0000000 0xa8ed58fff0000000 0x71fff9fff0000001 0xb8fffcfff8000000

def z849 : W := mkw 0x707e6edfe0000000 0xb83f376ff0000000 0x407f060ff0000000 0x203f8307f8000000

def z850 : W := mkw 0x49db01bc03a009c0 0x24ed80de01d004e0 0xdbff01fc09e01ce1 0xedff80fe04f00e70

def z851 : W := mkw 0xf1feffffec920000 0xf8ff7ffff6490000 0x71fffffff0000001 0xb8fffffff8000000

def z852 : W := mkw 0xb5cf9b35af935346 0x5ae7cd9ad7c9a9a3 0x008f183186030306 0x00478c18c3018183

def z853 : W := mkw 0x71feffffec160410 0xb8ff7ffff60b0208 0xfffffffffe1f1c19 0xffffffffff0f8e0c

def z854 : W := mkw 0x79feffffeca01a80 0xbcff7ffff6500d40 0xfbfffffffee01f01 0xfdffffffff700f80

def z855 : W := mkw 0x000100001301616a 0x000080000980b0b5 0xb60000020703e3ff 0x5b0000010381f1ff

def z856 : W := mkw 0x11b6ffffe0000000 0x08db7ffff0000000 0x71fffffff0000001 0xb8fffffff8000000

def z857 : W := mkw 0x02246e42f04de43a 0x011237217826f21d 0x2400e602701ce018 0x12007301380e700c

def z858 : W := mkw 0xa1eddf200fdbc000 0x50f6ef9007ede000 0xfdfffff00fffe001 0xfefffff807fff000

def z859 : W := mkw 0x023044885068a8a8 0x0118224428345454 0xff70e7cc79fcfce1 0xffb873e63cfe7e70

def z860 : W := mkw 0x206c4e0000488000 0x1036270000244000 0xed7fe60009fce001 0xf6bff30004fe7000

def z861 : W := mkw 0x10062a57e0000000 0x8803152bf0000000 0x708f1e3ff0000001 0x38478f1ff8000000

def z862 : W := mkw 0x41de0bbca0000000 0x20ef05de50000000 0x51ff07fc70000001 0xa8ff83fe38000000

def z863 : W := mkw 0xa1eede14acda8000 0x50f76f0a566d4000 0x79fffe3ff8fc0001 0xbcffff1ffc7e0000

def z864 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0x5b7f01fc09e01fe0 0xadbf80fe04f00ff0

def z865 : W := mkw 0x71fedfbde0000000 0xb8ff6fdef0000000 0x70ff1e3ff0000001 0x387f8f1ff8000000

def z866 : W := mkw 0x49db01bcafa01bc0 0x24ed80de57d00de0 0xdbff01ffffe01fe1 0xedff80fffff00ff0

def z867 : W := mkw 0x607e6edee0000000 0xb03f376f70000000 0x607fe60e70000000 0x303ff30738000000

def z868 : W := mkw 0x61fe4fbcec001200 0xb0ff27de76000900 0xdbff07fc7e001f01 0xedff83fe3f000f80

def z869 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0x8bff01f00fe01fe0 0xc5ff80f807f00ff0

def z870 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x700f060e70000001 0x3807830738000000

def z871 : W := mkw 0x405a009c00200880 0x202d004e00100440 0xdb7f01cc09e01ce1 0xedbf80e604f00e70

def z872 : W := mkw 0x080100001fa03bea 0x040080000fd01df5 0x8a0000000fe01ffe 0x4500000007f00fff

def z873 : W := mkw 0xa1edde000fdbc140 0x50f6ef0007ede0a0 0xeffffe000fffe3e1 0xf7ffff0007fff1f0

def z874 : W := mkw 0x31eefe57e0000000 0x98f77f2bf0000000 0x71fffe3ff0000001 0xb8ffff1ff8000000

def z875 : W := mkw 0x71cebb77e0000000 0xb8e75dbbf0000000 0x008f1833f0000000 0x00478c19f8000000

def z876 : W := mkw 0xe07ede9ce05bc000 0xf03f6f4e702de000 0x647ffe0c701fe000 0x323fff06380ff000

def z877 : W := mkw 0x35a6ff77ec161614 0x9ad37fbbf60b0b0a 0xff8ffffffe1f1f1f 0xffc7ffffff0f8f8f

def z878 : W := mkw 0x02246e42f04ca438 0x011237217826521c 0x2400fe03f01ce018 0x12007f01f80e700c

def z879 : W := mkw 0x3825fe43efa01bc0 0x9c12ff21f7d00de0 0xaa00fe03ffe01fe0 0x55007f01fff00ff0

def z880 : W := mkw 0x71feffffec201a80 0xb8ff7ffff6100d40 0xfbffffffffe01fe1 0xfdfffffffff00ff0

def z881 : W := mkw 0x707ede9de0000000 0xb83f6f4ef0000000 0x407f1e0df0000000 0x203f8f06f8000000

def z882 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0xfbfffffff8001c01 0xfdfffffffc000e00

def z883 : W := mkw 0x49db01bc0fa15bc2 0x24ed80de07d0ade1 0xdbff01fc0fe31fe7 0xedff80fe07f18ff3

def z884 : W := mkw 0x35ecfe43ec160414 0x9af67f21f60b020a 0xedfffe03fe1f001f 0xf6ffff01ff0f800f

def z885 : W := mkw 0xa025de00035bc000 0x5012ef0001ade000 0xedfffe000fffe001 0xf6ffff0007fff000

def z886 : W := mkw 0x707effffe0000000 0xb83f7ffff0000000 0x707ffffff0000000 0x383ffffff8000000

def z887 : W := mkw 0xa3ddbaca5fb76cb8 0x51eedd652fdbb65c 0x128f19ce76031cf8 0x09478ce73b018e7c

def z888 : W := mkw 0x21ce9a14a0000000 0x10e74d0a50000000 0x708f1e3ff0000001 0x38478f1ff8000000

def z889 : W := mkw 0x604e0a14a0000000 0xb027050a50000000 0x708f1e3ff0000001 0x38478f1ff8000000

def z890 : W := mkw 0x00206442104ca438 0x001032210826521c 0xff70e7ce79fcfcf9 0xffb873e73cfe7e7c

def z891 : W := mkw 0x00062a56a0040410 0x0003152b50020208 0xff8ffffff81c1c19 0xffc7fffffc0e0e0c

def z892 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0xed70e7cc79fcfce1 0xf6b873e63cfe7e70

def z893 : W := mkw 0x083164ca4fa01bc0 0x0418b26527d00de0 0xfb70e7ce7fe01fe1 0xfdb873e73ff00ff0

def z894 : W := mkw 0x607e4fbce0000000 0xb03f27de70000000 0x507f07fc70000000 0x283f83fe38000000

def z895 : W := mkw 0x75feffffec5e9614 0xbaff7ffff62f4b0a 0xffffffffffffff1f 0xffffffffffffff8f

def z896 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x960000338703e3fe 0x4b000019c381f1ff

def z897 : W := mkw 0x21edde000349c000 0x10f6ef0001a4e000 0xedfffe000fffe001 0xf6ffff0007fff000

def z898 : W := mkw 0x421221fe50242cb8 0x210910ff2812165c 0x120001fe70001cf8 0x090000ff38000e7c

def z899 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xdbff01ff8fe01fff 0xedff80ffc7f00fff

def z900 : W := mkw 0x00060a14a0000140 0x0003050a500000a0 0x728f1e3ff00003e1 0x39478f1ff80001f0

def z901 : W := mkw 0x627e6edee06c8c90 0xb13f376f70364648 0x497fe7cc78fc1c00 0xa4bff3e63c7e0e00

def z902 : W := mkw 0x00062a56a0000000 0x0003152b50000000 0x718ffffff0000001 0xb8c7fffff8000000

def z903 : W := mkw 0x0801000013a169ea 0x0400800009d0b4f5 0x8600000007e3e3fe 0x4300000003f1f1ff

def z904 : W := mkw 0x800100001fdbe02a 0x400080000fedf015 0x8c0000000fffe01e 0x4600000007fff00f

def z905 : W := mkw 0x01860b34ac001200 0x00c3059a56000900 0xfb8f1ffffe001f01 0xfdc78fffff000f80

def z906 : W := mkw 0x22246e42f04ca438 0x911237217826521c 0x2400e602701ce018 0x12007301380e700c

def z907 : W := mkw 0x01f864ca40000000 0x00fc326520000000 0x71ffe7ce70000001 0xb8fff3e738000000

def z908 : W := mkw 0x15c8b1630c161614 0x0ae458b1860b0b0a 0xfffff9f38e1f1f1f 0xfffffcf9c70f8f8f

def z909 : W := mkw 0xe87f4e9cb3e9e9ea 0x743fa74e59f4f4f5 0x407f060c71e0e0e0 0x203f830638f07070

def z910 : W := mkw 0x51debbffa0000000 0x28ef5dffd0000000 0x71fffffff0000001 0xb8fffffff8000000

def z911 : W := mkw 0x607e4e9ce0488000 0xb03f274e70244000 0x407f060c71e0e000 0x203f830638f07000

def z912 : W := mkw 0x000120421305657a 0x000090210982b2bd 0xbf00e1c20f1fffff 0xdf8070e1078fffff

def z913 : W := mkw 0x49db009c0fa009c0 0x24ed804e07d004e0 0xdbff01cc0fe01ce1 0xedff80e607f00e70

def z914 : W := mkw 0x61fedfbca0000000 0x30ff6fde50000000 0x71fffffff0000001 0xb8fffffff8000000

def z915 : W := mkw 0x607e6edee0000000 0xb03f376f70000000 0x71fffffff0000001 0xb8fffffff8000000

def z916 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x517fe7fff0000000 0xa8bff3fff8000000

def z917 : W := mkw 0x01869a14ac120000 0x00c34d0a56090000 0xfd8ffe3ffe1f0001 0xfec7ff1fff0f8000

def z918 : W := mkw 0x71feffffe0040410 0xb8ff7ffff0020208 0x73fffffff0001c19 0xb9fffffff8000e0c

def z919 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0xf68f1e3ff0000019 0x7b478f1ff800000c

def z920 : W := mkw 0x75feffffec121204 0xbaff7ffff6090902 0xf7fffffff603031f 0xfbfffffffb01818f

def z921 : W := mkw 0x61fefffe40000000 0x30ff7fff20000000 0x71fffffe70000001 0xb8ffffff38000000

def z922 : W := mkw 0xf1feffffe05bc000 0xf8ff7ffff02de000 0xfdfffffff9ffe001 0xfefffffffcfff000

def z923 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0xf28f1e3ff6000301 0x79478f1ffb000180

def z924 : W := mkw 0x01e8440000488000 0x00f4220000244000 0xedffe60009fce001 0xf6fff30004fe7000

def z925 : W := mkw 0xa06dde0003dbc000 0x5036ef0001ede000 0x407fe60001fce000 0x203ff30000fe7000

def z926 : W := mkw 0x018190001f13616a 0x00c0c8000f89b0b5 0xaf80f8000f1fe3ff 0xd7c07c00078ff1ff

def z927 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0x64fffe0007ffe000 0x327fff0003fff000

def z928 : W := mkw 0x0a0100001fa43ff8 0x050080000fd21ffc 0x8a0000000fe01ff8 0x4500000007f00ffc

def z929 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x860000000100e0f8 0x430000000080707c

def z930 : W := mkw 0x3624fe43f05ea43c 0x9b127f21f82f521e 0x2400fe03f01fe01e 0x12007f01f80ff00f

def z931 : W := mkw 0x00060a14a0014000 0x0003050a5000a000 0x748f1e3ff003e001 0x3a478f1ff801f000

def z932 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xcd7fe6000fffe000 0xe6bff30007fff000

def z933 : W := mkw 0x607e4e9ce0000000 0xb03f274e70000000 0x50ff063c70000001 0x287f831e38000000

def z934 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x820000000700e3e0 0x41000000038071f0

def z935 : W := mkw 0x09c901200fa01bc0 0x04e4809007d00de0 0xdbff01f00fe01fe1 0xedff80f807f00ff0

def z936 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0x5b70e7ce79fcfcf8 0xadb873e73cfe7e7c

def z937 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xdb7f01cc09e01ce1 0xedbf80e604f00e70

def z938 : W := mkw 0x0003001413002168 0x0001800a098010b4 0xf68f1e3ff703e3ff 0x7b478f1ffb81f1ff

def z939 : W := mkw 0x860100001ffffebc 0x430080000fffff5e 0x8e0000000ffffffe 0x4700000007ffffff

def z940 : W := mkw 0x5c5bb0df03b60dd4 0x2e2dd86f81db06ea 0x647ff80f81ff00fe 0x323ffc07c0ff807f

def z941 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x600f1e0ff0000000 0x30078f07f8000000

def z942 : W := mkw 0x000100001f01736a 0x000080000f80b9b5 0x8e0000000f03fffe 0x470000000781ffff

def z943 : W := mkw 0x69fe4fbceca01a80 0xb4ff27de76500d40 0x497f07cc78e01c00 0xa4bf83e63c700e00

def z944 : W := mkw 0x3224fe43f04de43a 0x99127f21f826f21d 0x2400fe03f01fe01e 0x12007f01f80ff00f

def z945 : W := mkw 0xa026de14a05bc000 0x50136f0a502de000 0x748ffe3ff01fe001 0x3a47ff1ff80ff000

def z946 : W := mkw 0x706efe57e0000000 0xb8377f2bf0000000 0x200ffe03f0000000 0x1007ff01f8000000

def z947 : W := mkw 0x75eeff77ec161614 0xbaf77fbbf60b0b0a 0xbf8ffff3fe1f1f1f 0xdfc7fff9ff0f8f8f

def z948 : W := mkw 0x7dfeffffec361fd4 0xbeff7ffff61b0fea 0xfffffffffe1f1fff 0xffffffffff0f8fff

def z949 : W := mkw 0x1180b16300040410 0x08c058b180020208 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z950 : W := mkw 0x71feffffe0014002 0xb8ff7ffff000a001 0x71fffffff0030007 0xb8fffffff8018003

def z951 : W := mkw 0x4a1221fef0243ffa 0x250910ff78121ffd 0x120001fff0001ffe 0x090000fff8000fff

def z952 : W := mkw 0x21fcde8840000000 0x10fe6f4420000000 0x61fffe0c70000001 0xb0ffff0638000000

def z953 : W := mkw 0x405a009ce0000000 0xa02d004e70000000 0x407f000c70000000 0x203f800638000000

def z954 : W := mkw 0x800100001fdbe028 0x400080000fedf014 0x8e0000000fffe0f8 0x4700000007fff07c

def z955 : W := mkw 0x73feffffe04c8410 0xb9ff7ffff0264208 0x71fffffff01c0001 0xb8fffffff80e0000

def z956 : W := mkw 0x00160a9ca0200880 0x000b054e50100440 0xfbff1ffff9e01ce1 0xfdff8ffffcf00e70

def z957 : W := mkw 0x0021440003488000 0x0010a20001a44000 0xedffe6000ffce001 0xf6fff30007fe7000

def z958 : W := mkw 0xa1ecde000cdbc000 0x50f66f00066de000 0x6dfffe0008ffe001 0xb6ffff00047ff000

def z959 : W := mkw 0x8a0100001ffffff8 0x450080000ffffffc 0x8e0000000ffffff8 0x4700000007fffffc

def z960 : W := mkw 0x003044881068a8a8 0x0018224408345454 0xff70e7ce79fcfcf9 0xffb873e73cfe7e7c

def z961 : W := mkw 0x00160a9ca0000000 0x000b054e50000000 0x71ff1ffff0000001 0xb8ff8ffff8000000

def z962 : W := mkw 0x02010000134de57a 0x0100800009a6f2bd 0x86000000071fe3fe 0x43000000038ff1ff

def z963 : W := mkw 0x000100001301616a 0x000080000980b0b5 0xd600000c0703e3ff 0x6b0000060381f1ff

def z964 : W := mkw 0xf1feffffecda8000 0xf8ff7ffff66d4000 0xfdfffffff9fce001 0xfefffffffcfe7000

def z965 : W := mkw 0xa1edde000fdbd200 0x50f6ef0007ede900 0xeffffe000fffff01 0xf7ffff0007ffff80

def z966 : W := mkw 0x606e4e14e0000000 0xb037270a70000000 0x000f060070000000 0x0007830038000000

def z967 : W := mkw 0x687e4e9ce02009c0 0xb43f274e701004e0 0x407f060c700000e0 0x203f830638000070

def z968 : W := mkw 0x607e4e9ce0000000 0xb03f274e70000000 0x617fe60c70000001 0xb0bff30638000000

def z969 : W := mkw 0x79db91bd0fa01bc0 0xbcedc8de87d00de0 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z970 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xdfff01fc0fe31fff 0xefff80fe07f18fff

def z971 : W := mkw 0x00366edee0000000 0x001b376f70000000 0x717fe7ce70000001 0xb8bff3e738000000

def z972 : W := mkw 0x00264e14a0488000 0x0013270a50244000 0xfdfffe3ff9fce001 0xfeffff1ffcfe7000

def z973 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0xff8ffe3fff1fe3ff 0xffc7ff1fff8ff1ff

def z974 : W := mkw 0xb7f8f5eb4cfe9e94 0x5bfc7af5a67f4f4a 0x0970e1c008fc1c00 0x84b870e0047e0e00

def z975 : W := mkw 0x1400b04300160414 0x0a005821800b020a 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z976 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0xff80fffffe1f1f1f 0xffc07fffff0f8f8f

def z977 : W := mkw 0x75feffffec161614 0xbaff7ffff60b0b0a 0x7bfffffff81c1f1f 0xbdfffffffc0e0f8f

def z978 : W := mkw 0x0a0100001fedfffa 0x050080000ff6fffd 0x8e0000000ffffffe 0x4700000007ffffff

def z979 : W := mkw 0x5ff8f5eb4cfe9e94 0x2ffc7af5a67f4f4a 0x0970e1c008fc1c00 0x84b870e0047e0e00

def z980 : W := mkw 0x00050a001301616a 0x000285000980b0b5 0xa6001e000703e3fe 0x53000f000381f1ff

def z981 : W := mkw 0x49db01bc0fa15bc0 0x24ed80de07d0ade0 0xdfff01fc0fe3ffe1 0xefff80fe07f1fff0

def z982 : W := mkw 0x79feffffec201bc0 0xbcff7ffff6100de0 0xfbfffffffe001fe1 0xfdffffffff000ff0

def z983 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xfbff07fe7fe01fe1 0xfdff83ff3ff00ff0

def z984 : W := mkw 0x75feffffec041614 0xbaff7ffff6020b0a 0xfbfffffffe001f1f 0xfdffffffff000f8f

def z985 : W := mkw 0x15869b35ac121204 0x0ac34d9ad6090902 0x708f1e3ff6030307 0x38478f1ffb018183

def z986 : W := mkw 0x49d901a81fa17bea 0x24ec80d40fd0bdf5 0x8f7001c00fe3fffe 0xc7b800e007f1ffff

def z987 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0xf28f1e3ff10000e1 0x79478f1ff8800070

def z988 : W := mkw 0x021220def0242cb8 0x0109106f7812165c 0x120001fff0001cf8 0x090000fff8000e7c

def z989 : W := mkw 0x0001000013002168 0x00008000098010b4 0x860000000700e3f8 0x43000000038071fc

def z990 : W := mkw 0x01e9d4000fda8000 0x00f4ea0007ed4000 0xedfffe000fffe001 0xf6ffff0007fff000

def z991 : W := mkw 0x5a1221fff0243ff8 0xad0910fff8121ffc 0x120001fff0001ff8 0x090000fff8000ffc

def z992 : W := mkw 0x40160bbca0000000 0x200b05de50000000 0x708f1ffff0000001 0x38478ffff8000000

def z993 : W := mkw 0x4bfa65fe4cec9e90 0x25fd32ff26764f48 0x79ffe7fe78fc1c01 0xbcfff3ff3c7e0e00

def z994 : W := mkw 0x1401b0431317657e 0x0a00d821898bb2bf 0xa600f803871fe3fe 0x53007c01c38ff1ff

def z995 : W := mkw 0x10062b77a0000000 0x080315bbd0000000 0x708f1ffff0000001 0x38478ffff8000000

def z996 : W := mkw 0x1781b1631f7ffffe 0x0bc0d8b18fbfffff 0xbf80f9f38fffffff 0xdfc07cf9c7ffffff

def z997 : W := mkw 0x75feffffe0160414 0xbaff7ffff00b020a 0xf7fffffff61f031f 0xfbfffffffb0f818f

def z998 : W := mkw 0x5ddb01bd0fa01bc4 0x2eed80de87d00de2 0xdbff01fd8fe01fe7 0xedff80fec7f00ff3

def z999 : W := mkw 0x5196bbffe0000000 0xa8cb5dfff0000000 0x718ffffff0000001 0xb8c7fffff8000000

def z1000 : W := mkw 0x75ce9b35ac121204 0xbae74d9ad6090902 0xf68f1e3ff603031f 0x7b478f1ffb01818f

def z1001 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x11fff9fff0000000 0x88fffcfff8000000

def z1002 : W := mkw 0x71feffffe0014000 0xb8ff7ffff000a000 0x75fffffff003e001 0xbafffffff801f000

def z1003 : W := mkw 0x607e6edee0000000 0xb03f376f70000000 0x507f07ce70000000 0x283f83e738000000

def z1004 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xedfffe318fffe307 0xf6ffff18c7fff183

def z1005 : W := mkw 0x71feffffe0200880 0xb8ff7ffff0100440 0x73fffffff0001ce1 0xb9fffffff8000e70

def z1006 : W := mkw 0xe9eddf200fdbd200 0x74f6ef9007ede900 0xedfffe000fffe001 0xf6ffff0007fff000

def z1007 : W := mkw 0x01cb01340f801340 0x00e5809a07c009a0 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z1008 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0xff80fff38f1fff1f 0xffc07ff9c78fff8f

def z1009 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0xfdfffffff81c0001 0xfefffffffc0e0000

def z1010 : W := mkw 0x49db01bcafa01bc2 0x24ed80de57d00de1 0xdbff01fd8fe01fe7 0xedff80fec7f00ff3

def z1011 : W := mkw 0x21eede14a0000000 0x10f76f0a50000000 0x61fffe0c70000001 0xb0ffff0638000000

def z1012 : W := mkw 0x607e4e9ce0000000 0xb03f274e70000000 0x607f1e0ff0000000 0x303f8f07f8000000

def z1013 : W := mkw 0xa27f4e9cf3e9e9ea 0x513fa74e79f4f4f5 0x407f060c71e0e0e0 0x203f830638f07070

def z1014 : W := mkw 0x021220de50242df8 0x0109106f281216fc 0x120001fe70001ff8 0x090000ff38000ffc

def z1015 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x02000000060303fe 0x01000000030181ff

def z1016 : W := mkw 0x707e6fffe0000000 0xb83f37fff0000000 0x407f07cc70000000 0x203f83e638000000

def z1017 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0xff70ffcff9fffcff 0xffb87fe7fcfffe7f

def z1018 : W := mkw 0x15c8b1630c961614 0x0ae458b1864b0b0a 0xbff0f9f38eff1f1f 0xdff87cf9c77f8f8f

def z1019 : W := mkw 0x306cfe43e0000000 0x98367f21f0000000 0x607ffe03f0000000 0x303fff01f8000000

def z1020 : W := mkw 0x707efedfe0000000 0xb83f7f6ff0000000 0x70fffe3ff0000001 0x387fff1ff8000000

def z1021 : W := mkw 0x71debbffe0000000 0xb8ef5dfff0000000 0x318ff9fff0000001 0x98c7fcfff8000000

def z1022 : W := mkw 0x1586bb77ac161614 0x0ac35dbbd60b0b0a 0x798ffffff81c1c01 0xbcc7fffffc0e0e00

def z1023 : W := mkw 0x71debbffe0000000 0xb8ef5dfff0000000 0x51ff19fff0000001 0xa8ff8cfff8000000

def z1024 : W := mkw 0xa06dde000fdbc000 0x5036ef0007ede000 0xec7ffe000fffe000 0x763fff0007fff000

def z1025 : W := mkw 0x607e4e9ce0000000 0xb03f274e70000000 0xf6ff1e3ff603031f 0x7b7f8f1ffb01818f

def z1026 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xfbff19ff8fe01fe1 0xfdff8cffc7f00ff0

def z1027 : W := mkw 0x75feffffec121204 0xbaff7ffff6090902 0x71fffffff0000001 0xb8fffffff8000000

def z1028 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x60fffe3ff0000000 0x307fff1ff8000000

def z1029 : W := mkw 0x71feffffe0040410 0xb8ff7ffff0020208 0xfffffffffe1f1f1f 0xffffffffff0f8f8f

def z1030 : W := mkw 0x4a7f4e9cf3e9e9ea 0x253fa74e79f4f4f5 0x407f060c71e0e0e0 0x203f830638f07070

def z1031 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0xf3fffffff6000301 0xf9fffffffb000180

def z1032 : W := mkw 0x060100001f7ffffe 0x030080000fbfffff 0x8e0000000ffffffe 0x4700000007ffffff

def z1033 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0xffff1e3fffe3e3ff 0xffff8f1ffff1f1ff

def z1034 : W := mkw 0x7dfeffffe0241fd4 0xbeff7ffff0120fea 0x73fffffff0001fff 0xb9fffffff8000fff

def z1035 : W := mkw 0x000100001301616a 0x000080000980b0b5 0xa60018038703e3fe 0x53000c01c381f1ff

def z1036 : W := mkw 0x00366edee0040410 0x001b376f70020208 0xfffffffffe1f1f1f 0xffffffffff0f8f8f

def z1037 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xc9ff01cc0fe01ce1 0xe4ff80e607f00e70

def z1038 : W := mkw 0xb5c8b1630c961614 0x5ae458b1864b0b0a 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z1039 : W := mkw 0x59db01bdafa01bc0 0xaced80ded7d00de0 0xdbff01fd8fe01fe1 0xedff80fec7f00ff0

def z1040 : W := mkw 0x71feffffec001200 0xb8ff7ffff6000900 0xfffffffffe031f1f 0xffffffffff018f8f

def z1041 : W := mkw 0x019301bc0f201bc0 0x00c980de07900de0 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z1042 : W := mkw 0x41db01bc0fa00880 0x20ed80de07d00440 0xdbff01fc0fe01ce1 0xedff80fe07f00e70

def z1043 : W := mkw 0x485b01bc03a01bc0 0x242d80de01d00de0 0xdb7f01fc09e01fe1 0xedbf80fe04f00ff0

def z1044 : W := mkw 0xb5eddf210fdbd204 0x5af6ef9087ede902 0xfffffff18fffff07 0xfffffff8c7ffff83

def z1045 : W := mkw 0xa3f9f4ca5fffecb8 0x51fcfa652ffff65c 0x8f70e1c00ffffcf8 0xc7b870e007fffe7c

def z1046 : W := mkw 0x71feffffec800000 0xb8ff7ffff6400000 0x79fffffff8e00001 0xbcfffffffc700000

def z1047 : W := mkw 0x00060a14b0002028 0x0003050a58001014 0xf68f1e3ff703e3ff 0x7b478f1ffb81f1ff

def z1048 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x71fffffff6030307 0xb8fffffffb018183

def z1049 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0x368f1e3ff603e3fe 0x1b478f1ffb01f1ff

def z1050 : W := mkw 0x61fe4fbce0000000 0xb0ff27de70000000 0x40ff063c70000000 0x207f831e38000000

def z1051 : W := mkw 0x20264e14e0000000 0x9013270a70000000 0x708f1e3ff0000001 0x38478f1ff8000000

def z1052 : W := mkw 0x00010000132169ea 0x000080000990b4f5 0x8e0000000fe3fffe 0x4700000007f1ffff

def z1053 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0x49ff01fc0fe01fe0 0xa4ff80fe07f00ff0

def z1054 : W := mkw 0xa224fe42f05fe43a 0x51127f21782ff21d 0x2400fe03f01fe01e 0x12007f01f80ff00f

def z1055 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0xdb70e7cc79fcfce1 0xedb873e63cfe7e70

def z1056 : W := mkw 0x79feffffec801200 0xbcff7ffff6400900 0x71fffffff0000001 0xb8fffffff8000000

def z1057 : W := mkw 0x49da01bc0ca01a80 0x24ed00de06500d40 0xdbff01fc09e01ce1 0xedff80fe04f00e70

def z1058 : W := mkw 0x01ce0a14a0000000 0x00e7050a50000000 0x71ff1e3ff0000001 0xb8ff8f1ff8000000

def z1059 : W := mkw 0x73feffffe0688880 0xb9ff7ffff0344440 0x71fffffff0e00001 0xb8fffffff8700000

def z1060 : W := mkw 0x8001000013c9e16a 0x4000800009e4f0b5 0x8600000007e3e3fe 0x4300000003f1f1ff

def z1061 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x1b80f9f38e1f1f1e 0x8dc07cf9c70f8f8f

def z1062 : W := mkw 0x5ddb91bd0fb21bc4 0x2eedc8de87d90de2 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z1063 : W := mkw 0x01cd9a000f934000 0x00e6cd0007c9a000 0xedfffe000fffe001 0xf6ffff0007fff000

def z1064 : W := mkw 0x481301bc13217bea 0x240980de0990bdf5 0x960001fc0703fffe 0x4b0000fe0381ffff

def z1065 : W := mkw 0x54162bffe0041614 0xaa0b15fff0020b0a 0xf68f1ffff6031f1f 0x7b478ffffb018f8f

def z1066 : W := mkw 0x707e6fffe0000000 0xb83f37fff0000000 0x717fe7fff0000001 0xb8bff3fff8000000

def z1067 : W := mkw 0x41ce0b34a0000000 0x20e7059a50000000 0x708f1e3ff0000001 0x38478f1ff8000000

def z1068 : W := mkw 0x5e1221ff50243ffc 0x2f0910ffa8121ffe 0x120001fff0001ffe 0x090000fff8000fff

def z1069 : W := mkw 0x207c6eca40000000 0x103e376520000000 0x717fe7ce70000001 0xb8bff3e738000000

def z1070 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0xfff0fffff9fcfcf9 0xfff87ffffcfe7e7c

def z1071 : W := mkw 0x21fcfeca4c160410 0x10fe7f65260b0208 0xffffffce7e1f1c19 0xffffffe73f0f8e0c

def z1072 : W := mkw 0x421220def0242cb8 0xa109106f7812165c 0x120001ce70001cf8 0x090000e738000e7c

def z1073 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x8f80f9f18e1f1f1e 0xc7c07cf8c70f8f8f

def z1074 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xffff07fc0fe0ffe1 0xffff83fe07f07ff0

def z1075 : W := mkw 0x800100001fdbe16a 0x400080000fedf0b5 0x8c0000000fffe0e0 0x4600000007fff070

def z1076 : W := mkw 0x71ce9b35a0000000 0xb8e74d9ad0000000 0x108f183ff0000000 0x08478c1ff8000000

def z1077 : W := mkw 0x75feffffec121204 0xbaff7ffff6090902 0xfbfffffffe031f07 0xfdffffffff018f83

def z1078 : W := mkw 0x00050a00b301616a 0x000285005980b0b5 0x860018018703e3fe 0x43000c00c381f1ff

def z1079 : W := mkw 0xa1eddf200fdbd200 0x50f6ef9007ede900 0xedfffe300fffe301 0xf6ffff1807fff180

def z1080 : W := mkw 0x31fcffeb40000000 0x18fe7ff5a0000000 0x71fffffff0000001 0xb8fffffff8000000

def z1081 : W := mkw 0x55faf5ff4c161614 0x2afd7affa60b0b0a 0xfffffffffe1f1f1f 0xffffffffff0f8f8f

def z1082 : W := mkw 0x5ddb91bd0fb21bc4 0x2eedc8de87d90de2 0xffff19ff8fe31fff 0xffff8cffc7f18fff

def z1083 : W := mkw 0x61fede9ce0000000 0xb0ff6f4e70000000 0x40ff1e0c70000000 0x207f8f0638000000

def z1084 : W := mkw 0x080100001fa03be8 0x040080000fd01df4 0x8e0000000fe0fff8 0x4700000007f07ffc

def z1085 : W := mkw 0x75feffffec161614 0xbaff7ffff60b0b0a 0xfffffffff81c1c19 0xfffffffffc0e0e0c

def z1086 : W := mkw 0x71cebb77a0000000 0xb8e75dbbd0000000 0x718ffffff0000001 0xb8c7fffff8000000

def z1087 : W := mkw 0x71debbffe0000000 0xb8ef5dfff0000000 0x708f1ffff0000001 0x38478ffff8000000

def z1088 : W := mkw 0xb5eddf210fdbd204 0x5af6ef9087ede902 0xfffffe338fffe31f 0xffffff19c7fff18f

def z1089 : W := mkw 0x41da01bca0000000 0x20ed00de50000000 0x51ff01fff0000001 0xa8ff80fff8000000

def z1090 : W := mkw 0xa1ead414bcdaa16a 0x50f56a0a5e6d50b5 0x1b70e03ff8fc03fe 0x8db8701ffc7e01ff

def z1091 : W := mkw 0x00364e9ce0000000 0x001b274e70000000 0x407f060c70000000 0x203f830638000000

def z1092 : W := mkw 0x55dab1ffec161614 0xaaed58fff60b0b0a 0xfffff9fffe1f1f1f 0xfffffcffff0f8f8f

def z1093 : W := mkw 0x75feffffe0160414 0xbaff7ffff00b020a 0x71fffffff01c0001 0xb8fffffff80e0000

def z1094 : W := mkw 0xa1eddf200fdbd200 0x50f6ef9007ede900 0xfffffff38fffff1f 0xfffffff9c7ffff8f

def z1095 : W := mkw 0x581321ffefa01bc0 0xac0990fff7d00de0 0x9a0001ffffe01fe0 0x4d0000fffff00ff0

def z1096 : W := mkw 0x75c8b1630c161614 0xbae458b1860b0b0a 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z1097 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xffff19fc0fe31fe1 0xffff8cfe07f18ff0

def z1098 : W := mkw 0x3026fe57e0000000 0x98137f2bf0000000 0x600ffe0ff0000000 0x3007ff07f8000000

def z1099 : W := mkw 0xb5edde010fdbc004 0x5af6ef0087ede002 0xedfffe018fffe007 0xf6ffff00c7fff003

def z1100 : W := mkw 0x407a64de40000000 0x203d326f20000000 0x717fe7ce70000001 0xb8bff3e738000000

def z1101 : W := mkw 0x1400216300041614 0x0a0010b180020b0a 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z1102 : W := mkw 0x75feffffec161614 0xbaff7ffff60b0b0a 0x7dfffffff81f1c1f 0xbefffffffc0f8e0f

def z1103 : W := mkw 0x707efedfe0000000 0xb83f7f6ff0000000 0x717fffcff0000001 0xb8bfffe7f8000000

def z1104 : W := mkw 0x501221ffe0000000 0xa80910fff0000000 0x508f01fff0000001 0x284780fff8000000

def z1105 : W := mkw 0x04060a14ac161614 0x0203050a560b0b0a 0xfe8f1e3ffe1f1f1f 0x7f478f1fff0f8f8f

def z1106 : W := mkw 0xa1ecde000cda8000 0x50f66f00066d4000 0xedfffe0009fce001 0xf6ffff0004fe7000

def z1107 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x3680f9f3861f1f1e 0x1b407cf9c30f8f8f

def z1108 : W := mkw 0xa025de00135be16a 0x5012ef0009adf0b5 0xa600fe00071fe3fe 0x53007f00038ff1ff

def z1109 : W := mkw 0xb224fe43f05fe438 0xd9127f21f82ff21c 0x2400fe03f01fe018 0x12007f01f80ff00c

def z1110 : W := mkw 0x485b009c03a009c0 0x242d804e01d004e0 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z1111 : W := mkw 0x485b009c0fa01bc0 0x242d804e07d00de0 0xdb7f01cc0fe01fe1 0xedbf80e607f00ff0

def z1112 : W := mkw 0xf5feffffecde9614 0xfaff7ffff66f4b0a 0x79fffffff8fc1c01 0xbcfffffffc7e0e00

def z1113 : W := mkw 0xb424fe43b05fe43e 0x5a127f21d82ff21f 0x2400fe03f01fe01e 0x12007f01f80ff00f

def z1114 : W := mkw 0x73feffffe06c8c90 0xb9ff7ffff0364648 0xfffffffff8fc1c19 0xfffffffffc7e0e0c

def z1115 : W := mkw 0xe9db91bc0fb21bc0 0x74edc8de07d90de0 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z1116 : W := mkw 0x73feffffe06c8c90 0xb9ff7ffff0364648 0xfdfffffff9fcfc01 0xfefffffffcfe7e00

def z1117 : W := mkw 0x607e4e9ce0000000 0xb03f274e70000000 0x517f07cc70000001 0xa8bf83e638000000

def z1118 : W := mkw 0x75feffffec161614 0xbaff7ffff60b0b0a 0x73fffffff6031f1f 0xb9fffffffb018f8f

def z1119 : W := mkw 0x50366fffe0000000 0xa81b37fff0000000 0x71fffffff0000001 0xb8fffffff8000000

def z1120 : W := mkw 0x000100001349e16a 0x0000800009a4f0b5 0x8e0000000fffe3fe 0x4700000007fff1ff

def z1121 : W := mkw 0x0013009c032009c0 0x0009804e019004e0 0xdb7f01cc09e01ce1 0xedbf80e604f00e70

def z1122 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0xff8f1fffff03ffff 0xffc78fffff81ffff

def z1123 : W := mkw 0x040100001317657e 0x02008000098bb2bf 0x86000000071fe3fe 0x43000000038ff1ff

def z1124 : W := mkw 0x61fe4fbce0000000 0xb0ff27de70000000 0x417f07cc70000000 0xa0bf83e638000000

def z1125 : W := mkw 0x485b009c03a009c0 0x242d804e01d004e0 0x497f01cc09e01ce0 0xa4bf80e604f00e70

def z1126 : W := mkw 0x0059008803a00880 0x002c804401d00440 0xdb7f01cc09e01ce1 0xedbf80e604f00e70

def z1127 : W := mkw 0x21ecde00a0000000 0x10f66f0050000000 0x61fffe03f0000001 0xb0ffff01f8000000

def z1128 : W := mkw 0xe07e4e9ce0c88000 0xf03f274e70644000 0x407f060c70e00000 0x203f830638700000

def z1129 : W := mkw 0x59db91bd0fa01bc0 0x2cedc8de87d00de0 0xdbff19fd8fe01fe1 0xedff8cfec7f00ff0

def z1130 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0xf9fffffff9e00001 0xfcfffffffcf00000

def z1131 : W := mkw 0x61fede9ce0000000 0xb0ff6f4e70000000 0x71fffe3ff0000001 0xb8ffff1ff8000000

def z1132 : W := mkw 0xa9edde000fdbd340 0x54f6ef0007ede9a0 0xedfffe000fffe301 0xf6ffff0007fff180

def z1133 : W := mkw 0x71eedf35e0000000 0xb8f76f9af0000000 0x008f1e31f0000000 0x00478f18f8000000

def z1134 : W := mkw 0x21fefedee0000000 0x10ff7f6f70000000 0x71fffffff0000001 0xb8fffffff8000000

def z1135 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x51ffe7fc70000001 0xa8fff3fe38000000

def z1136 : W := mkw 0x71feffffec001200 0xb8ff7ffff6000900 0x79fffffff8001c01 0xbcfffffffc000e00

def z1137 : W := mkw 0x20264e14e0000000 0x9013270a70000000 0x400f060c70000000 0x2007830638000000

def z1138 : W := mkw 0x21edde000fc88000 0x10f6ef0007e44000 0xedfffe000ffce001 0xf6ffff0007fe7000

def z1139 : W := mkw 0x0a0100001fe8bbe8 0x050080000ff45df4 0x8a0000000fe0ffe0 0x4500000007f07ff0

def z1140 : W := mkw 0x163064cb506cacbc 0x0b183265a836565e 0xff70e7cff9fcfcff 0xffb873e7fcfe7e7f

def z1141 : W := mkw 0x01860b34a0000000 0x00c3059a50000000 0x718f1ffff0000001 0xb8c78ffff8000000

def z1142 : W := mkw 0x31eeff77a0000000 0x18f77fbbd0000000 0x71fffffff0000001 0xb8fffffff8000000

def z1143 : W := mkw 0x01d901a80fa01a80 0x00ec80d407d00d40 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z1144 : W := mkw 0x9581b1631fdff77e 0x4ac0d8b18feffbbf 0xbf80f9f38fffffff 0xdfc07cf9c7ffffff

def z1145 : W := mkw 0x77f8f5eb4c7e9e94 0xbbfc7af5a63f4f4a 0x0970e1c008fc1c00 0x84b870e0047e0e00

def z1146 : W := mkw 0x0801000013a169ea 0x0400800009d0b4f5 0x0000000001e0e0e0 0x0000000000f07070

def z1147 : W := mkw 0x71fedfbde0000000 0xb8ff6fdef0000000 0x61fffe3df0000001 0xb0ffff1ef8000000

def z1148 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0xffff01fe0fe01ff9 0xffff80ff07f00ffc

def z1149 : W := mkw 0xa1ecde00005bc000 0x50f66f00002de000 0xedfffe0009ffe001 0xf6ffff0004fff000

def z1150 : W := mkw 0x49db01bc03a01bc0 0x24ed80de01d00de0 0x53ff01fc01e01fe1 0xa9ff80fe00f00ff0

def z1151 : W := mkw 0x81e944000fdbc000 0x40f4a20007ede000 0xedffe6000fffe001 0xf6fff30007fff000

def z1152 : W := mkw 0x71feffffe0120000 0xb8ff7ffff0090000 0x75fffffff01f0001 0xbafffffff80f8000

def z1153 : W := mkw 0x35fcffeb4c161614 0x1afe7ff5a60b0b0a 0xfffffffffe1f1f1f 0xffffffffff0f8f8f

def z1154 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0x69fffe0009fce001 0xb4ffff0004fe7000

def z1155 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0xf5fffffff6030001 0xfafffffffb018000

def z1156 : W := mkw 0x02010000136cadf8 0x0100800009b656fc 0x8e0000000ffcfff8 0x4700000007fe7ffc

def z1157 : W := mkw 0x41fa45bc40000000 0x20fd22de20000000 0x51ff07fc70000001 0xa8ff83fe38000000

def z1158 : W := mkw 0x61fede9cec120000 0xb0ff6f4e76090000 0xedfffe0c7e1f0001 0xf6ffff063f0f8000

def z1159 : W := mkw 0x080100001fa17bea 0x040080000fd0bdf5 0x8a0000000fe0ffe0 0x4500000007f07ff0

def z1160 : W := mkw 0x5596bbffec161614 0xaacb5dfff60b0b0a 0xff8ffffffe1f1f1f 0xffc7ffffff0f8f8f

def z1161 : W := mkw 0x8001000013c9e16a 0x4000800009e4f0b5 0x0000000001e0e0e0 0x0000000000f07070

def z1162 : W := mkw 0x71feffffe0040410 0xb8ff7ffff0020208 0x75fffffff01c0019 0xbafffffff80e000c

def z1163 : W := mkw 0x206c4e00e0000000 0x9036270070000000 0x407f060070000000 0x203f830038000000

def z1164 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xedfffe038fffe01f 0xf6ffff01c7fff00f

def z1165 : W := mkw 0x1400b16300161614 0x0a0058b1800b0b0a 0xb680f9f3861f1f1f 0x5b407cf9c30f8f8f

def z1166 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0xff70e7ce7fffffff 0xffb873e73fffffff

def z1167 : W := mkw 0x405e0a9ca0000000 0x202f054e50000000 0x70ff1e3ff0000001 0x387f8f1ff8000000

def z1168 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x308ffffff0000000 0x1847fffff8000000

def z1169 : W := mkw 0x55debbffac161614 0x2aef5dffd60b0b0a 0xfffffffffe1f1f1f 0xffffffffff0f8f8f

def z1170 : W := mkw 0xb5eddf210fdbd204 0x5af6ef9087ede902 0xedfffe000fffe001 0xf6ffff0007fff000

def z1171 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x50ff1ffff0000000 0x287f8ffff8000000

def z1172 : W := mkw 0xf9feffffecfa9a80 0xfcff7ffff67d4d40 0x79fffffff8fc1c01 0xbcfffffffc7e0e00

def z1173 : W := mkw 0xa1eddf200fdbd200 0x50f6ef9007ede900 0xedffffc00ffffc01 0xf6ffffe007fffe00

def z1174 : W := mkw 0x1406ba57a0160414 0x0a035d2bd00b020a 0x748ffe3ff01f001f 0x3a47ff1ff80f800f

def z1175 : W := mkw 0x158191211f13736e 0x0ac0c8908f89b9b7 0x868018318703e3fe 0x43400c18c381f1ff

def z1176 : W := mkw 0x4a1220de50242df8 0x2509106f281216fc 0x120001ce70001cf8 0x090000e738000e7c

def z1177 : W := mkw 0x71faf5ff40000000 0xb8fd7affa0000000 0x71ffe7fe70000001 0xb8fff3ff38000000

def z1178 : W := mkw 0x1400b1630c161614 0x0a0058b1860b0b0a 0xbe00f9f38e1f1f1e 0x5f007cf9c70f8f8f

def z1179 : W := mkw 0xe07e4e9ce049c000 0xf03f274e7024e000 0x407f060c7000e000 0x203f830638007000

def z1180 : W := mkw 0x75fedfbdec121204 0xbaff6fdef6090902 0x40ff1e3df6030306 0x207f8f1efb018183

def z1181 : W := mkw 0x605e0a9ce0000000 0xb02f054e70000000 0x000f000c70000000 0x0007800638000000

def z1182 : W := mkw 0x49db01bcefa01bc0 0xa4ed80de77d00de0 0xdbff01fc7fe01fe1 0xedff80fe3ff00ff0

def z1183 : W := mkw 0x71feffffe0488000 0xb8ff7ffff0244000 0x75fffffff01ce001 0xbafffffff80e7000

def z1184 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0x2dfffe000effe000 0x96ffff00077ff000

def z1185 : W := mkw 0x1d81b1631fb77ffe 0x0ec0d8b18fdbbfff 0xbf80f9f38fffffff 0xdfc07cf9c7ffffff

def z1186 : W := mkw 0x1181b1631301616a 0x08c0d8b18980b0b5 0xb780f9f38703e3ff 0xdbc07cf9c381f1ff

def z1187 : W := mkw 0x50060b35a0000000 0xa803059ad0000000 0x708f1e3ff0000001 0x38478f1ff8000000

def z1188 : W := mkw 0x71fcffebe0000000 0xb8fe7ff5f0000000 0x61ffffc3f0000001 0xb0ffffe1f8000000

def z1189 : W := mkw 0x75eeff77ec161614 0xbaf77fbbf60b0b0a 0x248ffe33f61f031e 0x1247ff19fb0f818f

def z1190 : W := mkw 0x505a21ffe0000000 0xa82d10fff0000000 0x507f01fff0000000 0x283f80fff8000000

def z1191 : W := mkw 0x521221fff0242dfa 0xa90910fff81216fd 0x120001fff0001ffe 0x090000fff8000fff

def z1192 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x508f063c70000001 0x2847831e38000000

def z1193 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x21fffff3f0000000 0x90fffff9f8000000

def z1194 : W := mkw 0x71feffffe0040410 0xb8ff7ffff0020208 0x79fffffff81c1c01 0xbcfffffffc0e0e00

def z1195 : W := mkw 0x0a01000013ecadf8 0x0500800009f656fc 0x8e00000009fcfcf8 0x4700000004fe7e7c

def z1196 : W := mkw 0x75feffffec121204 0xbaff7ffff6090902 0xfdfffffffe1f0307 0xfeffffffff0f8183

def z1197 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x617fffcff0000000 0xb0bfffe7f8000000

def z1198 : W := mkw 0x35eeff77ac161614 0x1af77fbbd60b0b0a 0xfffffffffe1f1f1f 0xffffffffff0f8f8f

def z1199 : W := mkw 0x607e6edee0040410 0xb03f376f70020208 0xff7fe7ce781c1c19 0xffbff3e73c0e0e0c

def z1200 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0x528f1e3ff703e3fe 0x29478f1ffb81f1ff

def z1201 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0xf48f1e3ff100e001 0x7a478f1ff8807000

def z1202 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0xff80f9ff8f1f1fff 0xffc07cffc78f8fff

def z1203 : W := mkw 0x73feffffe06c8c90 0xb9ff7ffff0364648 0xfbfffffff9fc1ce1 0xfdfffffffcfe0e70

def z1204 : W := mkw 0xa1edde0003dbc000 0x50f6ef0001ede000 0x65fffe0001ffe001 0xb2ffff0000fff000

def z1205 : W := mkw 0x000100001f81616a 0x000080000fc0b0b5 0x8e0000000fe3e3fe 0x4700000007f1f1ff

def z1206 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0xfff0e7fe7ffcfff9 0xfff873ff3ffe7ffc

def z1207 : W := mkw 0x040020420c161614 0x02001021060b0b0a 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z1208 : W := mkw 0x79feffffe0a00880 0xbcff7ffff0500440 0x71fffffff0e00001 0xb8fffffff8700000

def z1209 : W := mkw 0x0a01000013e8a9e8 0x0500800009f454f4 0x0000000001e0e0e0 0x0000000000f07070

def z1210 : W := mkw 0x71fedfbde0000000 0xb8ff6fdef0000000 0x407f060c70000000 0x203f830638000000

def z1211 : W := mkw 0x607e4e9ce0000000 0xb03f274e70000000 0x60ff1e0c70000001 0x307f8f0638000000

def z1212 : W := mkw 0x41da01bc00000000 0x20ed00de00000000 0x71ff07fe70000001 0xb8ff83ff38000000

def z1213 : W := mkw 0xa06d4e0003c9c000 0x5036a70001e4e000 0x647fe60001fce000 0x323ff30000fe7000

def z1214 : W := mkw 0xf1eddf210fdbc000 0xf8f6ef9087ede000 0xedfffe000fffe001 0xf6ffff0007fff000

def z1215 : W := mkw 0x687e4fbce0201bc0 0xb43f27de70100de0 0x527f07fc70001fe0 0x293f83fe38000ff0

def z1216 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xc9ffe6000ffce001 0xe4fff30007fe7000

def z1217 : W := mkw 0x00060a14a0014002 0x0003050a5000a001 0x708f1e3ff0030007 0x38478f1ff8018003

def z1218 : W := mkw 0x020100001fecacb8 0x010080000ff6565c 0x8e0000000ffcfcf8 0x4700000007fe7e7c

def z1219 : W := mkw 0x3026fe57e0000000 0x98137f2bf0000000 0x208ffe33f0000000 0x1047ff19f8000000

def z1220 : W := mkw 0x080100001f81736a 0x040080000fc0b9b5 0x860000000703e3fe 0x430000000381f1ff

def z1221 : W := mkw 0x880100001ffbfbea 0x440080000ffdfdf5 0x8e0000000ffffffe 0x4700000007ffffff

def z1222 : W := mkw 0x00346eca40000000 0x001a376520000000 0x71ffffce70000001 0xb8ffffe738000000

def z1223 : W := mkw 0x41fa65fe4c041610 0x20fd32ff26020b08 0xffffe7fe7e1c1f19 0xfffff3ff3f0e0f8c

def z1224 : W := mkw 0x71fefedfe0000000 0xb8ff7f6ff0000000 0x61fffe0ff0000001 0xb0ffff07f8000000

def z1225 : W := mkw 0x747e6fffe0041614 0xba3f37fff0020b0a 0x527f07fff0001f1e 0x293f83fff8000f8f

def z1226 : W := mkw 0x41db01bc032009c0 0x20ed80de019004e0 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z1227 : W := mkw 0x405e0a9ca0000000 0x202f054e50000000 0x407f060c70000000 0x203f830638000000

def z1228 : W := mkw 0xb025fe43efdbc000 0xd812ff21f7ede000 0xac00fe03ffffe000 0x56007f01fffff000

def z1229 : W := mkw 0x0002001400000000 0x0001000a00000000 0x708f063e70000001 0x3847831f38000000

def z1230 : W := mkw 0x018091200c121200 0x00c0489006090900 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z1231 : W := mkw 0x71feffffe0200880 0xb8ff7ffff0100440 0x71fffffff1e000e1 0xb8fffffff8f00070

def z1232 : W := mkw 0x02366edee06c8c90 0x011b376f70364648 0x79fffffff8fc1c01 0xbcfffffffc7e0e00

def z1233 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xfffffe0c0fffe0e1 0xffffff0607fff070

def z1234 : W := mkw 0x820100001fffedfa 0x410080000ffff6fd 0x8e0000000ffffffe 0x4700000007ffffff

def z1235 : W := mkw 0x61fe4e9ce0000000 0xb0ff274e70000000 0x41ff060c70000001 0xa0ff830638000000

def z1236 : W := mkw 0x02010000136dedfa 0x0100800009b6f6fd 0x8e00000009fcfcf8 0x4700000004fe7e7c

def z1237 : W := mkw 0x1f81b1631ffebffc 0x0fc0d8b18fff5ffe 0xbf80f9f38fffffff 0xdfc07cf9c7ffffff

def z1238 : W := mkw 0x51fa65ffe0000000 0xa8fd32fff0000000 0x71ffe7fff0000001 0xb8fff3fff8000000

def z1239 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x208f1e33f0000000 0x10478f19f8000000

def z1240 : W := mkw 0x61fe6ffee0000000 0xb0ff37ff70000000 0x71ffe7fe70000001 0xb8fff3ff38000000

def z1241 : W := mkw 0x71ce9b35a0000000 0xb8e74d9ad0000000 0x208f1e33f0000000 0x10478f19f8000000

def z1242 : W := mkw 0xf5feffffecde9614 0xfaff7ffff66f4b0a 0xfffffffffeff1f1f 0xffffffffff7f8f8f

def z1243 : W := mkw 0x75debbffec161614 0xbaef5dfff60b0b0a 0xbf8ff9fffe1f1f1f 0xdfc7fcffff0f8f8f

def z1244 : W := mkw 0x43da01bc106cacb8 0x21ed00de0836565c 0xdfff01fc09fcfcf9 0xefff80fe04fe7e7c

def z1245 : W := mkw 0x71eeff77e0000000 0xb8f77fbbf0000000 0x708ffe3ff0000001 0x3847ff1ff8000000

def z1246 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x968000300703e3ff 0x4b4000180381f1ff

def z1247 : W := mkw 0x607e6edee0000000 0xb03f376f70000000 0x417fe7cc70000000 0xa0bff3e638000000

def z1248 : W := mkw 0x71fedfbde0000000 0xb8ff6fdef0000000 0x51ff1ffdf0000001 0xa8ff8ffef8000000

def z1249 : W := mkw 0x75feffffe0001204 0xbaff7ffff0000902 0x71fffffff0000307 0xb8fffffff8000183

def z1250 : W := mkw 0x040100001f13736e 0x020080000f89b9b7 0x860000000703e3fe 0x430000000381f1ff

def z1251 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x748f1e3ff003001f 0x3a478f1ff801800f

def z1252 : W := mkw 0x485b01bc0fa01bc0 0x242d80de07d00de0 0xda7f01fc0fe01fe0 0x6d3f80fe07f00ff0

def z1253 : W := mkw 0x000100001300216a 0x00008000098010b5 0x82000000070003fe 0x41000000038001ff

def z1254 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x708f1e3ff6030307 0x38478f1ffb018183

def z1255 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0x52ff01fc07e01fe0 0x297f80fe03f00ff0

def z1256 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x040000000103e0fe 0x020000000081f07f

def z1257 : W := mkw 0x55da21ffec041614 0xaaed10fff6020b0a 0xdbff01fffe001f1f 0xedff80ffff000f8f

def z1258 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x000000000703e3e6 0x000000000381f1f3

def z1259 : W := mkw 0x41fe6ffee0000000 0x20ff37ff70000000 0x71fffffff0000001 0xb8fffffff8000000

def z1260 : W := mkw 0x71feffffe0200880 0xb8ff7ffff0100440 0x79fffffff8e01c01 0xbcfffffffc700e00

def z1261 : W := mkw 0x79feffffe0001340 0xbcff7ffff00009a0 0x71fffffff0000301 0xb8fffffff8000180

def z1262 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0x2d80f9f38e1f1f1e 0x96c07cf9c70f8f8f

def z1263 : W := mkw 0x3426fe57e0160414 0x9a137f2bf00b020a 0xf68ffe3ff61f031f 0x7b47ff1ffb0f818f

def z1264 : W := mkw 0xa06dde0003dbc000 0x5036ef0001ede000 0xed7ffe0009ffe001 0xf6bfff0004fff000

def z1265 : W := mkw 0x61fedfbce0000000 0xb0ff6fde70000000 0x71fffffc70000001 0xb8fffffe38000000

def z1266 : W := mkw 0x71feffffec120000 0xb8ff7ffff6090000 0xfffffffffe1f031f 0xffffffffff0f818f

def z1267 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0xeffffe000fffe31f 0xf7ffff0007fff18f

def z1268 : W := mkw 0xa3fcfeca4cfe8c90 0x51fe7f65267f4648 0x79ffffce78fc1c01 0xbcffffe73c7e0e00

def z1269 : W := mkw 0x79feffffeca01a80 0xbcff7ffff6500d40 0xfbfffffff9e01ce1 0xfdfffffffcf00e70

def z1270 : W := mkw 0x77feffffec7e9e94 0xbbff7ffff63f4f4a 0xfffffffffeff1f1f 0xffffffffff7f8f8f

def z1271 : W := mkw 0x707e6fffe0000000 0xb83f37fff0000000 0x70ff1ffff0000001 0x387f8ffff8000000

def z1272 : W := mkw 0x71feffffe0240c90 0xb8ff7ffff0120648 0xfffffffff9fc1cf9 0xfffffffffcfe0e7c

def z1273 : W := mkw 0x71eeff77e0000000 0xb8f77fbbf0000000 0x61fffe33f0000001 0xb0ffff19f8000000

def z1274 : W := mkw 0xb1edde01afdbc000 0xd8f6ef00d7ede000 0xedfffe018fffe001 0xf6ffff00c7fff000

def z1275 : W := mkw 0x23ecde00106cacb8 0x11f66f000836565c 0xeffffe0009fcfcf9 0xf7ffff0004fe7e7c

def z1276 : W := mkw 0x00050a0013016028 0x000285000980b014 0xf68f1e3ff703e3ff 0x7b478f1ffb81f1ff

def z1277 : W := mkw 0x30069a15a0000000 0x98034d0ad0000000 0x708f1e3ff0000001 0x38478f1ff8000000

def z1278 : W := mkw 0x00266e56e0000000 0x0013372b70000000 0x708ffe3ff0000001 0x3847ff1ff8000000

def z1279 : W := mkw 0x5c1221ffb0243ffe 0x2e0910ffd8121fff 0x120001fff0001ffe 0x090000fff8000fff

def z1280 : W := mkw 0x000100001301602a 0x000080000980b015 0x840000000703e01e 0x420000000381f00f

def z1281 : W := mkw 0x31ecfe43e0000000 0x98f67f21f0000000 0x208ffe03f0000000 0x1047ff01f8000000

def z1282 : W := mkw 0xa2246e42504de438 0x511237212826f21c 0x2400e602701ce018 0x12007301380e700c

def z1283 : W := mkw 0x627e4e9ce0688880 0xb13f274e70344440 0x407f060c70e00000 0x203f830638700000

def z1284 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x608f1e0c70000001 0x30478f0638000000

def z1285 : W := mkw 0x021220def0242dfa 0x0109106f781216fd 0x120001ce70001cf8 0x090000e738000e7c

def z1286 : W := mkw 0xa1edde000fdbc142 0x50f6ef0007ede0a1 0xedfffe000fffe307 0xf6ffff0007fff183

def z1287 : W := mkw 0x71feffffec5a8000 0xb8ff7ffff62d4000 0xfdffffffffffe001 0xfefffffffffff000

def z1288 : W := mkw 0x01a5de000f5bc000 0x00d2ef0007ade000 0xedfffe000fffe001 0xf6ffff0007fff000

def z1289 : W := mkw 0x0801000013217bea 0x040080000990bdf5 0x860000000703fffe 0x430000000381ffff

def z1290 : W := mkw 0x49db91bc0fb21bc0 0x24edc8de07d90de0 0xdbffe1fc0ffc1fe1 0xedfff0fe07fe0ff0

def z1291 : W := mkw 0xf5feffffec5fd614 0xfaff7ffff62feb0a 0xfffffffffe1fff1f 0xffffffffff0fff8f

def z1292 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x040000000603e31e 0x020000000301f18f

def z1293 : W := mkw 0x0069440003c88000 0x0034a20001e44000 0xed7fe60009fce001 0xf6bff30004fe7000

def z1294 : W := mkw 0x161221fff0243ffe 0x0b0910fff8121fff 0x120001fff0001ffe 0x090000fff8000fff

def z1295 : W := mkw 0x21eede14ac120000 0x10f76f0a56090000 0xfffffe3ffe1f031f 0xffffff1fff0f818f

def z1296 : W := mkw 0x75cebb77ac161614 0xbae75dbbd60b0b0a 0xff8ffffffe1f1f1f 0xffc7ffffff0f8f8f

def z1297 : W := mkw 0x627f4e9cf369e9ea 0xb13fa74e79b4f4f5 0x407f060c71e0e0e0 0x203f830638f07070

def z1298 : W := mkw 0xf1feffffe05a8000 0xf8ff7ffff02d4000 0x71fffffff01c0001 0xb8fffffff80e0000

def z1299 : W := mkw 0x75feffffe0041614 0xbaff7ffff0020b0a 0xfffffffff81c1f1f 0xfffffffffc0e0f8f

def z1300 : W := mkw 0x00020014a0000000 0x0001000a50000000 0x508f003ff0000001 0x2847801ff8000000

def z1301 : W := mkw 0x140121631305777e 0x0a0090b18982bbbf 0x960001f38703fffe 0x4b0000f9c381ffff

def z1302 : W := mkw 0x49da01bc00201bc0 0x24ed00de00100de0 0xdbff01fc09e01fe1 0xedff80fe04f00ff0

def z1303 : W := mkw 0x71fe6fffe0000000 0xb8ff37fff0000000 0x51ff07fff0000001 0xa8ff83fff8000000

def z1304 : W := mkw 0x75feffffec161614 0xbaff7ffff60b0b0a 0x75fffffff61f031f 0xbafffffffb0f818f

def z1305 : W := mkw 0x018021620c041610 0x00c010b106020b08 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z1306 : W := mkw 0x50162bffe0000000 0xa80b15fff0000000 0x500f07fff0000000 0x280783fff8000000

def z1307 : W := mkw 0x803164ca4fdbc000 0x4018b26527ede000 0xfd70e7ce7fffe001 0xfeb873e73ffff000

def z1308 : W := mkw 0x607e4e9ce0000000 0xb03f274e70000000 0x40ff1e3df0000000 0x207f8f1ef8000000

def z1309 : W := mkw 0x604e0a14a0000000 0xb027050a50000000 0x400f060c70000000 0x2007830638000000

def z1310 : W := mkw 0xa1edde00afdbc002 0x50f6ef0057ede001 0xedfffe018fffe007 0xf6ffff00c7fff003

def z1311 : W := mkw 0x49db91bc0fb21bc0 0x24edc8de07d90de0 0xfffff9ff8fff1fff 0xfffffcffc7ff8fff

def z1312 : W := mkw 0x80254e000fdbc000 0x4012a70007ede000 0xedfffe000fffe001 0xf6ffff0007fff000

def z1313 : W := mkw 0x00244e0000488000 0x0012270000244000 0xedfffe0009fce001 0xf6ffff0004fe7000

def z1314 : W := mkw 0xa1edde000fdbc000 0x50f6ef0007ede000 0x49fffe000fffe000 0xa4ffff0007fff000

def z1315 : W := mkw 0x820100001ffbe8a8 0x410080000ffdf454 0x8c0000000fffe0e0 0x4600000007fff070

def z1316 : W := mkw 0x01ed4e000fc9c000 0x00f6a70007e4e000 0xedfffe000fffe001 0xf6ffff0007fff000

def z1317 : W := mkw 0x79feffffeca01bc0 0xbcff7ffff6500de0 0x7bfffffff8e01fe1 0xbdfffffffc700ff0

def z1318 : W := mkw 0x01db009c0fa009c0 0x00ed804e07d004e0 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z1319 : W := mkw 0x02010000136decb8 0x0100800009b6f65c 0x8e0000000ffffcf8 0x4700000007fffe7c

def z1320 : W := mkw 0x485b009c03a009c0 0x242d804e01d004e0 0x527f01cc01e01ce0 0x293f80e600f00e70

def z1321 : W := mkw 0x75feffffec161614 0xbaff7ffff60b0b0a 0x497fe7cc781c1c00 0xa4bff3e63c0e0e00

def z1322 : W := mkw 0x48160bbca0201bc0 0x240b05de50100de0 0x728f1ffff0001fe1 0x39478ffff8000ff0

def z1323 : W := mkw 0x705e2bffe0000000 0xb82f15fff0000000 0x100f01fff0000000 0x080780fff8000000

def z1324 : W := mkw 0x607e4e9ce0200880 0xb03f274e70100440 0xdb7f07cc79e01ce1 0xedbf83e63cf00e70

def z1325 : W := mkw 0x000100001f13616a 0x000080000f89b0b5 0x8e0000000f1fe3fe 0x47000000078ff1ff

def z1326 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x408f1e3df0000000 0x20478f1ef8000000

def z1327 : W := mkw 0x206e4e14a0000000 0x1037270a50000000 0x70ff1e3ff0000001 0x387f8f1ff8000000

def z1328 : W := mkw 0x75feffffec160414 0xbaff7ffff60b020a 0xfdfffffffe1f001f 0xfeffffffff0f800f

def z1329 : W := mkw 0x2026de14a0000000 0x10136f0a50000000 0x708ffe3ff0000001 0x3847ff1ff8000000

def z1330 : W := mkw 0x75feffffec161614 0xbaff7ffff60b0b0a 0xfbfffffffe1c1f01 0xfdffffffff0e0f80

def z1331 : W := mkw 0x71feffffec001200 0xb8ff7ffff6000900 0x71fffffff6000301 0xb8fffffffb000180

def z1332 : W := mkw 0xa06d4e0003c9c000 0x5036a70001e4e000 0xedfffe000fffe001 0xf6ffff0007fff000

def z1333 : W := mkw 0xa1edde0003c9c000 0x50f6ef0001e4e000 0xedfffe0009fce001 0xf6ffff0004fe7000

def z1334 : W := mkw 0x707efedfe0000000 0xb83f7f6ff0000000 0x407fe60c70000000 0x203ff30638000000

def z1335 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x73fffffff000031f 0xb9fffffff800018f

def z1336 : W := mkw 0x820100001fdfe438 0x410080000feff21c 0x8c0000000fffe018 0x4600000007fff00c

def z1337 : W := mkw 0x000100001305657a 0x000080000982b2bd 0x8e0000000f1ffffe 0x47000000078fffff

def z1338 : W := mkw 0xe1fede9cecda8000 0xf0ff6f4e766d4000 0x497fe60c78fc0000 0xa4bff3063c7e0000

def z1339 : W := mkw 0x00070a14b301616a 0x0003850a5980b0b5 0x648f1e3ff703e3fe 0x32478f1ffb81f1ff

def z1340 : W := mkw 0x75feffffec161614 0xbaff7ffff60b0b0a 0x79fffffffe1f1f07 0xbcffffffff0f8f83

def z1341 : W := mkw 0x41da21fe40000000 0x20ed10ff20000000 0x51ff01fe70000001 0xa8ff80ff38000000

def z1342 : W := mkw 0x71feffffec120000 0xb8ff7ffff6090000 0x79fffffff81c0001 0xbcfffffffc0e0000

def z1343 : W := mkw 0xb1eddf210fdbc000 0x58f6ef9087ede000 0xedfffe318fffe001 0xf6ffff18c7fff000

def z1344 : W := mkw 0x71feffffe0488000 0xb8ff7ffff0244000 0x71fffffff1e0e001 0xb8fffffff8f07000

def z1345 : W := mkw 0x840100001fdff77e 0x420080000feffbbf 0x8e0000000ffffffe 0x4700000007ffffff

def z1346 : W := mkw 0x77feffffec7e9e94 0xbbff7ffff63f4f4a 0x79fffffff8fc1c01 0xbcfffffffc7e0e00

def z1347 : W := mkw 0x61fefedee0000000 0xb0ff7f6f70000000 0x71ffffce70000001 0xb8ffffe738000000

def z1348 : W := mkw 0x207c4e8840000000 0x103e274420000000 0x407f060c70000000 0x203f830638000000

def z1349 : W := mkw 0x71feffffec000000 0xb8ff7ffff6000000 0xf9fffffffe000001 0xfcffffffff000000

def z1350 : W := mkw 0x001020ca10242cb8 0x000810650812165c 0xff70e7ce79fcfcf9 0xffb873e73cfe7e7c

def z1351 : W := mkw 0xa06dde0003dbc000 0x5036ef0001ede000 0xe4fffe0007ffe001 0x727fff0003fff000

def z1352 : W := mkw 0x0813009c0fa01bc0 0x0409804e07d00de0 0xdbff01fc0fe01fe1 0xedff80fe07f00ff0

def z1353 : W := mkw 0x71fcffeb40000000 0xb8fe7ff5a0000000 0x71ffffce70000001 0xb8ffffe738000000

def z1354 : W := mkw 0x000100001301616a 0x000080000980b0b5 0xa68018000703e3ff 0x53400c000381f1ff

def z1355 : W := mkw 0x79feffffe0201a80 0xbcff7ffff0100d40 0x71fffffff0001c01 0xb8fffffff8000e00

def z1356 : W := mkw 0x5dc8b1630c961614 0x2ee458b1864b0b0a 0xbf80f9f38e1f1f1f 0xdfc07cf9c70f8f8f

def z1357 : W := mkw 0xf3feffffecfe8c90 0xf9ff7ffff67f4648 0x79fffffff8fc1c01 0xbcfffffffc7e0e00

def z1358 : W := mkw 0x71feffffe0000000 0xb8ff7ffff0000000 0x61ffffcc70000001 0xb0ffffe638000000

def z1359 : W := mkw 0x41da01bce0000000 0xa0ed00de70000000 0x51ff01fc70000001 0xa8ff80fe38000000

def z1360 : W := mkw 0x80010000135be16a 0x4000800009adf0b5 0x86000000071fe3fe 0x43000000038ff1ff

def z1361 : W := mkw 0x1624fe43f05fe43e 0x0b127f21f82ff21f 0x2400fe03f01fe01e 0x12007f01f80ff00f

def z1362 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0x108f183ff0000000 0x08478c1ff8000000

def z1363 : W := mkw 0x71de9bbda0000000 0xb8ef4dded0000000 0x71ff1ffff0000001 0xb8ff8ffff8000000

def z1364 : W := mkw 0x00264e14a0000000 0x0013270a50000000 0x71fffe3ff0000001 0xb8ffff1ff8000000

def z1365 : W := mkw 0x71feffffec121200 0xb8ff7ffff6090900 0xfffffffffe1f1f01 0xffffffffff0f8f80

def z1366 : W := mkw 0x21ecfe4240000000 0x10f67f2120000000 0x61fffe0270000001 0xb0ffff0138000000

def z1367 : W := mkw 0x09d900880fa01bc0 0x04ec804407d00de0 0xdbff01cc0fe01fe1 0xedff80e607f00ff0

def z1368 : W := mkw 0x9781b1631ffffebc 0x4bc0d8b18fffff5e 0xbf80f9f38fffffff 0xdfc07cf9c7ffffff

def z1369 : W := mkw 0x49d901a80fa01a80 0x24ec80d407d00d40 0xdbff01cc0fe01ce1 0xedff80e607f00e70

def z1370 : W := mkw 0x75debbffec161614 0xbaef5dfff60b0b0a 0x128f19fff6031f1e 0x09478cfffb018f8f

def z1371 : W := mkw 0x73feffffe0240c90 0xb9ff7ffff0120648 0x71fffffff0001c01 0xb8fffffff8000e00

def z1372 : W := mkw 0x7bfeffffecec9e90 0xbdff7ffff6764f48 0x79fffffff8fc1c01 0xbcfffffffc7e0e00

def z1373 : W := mkw 0x50162bffe0000000 0xa80b15fff0000000 0x108f19fff0000000 0x08478cfff8000000

def z1374 : W := mkw 0xe9cf9b34af935342 0x74e7cd9a57c9a9a1 0x008f183186030306 0x00478c18c3018183

def z1375 : W := mkw 0x71feffffec041610 0xb8ff7ffff6020b08 0xfffffffffe1c1f19 0xffffffffff0e0f8c

def z1376 : W := mkw 0x040100001305777e 0x020080000982bbbf 0x860000000703fffe 0x430000000381ffff

def z1377 : W := mkw 0x818190001fdbe16a 0x40c0c8000fedf0b5 0xbf80f8338fffe3ff 0xdfc07c19c7fff1ff

def z1378 : W := mkw 0x8201000013e9e8a8 0x4100800009f4f454 0x0000000001e0e0e0 0x0000000000f07070

def z1379 : W := mkw 0x71feffffe0688880 0xb8ff7ffff0344440 0xfffffffff9fcfce1 0xfffffffffcfe7e70

def z1380 : W := mkw 0x75feffffe0120004 0xbaff7ffff0090002 0x71fffffff0030007 0xb8fffffff8018003

def z1381 : W := mkw 0x607e4e9ce0000000 0xb03f274e70000000 0x707f060e70000001 0x383f830738000000

def z1382 : W := mkw 0x15b6ffffec161614 0x0adb7ffff60b0b0a 0xfffffffffe1f1f1f 0xffffffffff0f8f8f

def z1383 : W := mkw 0x00110088132169ea 0x000880440990b4f5 0xdf7001cc0fe3ffff 0xefb800e607f1ffff

def z1384 : W := mkw 0x00030014b301616a 0x0001800a5980b0b5 0x860000318703e3fe 0x43000018c381f1ff

def z1385 : W := mkw 0x71eeff77e0000000 0xb8f77fbbf0000000 0x318ffff3f0000001 0x98c7fff9f8000000

def z1386 : W := mkw 0x79feffffe02009c0 0xbcff7ffff01004e0 0x71fffffff00000e1 0xb8fffffff8000070

def z1387 : W := mkw 0x71de9bbde0000000 0xb8ef4ddef0000000 0x008f183df0000000 0x00478c1ef8000000

def z1388 : W := mkw 0x002144001349e16a 0x0010a20009a4f0b5 0xef70e6000fffe3ff 0xf7b8730007fff1ff

def z1389 : W := mkw 0x21ecde00e0000000 0x90f66f0070000000 0x61fffe0070000001 0xb0ffff0038000000

def z1390 : W := mkw 0x49db01bc0fa01bc0 0x24ed80de07d00de0 0x1bff01fc0ee01fe0 0x8dff80fe07700ff0

def z1391 : W := mkw 0x79feffffe0201bc0 0xbcff7ffff0100de0 0xfbfffffff9e01fe1 0xfdfffffffcf00ff0

def z1392 : W := mkw 0x75feffffe0040414 0xbaff7ffff002020a 0x71fffffff000001f 0xb8fffffff800000f

def z1393 : W := mkw 0xa1e9d4000fda8000 0x50f4ea0007ed4000 0xedffe6000ffce001 0xf6fff30007fe7000

def z1394 : W := mkw 0x00060a14a0000000 0x0003050a50000000 0xf48f1e3ff6030001 0x7a478f1ffb018000

def z1395 : W := mkw 0x0001000013016028 0x000080000980b014 0x860000000703e0f8 0x430000000381f07c

def z1396 : W := mkw 0x31a6ff77e0000000 0x98d37fbbf0000000 0x718ffffff0000001 0xb8c7fffff8000000

def z1397 : W := mkw 0x1580b1630c161614 0x0ac058b1860b0b0a 0xfff0f9f38fff1f1f 0xfff87cf9c7ff8f8f

def z1398 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x868018318703e3fe 0x43400c18c381f1ff

def z1399 : W := mkw 0x71feffffe04c8410 0xb8ff7ffff0264208 0xfffffffff9fcfc19 0xfffffffffcfe7e0c

def z1400 : W := mkw 0x000100001301616a 0x000080000980b0b5 0x840000000703e0e0 0x420000000381f070

def z1401 : W := mkw 0xa1e9d4001fdbe16a 0x50f4ea000fedf0b5 0x8f70e0000fffe3fe 0xc7b8700007fff1ff

def z1402 : W := mkw 0x206e4e14a0000000 0x1037270a50000000 0x407f060c70000000 0x203f830638000000

def z1403 : W := mkw 0x023064ca506cacb8 0x011832652836565c 0xff70e7fff9fcffff 0xffb873fffcfe7fff

def z1404 : W := mkw 0x00040a00a0000000 0x0002050050000000 0x608f1e03f0000001 0x30478f01f8000000

def z1405 : W := mkw 0x485b01bc03a01bc0 0x242d80de01d00de0 0xd2ff01fc07e01fe1 0x697f80fe03f00ff0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z6,z7,z2,z8,z3,z9,z5]),(0,[z10,z6,z7,z2,z3,z5,z11]),(0,[z6,z12,z7,z2,z3,z13,z5]),(0,[z6,z7,z2,z3,z14,z4,z5]),(0,[z6,z7,z2,z3,z15,z5,z16]),(0,[z6,z7,z2,z3,z4,z5,z17]),(0,[z6,z7,z2,z18,z3,z4,z19])],[(0,[z20,z6,z7,z2,z3,z21,z5]),(0,[z6,z7,z2,z3,z4,z22,z5]),(0,[z23,z6,z7,z2,z3,z24,z5]),(0,[z6,z7,z25,z2,z3,z4,z5]),(0,[z6,z7,z2,z26,z3,z4,z5]),(1,[z6,z7,z2,z3,z5,z27]),(0,[z6,z7,z2,z3,z4,z5,z19])],[(0,[z10,z28,z6,z7,z2,z3,z5]),(0,[z6,z7,z29,z2,z3,z4,z5]),(0,[z30,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z31,z5]),(0,[z6,z32,z7,z2,z3,z4,z5])],[(0,[z6,z7,z2,z33,z3,z4,z5]),(0,[z6,z34,z7,z2,z3,z4,z5]),(0,[z35,z20,z6,z7,z2,z3,z5]),(0,[z10,z6,z7,z2,z3,z4,z5]),(0,[z36,z6,z7,z2,z3,z4,z37]),(0,[z6,z38,z39,z2,z3,z4,z5]),(0,[z6,z40,z7,z2,z3,z41,z5]),(0,[z6,z40,z7,z2,z3,z4,z42]),(0,[z6,z7,z2,z43,z3,z4,z5]),(0,[z6,z7,z44,z2,z3,z4,z5]),(1,[z6,z7,z3,z15,z45,z5]),(0,[z6,z7,z2,z3,z4,z46,z16]),(0,[z6,z7,z47,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z48,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z49]),(0,[z50,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z51,z2,z3,z4,z5])],[(0,[z52,z6,z7,z2,z3,z4,z5]),(0,[z6,z53,z7,z2,z3,z4,z5]),(0,[z54,z10,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z55,z45,z5]),(0,[z6,z56,z7,z2,z3,z4,z5]),(0,[z57,z6,z7,z2,z3,z4,z5])],[(0,[z6,z58,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z59,z3,z4,z5]),(0,[z10,z6,z60,z7,z2,z3,z5]),(0,[z61,z6,z7,z2,z3,z4,z5])],[(0,[z20,z6,z62,z7,z2,z3,z5]),(0,[z6,z63,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z64,z5]),(0,[z6,z65,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z66,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z67]),(0,[z6,z7,z2,z68,z3,z4,z5]),(0,[z6,z69,z7,z2,z3,z4,z5])]],
   [[(0,[z6,z7,z2,z70,z3,z4,z5]),(1,[z6,z7,z2,z71,z4,z5]),(0,[z6,z7,z2,z3,z45,z72,z5]),(0,[z6,z7,z2,z3,z4,z5,z73])],[(0,[z10,z6,z7,z74,z2,z3,z5]),(0,[z6,z7,z2,z75,z3,z4,z5])],[(1,[z6,z76,z2,z3,z55,z5])],[(0,[z77,z6,z7,z2,z3,z4,z5]),(1,[z6,z7,z78,z79,z4,z5]),(0,[z6,z7,z2,z18,z3,z5,z19])],[(0,[z6,z80,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z79,z3,z5]),(0,[z6,z38,z7,z2,z3,z45,z5]),(0,[z6,z38,z60,z7,z2,z4,z5])],[(0,[z81,z6,z7,z2,z82,z4,z5]),(0,[z6,z7,z2,z83,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z84]),(0,[z6,z12,z7,z2,z3,z55,z5]),(0,[z6,z7,z85,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z86,z5])],[(0,[z20,z6,z87,z7,z2,z3,z5]),(0,[z6,z38,z7,z2,z3,z88,z5]),(0,[z6,z7,z2,z89,z3,z4,z5]),(0,[z90,z6,z7,z2,z3,z4,z5]),(0,[z91,z6,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z4,z92,z5])],[(0,[z10,z93,z6,z7,z2,z3,z5]),(0,[z10,z6,z76,z7,z2,z3,z5]),(0,[z6,z94,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z95,z3,z45,z5]),(0,[z6,z7,z2,z3,z4,z5,z96]),(0,[z6,z7,z2,z97,z3,z4,z5]),(0,[z6,z7,z2,z98,z3,z4,z5])]],
   [[(0,[z28,z62,z7,z2,z3,z4,z5]),(0,[z6,z39,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z99,z3,z4,z5]),(0,[z6,z7,z2,z79,z3,z4,z5]),(0,[z6,z100,z7,z2,z3,z4,z5])],[(1,[z10,z7,z2,z3,z101,z5]),(0,[z6,z7,z2,z102,z3,z4,z5])],[(0,[z6,z7,z2,z3,z4,z5,z103]),(0,[z6,z7,z2,z3,z4,z104,z5]),(0,[z105,z6,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z4,z5,z106])],[(0,[z6,z7,z2,z3,z107,z4,z5]),(0,[z6,z108,z7,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z3,z101,z5]),(0,[z6,z7,z2,z3,z4,z109,z5]),(0,[z6,z7,z2,z110,z3,z4,z5]),(0,[z6,z7,z2,z3,z45,z111,z5]),(0,[z6,z7,z2,z3,z112,z4,z5]),(0,[z6,z7,z113,z2,z3,z114,z5]),(0,[z6,z7,z2,z3,z4,z5,z115])],[(0,[z6,z7,z116,z2,z3,z4,z5]),(0,[z6,z7,z2,z117,z3,z4,z5]),(0,[z6,z7,z2,z118,z3,z13,z5]),(0,[z119,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z120,z2,z3,z4,z42]),(0,[z6,z7,z2,z3,z121,z4,z5]),(0,[z6,z7,z2,z122,z3,z4,z5]),(0,[z6,z60,z7,z2,z4,z5,z16])],[(0,[z6,z7,z2,z123,z3,z5,z124]),(0,[z6,z125,z7,z2,z3,z4,z5]),(0,[z126,z6,z7,z2,z3,z4,z5]),(0,[z6,z127,z7,z2,z3,z4,z5]),(0,[z6,z128,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z129,z3,z45,z5])],[(0,[z6,z130,z7,z1,z2,z4,z5]),(0,[z6,z7,z2,z3,z4,z131,z5]),(0,[z20,z6,z7,z2,z3,z5,z19]),(0,[z6,z38,z7,z2,z3,z15,z5]),(0,[z6,z7,z132,z2,z3,z4,z5]),(0,[z6,z7,z2,z133,z3,z45,z5]),(0,[z6,z7,z2,z3,z134,z4,z5]),(0,[z6,z7,z2,z3,z4,z135,z5])],[(0,[z6,z7,z1,z2,z3,z4,z5]),(0,[z20,z6,z7,z136,z2,z3,z5]),(0,[z20,z6,z7,z2,z3,z31,z5]),(0,[z10,z10,z6,z7,z2,z3,z5]),(0,[z6,z137,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z138,z3,z4,z5]),(0,[z6,z7,z2,z139,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z140]),(0,[z6,z7,z141,z2,z3,z4,z5]),(0,[z6,z7,z3,z4,z46,z5,z42]),(0,[z142,z6,z7,z2,z3,z4,z5])]],
   [[(0,[z6,z7,z2,z3,z4,z5,z143]),(0,[z6,z7,z2,z144,z3,z4,z5]),(0,[z50,z10,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z145,z3,z4,z5]),(0,[z6,z7,z146,z2,z147,z4,z5]),(0,[z6,z7,z2,z148,z3,z4,z5]),(0,[z6,z7,z2,z18,z3,z92,z5])],[(0,[z105,z6,z7,z2,z3,z4,z124]),(0,[z6,z7,z149,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z114,z13,z5]),(0,[z6,z150,z7,z2,z151,z4,z5]),(0,[z6,z152,z7,z3,z4,z5,z42])],[(0,[z7,z2,z3,z101,z4,z21,z5]),(0,[z10,z6,z152,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z153,z5]),(0,[z6,z7,z2,z3,z154,z4,z5]),(0,[z6,z7,z2,z3,z155,z4,z5])],[(0,[z156,z7,z29,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z3,z9,z5]),(0,[z6,z7,z2,z157,z3,z4,z5]),(0,[z158,z6,z7,z2,z3,z4,z5])],[(0,[z6,z7,z159,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z160,z5]),(0,[z28,z6,z7,z2,z3,z45,z5]),(0,[z105,z6,z7,z2,z3,z15,z5]),(1,[z6,z7,z2,z3,z88,z5])],[(0,[z6,z7,z2,z3,z4,z161,z5]),(0,[z6,z7,z2,z162,z3,z4,z5]),(0,[z20,z6,z7,z2,z3,z5,z42]),(0,[z10,z6,z7,z2,z118,z3,z5]),(0,[z6,z12,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z163,z3,z92,z5]),(0,[z6,z7,z2,z3,z164,z4,z5])],[(0,[z10,z20,z6,z7,z2,z3,z5]),(0,[z20,z6,z7,z2,z3,z165,z5]),(0,[z166,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z167,z2,z3,z4,z5]),(0,[z6,z40,z7,z2,z3,z4,z31]),(1,[z6,z32,z7,z2,z4,z5])],[(0,[z168,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z169,z3,z4,z5]),(0,[z170,z6,z7,z2,z3,z4,z5]),(0,[z93,z81,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z171,z3,z4,z5]),(0,[z6,z7,z2,z172,z3,z4,z5]),(0,[z6,z38,z7,z2,z151,z4,z5]),(0,[z6,z7,z2,z129,z3,z15,z5])]],
   [[(0,[z20,z6,z7,z29,z2,z3,z5]),(0,[z20,z6,z7,z2,z3,z151,z5]),(0,[z6,z7,z2,z3,z165,z45,z5]),(0,[z6,z76,z7,z2,z3,z55,z5]),(0,[z6,z173,z7,z2,z3,z4,z31])],[(0,[z6,z7,z2,z174,z3,z4,z5]),(0,[z6,z175,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z135,z46])],[(0,[z176,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z177,z2,z3,z4,z5]),(0,[z178,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z118,z163,z3,z5]),(0,[z6,z7,z2,z3,z4,z5,z27])],[(0,[z6,z7,z179,z2,z3,z4,z5]),(0,[z20,z6,z7,z2,z82,z3,z5]),(0,[z20,z6,z7,z2,z3,z92,z5]),(0,[z6,z7,z2,z3,z180,z4,z5]),(0,[z6,z7,z2,z3,z21,z45,z5]),(0,[z6,z7,z2,z3,z4,z181,z5]),(0,[z6,z39,z7,z2,z138,z4,z5]),(0,[z6,z7,z2,z3,z15,z5,z19]),(0,[z6,z182,z7,z2,z3,z4,z5])],[(0,[z6,z7,z183,z2,z3,z4,z5]),(0,[z6,z7,z184,z2,z3,z4,z5]),(0,[z20,z6,z7,z2,z185,z3,z5]),(0,[z6,z7,z186,z2,z3,z4,z5]),(1,[z6,z39,z2,z138,z4,z5]),(1,[z6,z7,z2,z3,z15,z5]),(0,[z187,z6,z7,z2,z3,z15,z5])],[(0,[z0,z6,z7,z2,z3,z45,z5]),(0,[z6,z188,z7,z2,z3,z4,z5]),(0,[z189,z10,z6,z7,z2,z3,z5]),(1,[z105,z7,z2,z3,z4,z37]),(0,[z6,z190,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z191]),(0,[z6,z40,z173,z2,z3,z4,z5]),(0,[z192,z6,z7,z2,z3,z4,z5])],[(0,[z28,z6,z7,z2,z3,z15,z5]),(0,[z6,z12,z7,z2,z3,z193,z5]),(1,[z6,z7,z2,z194,z4,z5]),(0,[z6,z7,z2,z3,z114,z55,z5]),(0,[z6,z7,z2,z195,z3,z4,z5])],[(1,[z6,z196,z7,z2,z3,z5]),(0,[z6,z7,z197,z2,z3,z4,z5]),(0,[z20,z6,z6,z7,z2,z3,z5]),(0,[z6,z12,z7,z2,z3,z15,z5]),(0,[z6,z7,z198,z2,z3,z4,z5])]],
   [[(0,[z199,z6,z7,z2,z3,z45,z5]),(0,[z6,z87,z146,z2,z3,z4,z5]),(0,[z6,z7,z2,z129,z151,z4,z5]),(0,[z6,z7,z2,z3,z200,z45,z5]),(0,[z6,z152,z7,z2,z3,z4,z46]),(0,[z6,z7,z113,z2,z163,z4,z5])],[(0,[z6,z7,z2,z3,z4,z201,z5]),(0,[z199,z6,z87,z7,z3,z4,z5]),(0,[z202,z6,z7,z2,z3,z4,z5]),(0,[z105,z6,z7,z2,z3,z4,z37]),(0,[z6,z7,z2,z3,z4,z5,z203])],[(0,[z81,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z165,z15,z5]),(0,[z6,z7,z2,z3,z15,z5,z73]),(0,[z6,z152,z7,z2,z3,z204,z5]),(0,[z205,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z4,z135,z5,z16]),(0,[z6,z7,z2,z3,z4,z5,z206])],[(0,[z156,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z8,z3,z4,z5]),(0,[z35,z6,z7,z2,z3,z4,z5]),(0,[z207,z20,z6,z7,z2,z3,z5]),(0,[z20,z6,z7,z2,z3,z135,z5]),(0,[z208,z10,z6,z7,z2,z3,z5]),(0,[z6,z60,z39,z7,z2,z4,z5]),(0,[z6,z40,z7,z2,z18,z3,z4]),(0,[z6,z7,z2,z3,z209,z4,z5])],[(1,[z6,z7,z2,z3,z4,z210]),(0,[z6,z7,z2,z3,z4,z211,z5])],[(0,[z10,z6,z7,z2,z129,z3,z5])],[(0,[z6,z7,z2,z3,z212,z4,z5]),(0,[z6,z7,z2,z3,z4,z213,z5]),(1,[z6,z7,z2,z3,z214,z5]),(0,[z6,z7,z215,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z216,z5])],[(0,[z0,z6,z7,z2,z3,z15,z5]),(0,[z6,z7,z2,z217,z3,z4,z5]),(0,[z156,z6,z7,z218,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z219,z5]),(0,[z36,z6,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z45,z220,z5]),(0,[z6,z7,z2,z3,z4,z221,z5])]],
   [[(0,[z6,z7,z2,z222,z3,z4,z5]),(0,[z6,z7,z78,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z15,z92,z5])],[(0,[z6,z223,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z224,z3,z4,z5]),(0,[z6,z7,z225,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z45,z31,z5]),(0,[z6,z7,z2,z118,z3,z45,z5]),(1,[z6,z7,z2,z163,z92,z5])],[(0,[z199,z6,z7,z2,z3,z15,z5]),(1,[z6,z7,z226,z2,z3,z5]),(0,[z10,z6,z7,z2,z3,z114,z5]),(0,[z105,z7,z2,z3,z4,z37,z5]),(0,[z6,z7,z2,z3,z4,z227,z5]),(0,[z6,z40,z2,z3,z4,z5,z11]),(0,[z6,z150,z7,z3,z151,z4,z5])],[(0,[z20,z6,z150,z7,z2,z3,z5]),(0,[z10,z6,z7,z2,z3,z46,z5]),(0,[z6,z228,z7,z2,z3,z4,z5]),(0,[z229,z6,z7,z2,z3,z45,z5]),(0,[z6,z7,z74,z3,z15,z4,z5]),(0,[z6,z230,z7,z2,z3,z4,z5])],[(0,[z6,z7,z7,z2,z3,z4,z5]),(0,[z20,z156,z6,z7,z2,z3,z5]),(0,[z54,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z78,z79,z3,z4,z5])],[(0,[z6,z196,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z231,z4,z5]),(0,[z81,z6,z7,z2,z9,z4,z5]),(0,[z6,z232,z7,z2,z3,z4,z5]),(0,[z6,z233,z7,z2,z3,z4,z5]),(1,[z6,z7,z2,z3,z109,z5]),(0,[z6,z7,z2,z3,z234,z4,z5]),(0,[z6,z7,z2,z235,z3,z4,z5]),(1,[z6,z7,z2,z3,z236,z5])],[(0,[z6,z7,z237,z2,z3,z4,z5]),(0,[z6,z7,z2,z79,z82,z4,z5]),(0,[z36,z6,z7,z2,z3,z4,z124]),(0,[z6,z87,z7,z2,z3,z4,z5]),(0,[z6,z39,z2,z138,z3,z4,z5]),(0,[z6,z7,z2,z194,z3,z4,z5]),(1,[z6,z152,z7,z3,z4,z42])],[(0,[z238,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z239,z4,z5]),(1,[z6,z7,z2,z3,z4,z240]),(0,[z6,z38,z7,z2,z165,z4,z5]),(0,[z6,z241,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z45,z5,z42])]],
   [[(0,[z199,z7,z2,z218,z3,z4,z5]),(0,[z20,z6,z7,z146,z2,z3,z5]),(0,[z6,z7,z2,z242,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z243,z5]),(0,[z6,z7,z2,z3,z15,z135,z5])],[(0,[z6,z7,z2,z3,z244,z4,z5]),(0,[z36,z6,z7,z2,z3,z15,z5]),(0,[z6,z7,z2,z3,z4,z245,z5]),(1,[z6,z7,z2,z3,z4,z246]),(0,[z6,z76,z7,z2,z3,z193,z5]),(0,[z6,z7,z2,z3,z114,z4,z193])],[(0,[z199,z6,z7,z2,z3,z4,z210]),(0,[z6,z7,z247,z2,z3,z4,z5])],[(0,[z6,z7,z2,z248,z3,z4,z5]),(0,[z199,z6,z7,z29,z3,z4,z5]),(0,[z199,z6,z7,z2,z3,z249,z5]),(0,[z6,z7,z2,z250,z3,z4,z5]),(1,[z91,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z45,z5]),(0,[z6,z7,z2,z118,z3,z15,z5])],[(0,[z0,z7,z1,z2,z3,z4,z5]),(0,[z6,z7,z226,z2,z218,z3,z5]),(0,[z6,z7,z184,z2,z3,z9,z5]),(0,[z20,z7,z2,z3,z4,z21,z5]),(0,[z6,z251,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z252,z4,z5])],[(0,[z81,z6,z39,z7,z2,z4,z5]),(0,[z6,z7,z2,z3,z4,z88,z5]),(0,[z6,z7,z253,z2,z3,z4,z5]),(0,[z6,z7,z2,z254,z3,z15,z5]),(0,[z6,z7,z2,z255,z3,z4,z5]),(0,[z6,z7,z2,z256,z3,z4,z5]),(0,[z6,z257,z7,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z4,z5,z258]),(0,[z6,z7,z2,z259,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z260,z5])],[(0,[z6,z7,z2,z3,z4,z46,z37]),(0,[z6,z7,z2,z261,z3,z4,z5]),(0,[z6,z262,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z263,z5]),(0,[z6,z7,z2,z3,z114,z193,z5])]],
   [[(0,[z6,z7,z264,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z265]),(0,[z6,z7,z2,z82,z3,z131,z5]),(0,[z20,z6,z173,z7,z2,z3,z5]),(0,[z6,z266,z7,z2,z3,z4,z5]),(0,[z6,z7,z267,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z15,z13,z5])],[(0,[z6,z7,z268,z2,z3,z4,z5]),(0,[z20,z6,z7,z2,z163,z3,z5]),(0,[z10,z7,z2,z3,z101,z4,z5]),(0,[z6,z7,z2,z3,z269,z4,z5]),(0,[z6,z40,z7,z2,z3,z45,z5]),(0,[z270,z6,z7,z2,z3,z45,z5])],[(0,[z6,z7,z271,z2,z3,z4,z5]),(0,[z6,z87,z7,z145,z3,z4,z5]),(0,[z6,z76,z7,z2,z3,z4,z5])],[(0,[z272,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z273,z3,z4,z5]),(1,[z6,z7,z2,z3,z14,z5]),(1,[z6,z173,z2,z3,z4,z31]),(0,[z6,z7,z2,z3,z4,z5,z274]),(0,[z275,z6,z7,z2,z3,z4,z5])],[(0,[z20,z6,z7,z113,z2,z3,z5]),(0,[z6,z39,z7,z2,z4,z135,z5]),(0,[z276,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z277,z4,z5])],[(0,[z81,z20,z6,z7,z2,z3,z5]),(0,[z10,z6,z7,z2,z3,z278,z5]),(0,[z6,z7,z2,z18,z3,z45,z5])],[(0,[z7,z29,z2,z218,z3,z4,z5])],[(0,[z6,z7,z279,z2,z3,z4,z5]),(1,[z93,z7,z2,z9,z4,z5]),(0,[z6,z7,z2,z185,z3,z4,z5]),(0,[z6,z7,z2,z280,z3,z4,z5])]],
   [[(0,[z6,z7,z2,z281,z3,z4,z5]),(1,[z282,z6,z7,z2,z3,z5]),(0,[z6,z173,z7,z2,z3,z4,z42]),(0,[z6,z150,z7,z2,z3,z283,z5]),(0,[z6,z7,z284,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z285,z15,z5]),(0,[z6,z7,z2,z3,z114,z4,z5])],[(0,[z6,z286,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z287,z4,z5]),(1,[z6,z38,z2,z165,z4,z5]),(0,[z6,z150,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z288,z4,z5]),(0,[z6,z7,z2,z129,z3,z289,z5])],[(0,[z290,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z37,z42]),(1,[z6,z7,z2,z3,z291,z5]),(1,[z6,z7,z2,z292,z3,z4]),(0,[z6,z7,z74,z2,z3,z4,z5]),(0,[z6,z7,z2,z163,z3,z45,z5])],[(0,[z0,z10,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z293,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z294]),(0,[z6,z7,z295,z2,z3,z4,z5]),(0,[z6,z40,z7,z2,z3,z15,z5]),(0,[z6,z7,z2,z3,z151,z45,z5]),(0,[z270,z6,z7,z2,z3,z15,z5]),(0,[z6,z7,z296,z2,z3,z4,z5])],[(0,[z297,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z298,z4,z5]),(0,[z6,z7,z2,z299,z3,z4,z5]),(0,[z6,z7,z300,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z4,z5,z124]),(0,[z6,z7,z2,z139,z3,z165,z5]),(0,[z6,z7,z2,z3,z4,z301,z5])],[(0,[z6,z7,z2,z3,z4,z302,z5]),(0,[z6,z7,z2,z3,z4,z249,z5]),(0,[z6,z303,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z304,z5]),(0,[z6,z7,z2,z305,z3,z15,z5])],[(0,[z6,z7,z2,z3,z4,z306,z5]),(0,[z6,z7,z2,z3,z45,z37,z5]),(0,[z6,z87,z7,z146,z3,z4,z5]),(0,[z6,z307,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z79,z4,z5,z16]),(0,[z6,z7,z2,z18,z3,z15,z5]),(0,[z6,z152,z7,z120,z3,z4,z5]),(0,[z6,z152,z7,z2,z3,z308,z5]),(0,[z6,z7,z309,z2,z3,z4,z5])]],
   [[(0,[z6,z7,z2,z3,z101,z4,z5]),(0,[z20,z6,z7,z2,z3,z45,z5]),(0,[z10,z6,z7,z2,z3,z37,z5]),(0,[z6,z7,z2,z3,z310,z4,z5]),(0,[z6,z7,z2,z311,z3,z4,z5]),(0,[z6,z7,z2,z3,z45,z5,z16])],[(0,[z6,z7,z312,z2,z3,z4,z5]),(0,[z20,z6,z7,z120,z2,z3,z5]),(0,[z10,z6,z7,z2,z3,z5,z16]),(0,[z313,z6,z7,z2,z3,z4,z5]),(0,[z314,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z315])],[(0,[z0,z20,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z5,z316]),(0,[z6,z7,z120,z2,z3,z45,z5]),(0,[z6,z7,z317,z2,z3,z15,z5])],[(0,[z207,z6,z7,z2,z3,z4,z5]),(0,[z20,z6,z39,z7,z2,z3,z5]),(0,[z20,z6,z7,z2,z138,z3,z5]),(0,[z6,z7,z2,z318,z3,z4,z5]),(0,[z319,z10,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z320,z5]),(0,[z6,z150,z7,z2,z3,z15,z5]),(0,[z6,z7,z321,z2,z3,z4,z5]),(0,[z322,z6,z7,z2,z3,z4,z5])],[(0,[z28,z6,z1,z2,z3,z4,z5]),(0,[z189,z6,z7,z2,z3,z4,z5]),(0,[z282,z20,z6,z7,z2,z3,z5]),(0,[z6,z323,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z240,z5]),(0,[z6,z7,z2,z3,z4,z5,z324]),(0,[z6,z39,z7,z2,z163,z4,z5]),(0,[z6,z7,z2,z3,z4,z325,z5]),(0,[z6,z7,z2,z163,z3,z15,z5])],[(0,[z6,z6,z7,z2,z3,z4,z5]),(1,[z6,z326,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z327,z4,z5]),(0,[z6,z7,z2,z328,z3,z4,z5]),(0,[z6,z7,z2,z3,z151,z15,z5]),(0,[z6,z7,z113,z2,z3,z5,z19]),(0,[z6,z7,z2,z3,z4,z5,z329])],[(0,[z330,z6,z7,z2,z3,z4,z5]),(0,[z10,z6,z38,z7,z2,z3,z5]),(0,[z6,z331,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z332]),(0,[z6,z333,z7,z2,z3,z4,z5]),(0,[z334,z6,z7,z2,z3,z4,z5])],[(0,[z335,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z336]),(0,[z6,z7,z2,z3,z337,z4,z5]),(0,[z6,z60,z7,z2,z3,z4,z135]),(0,[z6,z7,z2,z338,z3,z4,z5])]],
   [[(0,[z6,z7,z79,z3,z151,z4,z5]),(0,[z6,z7,z339,z2,z3,z4,z5])],[(0,[z93,z7,z2,z3,z9,z4,z5]),(0,[z229,z10,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z340,z5]),(0,[z6,z2,z138,z3,z165,z4,z5]),(0,[z6,z341,z7,z2,z3,z4,z5])],[(0,[z208,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z342,z3,z4,z5]),(0,[z20,z6,z7,z2,z3,z15,z5]),(0,[z20,z6,z7,z2,z18,z3,z5]),(0,[z6,z7,z2,z3,z55,z4,z5]),(0,[z6,z7,z2,z343,z3,z4,z5]),(1,[z6,z7,z2,z3,z344,z5]),(0,[z6,z345,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z204,z5])],[(0,[z6,z7,z2,z3,z4,z5,z346]),(0,[z6,z7,z78,z2,z79,z4,z5]),(0,[z6,z7,z120,z3,z4,z46,z5]),(0,[z6,z60,z7,z2,z3,z4,z16]),(0,[z6,z7,z347,z2,z3,z4,z5])],[(0,[z6,z87,z1,z2,z3,z4,z5]),(0,[z6,z62,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z4,z348,z5]),(0,[z36,z20,z6,z7,z2,z3,z5]),(0,[z6,z349,z7,z2,z3,z4,z5]),(1,[z6,z7,z2,z3,z283,z5]),(0,[z6,z7,z120,z2,z3,z15,z5])],[(0,[z0,z6,z1,z2,z3,z4,z5]),(0,[z350,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z351,z5]),(0,[z6,z7,z74,z132,z3,z4,z5]),(1,[z6,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z15,z45,z5]),(1,[z6,z60,z7,z2,z4,z16]),(0,[z6,z7,z2,z352,z3,z4,z5])],[(0,[z6,z353,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z354,z3,z4,z5]),(0,[z6,z7,z2,z79,z9,z4,z5]),(0,[z10,z6,z7,z247,z2,z3,z5]),(0,[z6,z150,z7,z2,z3,z355,z5])],[(0,[z6,z286,z7,z1,z2,z4,z5]),(1,[z6,z356,z2,z3,z4,z5]),(0,[z6,z7,z226,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z3,z21,z5]),(0,[z6,z7,z2,z3,z357,z4,z5]),(0,[z6,z7,z2,z358,z3,z4,z5])]],
   [[(0,[z6,z152,z7,z2,z3,z4,z5])],[(0,[z6,z38,z7,z2,z3,z4,z5]),(0,[z6,z359,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z13,z5]),(0,[z6,z7,z2,z3,z360,z4,z5])],[(0,[z20,z6,z7,z2,z3,z5,z124]),(0,[z6,z7,z2,z3,z4,z361,z5]),(0,[z6,z7,z362,z2,z3,z4,z5]),(0,[z6,z7,z113,z2,z3,z92,z5])],[(0,[z199,z6,z326,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z363,z3,z5]),(0,[z91,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z113,z2,z118,z4,z5])],[(0,[z6,z326,z7,z2,z3,z4,z5]),(1,[z20,z7,z2,z3,z21,z5]),(0,[z6,z7,z2,z118,z3,z55,z5]),(0,[z6,z7,z2,z95,z3,z4,z5]),(0,[z6,z364,z7,z2,z3,z15,z5]),(0,[z6,z60,z7,z2,z129,z4,z5])],[(0,[z365,z6,z7,z2,z3,z4,z5]),(0,[z10,z6,z62,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z5,z366]),(0,[z6,z367,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z368,z5]),(0,[z6,z369,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z246]),(0,[z6,z7,z2,z3,z370,z4,z5])],[(0,[z6,z62,z7,z2,z3,z15,z5]),(0,[z371,z20,z6,z7,z2,z3,z5]),(0,[z6,z7,z372,z2,z3,z4,z5]),(0,[z6,z7,z146,z2,z3,z109,z5]),(0,[z6,z7,z2,z3,z310,z165,z4]),(0,[z6,z7,z2,z3,z4,z373,z5])],[(0,[z270,z10,z6,z7,z2,z3,z5]),(0,[z105,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z15,z15,z5])]],
   [[(0,[z6,z7,z2,z3,z4,z374,z5])],[(0,[z10,z6,z40,z7,z2,z3,z5]),(1,[z6,z241,z7,z2,z3,z4]),(0,[z375,z6,z7,z2,z3,z4,z5])],[(0,[z6,z1,z2,z145,z3,z4,z5]),(0,[z376,z6,z7,z2,z3,z4,z5]),(0,[z6,z377,z7,z2,z3,z4,z5]),(0,[z6,z40,z7,z2,z3,z14,z5]),(0,[z6,z128,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z129,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z378])],[(1,[z6,z286,z7,z2,z4,z5]),(0,[z199,z23,z6,z7,z3,z4,z5]),(0,[z20,z6,z7,z2,z79,z3,z5]),(0,[z6,z7,z2,z379,z3,z4,z5]),(0,[z6,z7,z2,z3,z45,z380,z5]),(0,[z6,z7,z2,z133,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z381])],[(0,[z93,z6,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z382,z4,z5]),(0,[z10,z6,z87,z7,z2,z3,z5]),(0,[z6,z7,z383,z2,z3,z45,z5]),(0,[z384,z6,z7,z2,z3,z4,z5])],[(0,[z199,z6,z356,z2,z3,z4,z5]),(0,[z6,z7,z120,z2,z3,z236,z5]),(0,[z6,z7,z2,z3,z4,z385,z5])],[(0,[z6,z7,z386,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z387,z5,z11]),(0,[z6,z7,z2,z3,z4,z5,z388])],[(0,[z6,z7,z2,z3,z15,z5,z124]),(0,[z187,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z289,z5])]],
   [[(1,[z6,z7,z2,z3,z249,z5]),(0,[z389,z20,z6,z7,z2,z3,z5]),(0,[z6,z173,z7,z2,z18,z3,z4]),(1,[z6,z7,z132,z3,z45,z5]),(0,[z6,z7,z2,z3,z4,z5,z390])],[(0,[z28,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z391,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z392,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z393]),(0,[z394,z6,z7,z2,z3,z4,z5]),(0,[z6,z395,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z396,z5]),(0,[z6,z7,z2,z18,z118,z3,z5])],[(1,[z6,z7,z2,z8,z3,z5]),(0,[z6,z7,z2,z3,z4,z46,z124]),(0,[z6,z7,z146,z2,z3,z397,z5]),(0,[z6,z12,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z194,z4,z13,z5]),(1,[z6,z7,z2,z3,z355,z5]),(0,[z6,z7,z2,z3,z4,z5,z398]),(0,[z6,z7,z2,z3,z399,z4,z5])],[(0,[z6,z7,z2,z400,z3,z4,z5]),(0,[z401,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z402,z5]),(0,[z6,z7,z2,z3,z45,z5,z19])],[(0,[z6,z7,z2,z3,z403,z4,z5]),(0,[z10,z6,z7,z2,z3,z5,z19]),(0,[z6,z38,z7,z2,z138,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z404])],[(0,[z6,z7,z2,z3,z214,z4,z5]),(0,[z20,z6,z7,z132,z2,z3,z5]),(0,[z10,z6,z7,z2,z3,z31,z5]),(0,[z6,z150,z7,z2,z3,z4,z398]),(0,[z6,z7,z2,z3,z4,z5,z405])],[(0,[z93,z6,z7,z2,z3,z15,z5]),(0,[z20,z6,z7,z2,z3,z13,z5]),(1,[z6,z7,z2,z123,z3,z5]),(0,[z6,z7,z2,z3,z4,z5,z406]),(0,[z6,z7,z267,z2,z3,z165,z5])],[(0,[z6,z7,z2,z3,z407,z4,z5]),(0,[z6,z7,z2,z408,z3,z4,z5])]],
   [[(0,[z6,z7,z268,z1,z3,z4,z5]),(0,[z6,z7,z2,z218,z3,z45,z5]),(0,[z6,z7,z409,z2,z3,z4,z5]),(0,[z6,z7,z2,z82,z151,z4,z5]),(0,[z6,z7,z2,z3,z4,z410,z5]),(1,[z6,z40,z2,z3,z4,z11])],[(0,[z6,z7,z2,z3,z4,z411,z5]),(0,[z93,z6,z38,z7,z2,z4,z5]),(0,[z6,z7,z2,z3,z4,z412,z5]),(0,[z20,z6,z7,z2,z145,z3,z5]),(0,[z413,z10,z6,z7,z2,z3,z5]),(0,[z10,z105,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z414,z4,z5]),(0,[z6,z7,z2,z3,z415,z4,z5]),(0,[z6,z7,z2,z416,z3,z4,z5]),(0,[z6,z40,z60,z7,z2,z3,z4]),(0,[z6,z7,z2,z3,z4,z417,z5])],[(0,[z0,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z418,z3,z4,z5]),(0,[z6,z7,z2,z3,z419,z4,z5]),(1,[z6,z7,z2,z3,z420,z5]),(0,[z6,z7,z2,z3,z4,z5,z421])],[(0,[z10,z6,z7,z2,z3,z5,z42]),(0,[z6,z422,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z344,z5])],[(1,[z6,z7,z2,z3,z4,z366]),(0,[z282,z6,z7,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z3,z165,z5]),(0,[z6,z7,z2,z3,z4,z423,z5]),(0,[z36,z7,z2,z3,z4,z5,z124]),(0,[z6,z7,z2,z3,z45,z5,z124]),(1,[z6,z7,z2,z3,z204,z5]),(0,[z6,z7,z424,z2,z3,z4,z5])],[(0,[z199,z6,z7,z2,z3,z4,z5]),(1,[z156,z7,z29,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z425,z5]),(0,[z6,z7,z2,z118,z3,z193,z5])],[(0,[z426,z6,z7,z2,z3,z4,z5]),(0,[z427,z6,z7,z2,z3,z4,z5]),(0,[z10,z6,z7,z29,z2,z3,z5]),(0,[z6,z7,z29,z2,z3,z214,z5]),(0,[z10,z6,z7,z2,z3,z151,z5]),(0,[z6,z39,z7,z2,z79,z4,z5]),(0,[z6,z7,z2,z3,z236,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z428])],[(0,[z429,z6,z7,z2,z3,z4,z5]),(0,[z430,z6,z7,z2,z3,z4,z5])]],
   [[(1,[z365,z6,z7,z3,z4,z5]),(1,[z6,z7,z268,z3,z4,z5]),(0,[z6,z7,z431,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z432,z5]),(0,[z6,z433,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z434,z4,z5]),(0,[z6,z435,z7,z2,z3,z4,z5]),(0,[z6,z60,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z45,z92,z5]),(1,[z6,z7,z2,z129,z4,z135])],[(0,[z199,z6,z7,z218,z3,z4,z5]),(0,[z6,z436,z7,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z82,z3,z5]),(0,[z10,z6,z7,z2,z3,z92,z5]),(0,[z6,z7,z2,z3,z437,z4,z5]),(0,[z6,z438,z7,z2,z3,z4,z5]),(0,[z439,z6,z7,z2,z3,z4,z5]),(0,[z6,z440,z7,z2,z3,z4,z5])],[(0,[z319,z6,z7,z2,z3,z4,z5]),(0,[z20,z6,z7,z2,z218,z3,z5]),(0,[z6,z7,z2,z218,z3,z15,z5]),(0,[z20,z6,z7,z441,z2,z3,z5]),(0,[z105,z20,z6,z7,z2,z3,z5]),(0,[z6,z7,z442,z2,z3,z4,z5]),(0,[z443,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z444,z5]),(0,[z6,z7,z2,z3,z4,z5,z445])],[(1,[z10,z6,z7,z2,z3,z5]),(0,[z20,z6,z7,z2,z3,z55,z5]),(0,[z6,z7,z2,z3,z4,z135,z42]),(0,[z6,z7,z2,z446,z3,z4,z5]),(0,[z6,z7,z447,z2,z3,z4,z5])],[(0,[z36,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z448,z4,z5]),(0,[z23,z6,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z449,z3,z4,z5]),(1,[z6,z7,z2,z3,z450,z5]),(0,[z6,z7,z2,z3,z450,z135,z5])],[(1,[z28,z62,z2,z3,z4,z5]),(0,[z10,z6,z6,z7,z2,z3,z5])],[(1,[z6,z7,z451,z2,z3,z5]),(0,[z6,z7,z2,z363,z3,z4,z5]),(0,[z6,z173,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z118,z3,z4,z5]),(0,[z6,z7,z2,z3,z92,z193,z5]),(0,[z6,z7,z2,z18,z3,z114,z5]),(0,[z6,z7,z2,z3,z452,z4,z5])],[(0,[z36,z6,z40,z7,z2,z3,z4]),(0,[z6,z7,z453,z2,z3,z4,z5]),(0,[z6,z7,z2,z454,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z193,z5])]],
   [[(0,[z229,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z132,z3,z4,z45,z5]),(0,[z6,z7,z2,z3,z45,z135,z5]),(0,[z6,z7,z2,z254,z3,z4,z5]),(0,[z6,z7,z120,z2,z3,z396,z5])],[(0,[z6,z455,z7,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z3,z135,z5]),(0,[z6,z7,z456,z2,z3,z4,z5]),(0,[z6,z7,z2,z292,z3,z4,z5]),(1,[z6,z7,z2,z3,z4,z398])],[(0,[z199,z156,z7,z2,z3,z4,z5]),(0,[z199,z6,z7,z2,z3,z4,z366]),(1,[z20,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z457,z5]),(0,[z6,z7,z2,z3,z15,z155,z5]),(0,[z6,z7,z2,z458,z3,z15,z5]),(0,[z6,z60,z7,z2,z3,z15,z5]),(0,[z6,z152,z7,z2,z3,z4,z42]),(0,[z6,z7,z2,z459,z3,z4,z5]),(1,[z6,z7,z2,z18,z3,z19])],[(0,[z20,z6,z455,z7,z2,z3,z5]),(1,[z6,z7,z2,z460,z4,z5]),(0,[z6,z7,z2,z163,z3,z114,z5]),(0,[z6,z7,z2,z18,z3,z4,z193])],[(0,[z6,z87,z62,z2,z3,z4,z5]),(0,[z6,z461,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z462,z3,z4,z5])],[(0,[z0,z6,z62,z2,z3,z4,z5]),(0,[z6,z7,z2,z463,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z11]),(0,[z6,z7,z2,z3,z4,z200,z5]),(0,[z6,z464,z7,z2,z3,z4,z5])],[(0,[z371,z6,z7,z2,z3,z4,z5]),(0,[z199,z6,z7,z2,z465,z4,z5]),(0,[z23,z6,z7,z2,z3,z15,z5]),(0,[z6,z7,z146,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z13,z5,z19])],[(0,[z6,z7,z2,z3,z466,z4,z5]),(0,[z6,z467,z7,z2,z3,z4,z5]),(0,[z6,z39,z7,z2,z118,z4,z5]),(0,[z6,z7,z2,z292,z3,z4,z13]),(0,[z6,z7,z113,z2,z3,z45,z5]),(0,[z6,z468,z7,z2,z3,z4,z5]),(1,[z6,z7,z2,z3,z114,z193])]],
   [[(0,[z6,z7,z2,z3,z4,z469,z5]),(0,[z20,z6,z7,z78,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z4,z5]),(0,[z6,z241,z7,z2,z3,z165,z4]),(0,[z6,z7,z2,z3,z15,z55,z5]),(0,[z6,z173,z7,z2,z3,z15,z5]),(0,[z6,z150,z7,z2,z3,z4,z243])],[(0,[z6,z7,z2,z3,z4,z470,z5]),(1,[z199,z7,z218,z3,z4,z5]),(0,[z199,z10,z6,z7,z2,z3,z5]),(0,[z10,z6,z150,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z471,z4,z5]),(0,[z472,z6,z7,z2,z3,z4,z5]),(1,[z6,z7,z2,z3,z289,z5])],[(0,[z10,z156,z6,z7,z2,z3,z5]),(0,[z6,z152,z7,z2,z337,z4,z5])],[(1,[z6,z7,z2,z3,z414,z5]),(0,[z6,z7,z2,z3,z285,z4,z5]),(0,[z6,z60,z173,z7,z2,z3,z4]),(0,[z6,z7,z2,z3,z4,z355,z5]),(0,[z6,z152,z7,z2,z97,z4,z5]),(1,[z6,z7,z2,z3,z396,z5]),(0,[z6,z7,z2,z3,z135,z5,z27])],[],[(0,[z6,z62,z2,z145,z3,z4,z5]),(0,[z473,z6,z7,z2,z3,z4,z5]),(0,[z6,z38,z7,z2,z4,z135,z5]),(0,[z474,z6,z7,z2,z3,z4,z5])],[(0,[z270,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z124,z42]),(0,[z6,z40,z7,z2,z3,z4,z5])],[(0,[z6,z7,z475,z2,z3,z4,z5]),(0,[z6,z7,z476,z2,z3,z4,z5]),(0,[z477,z6,z7,z2,z3,z4,z5]),(0,[z478,z6,z7,z2,z3,z4,z5]),(0,[z6,z479,z7,z2,z3,z4,z5])]],
   [[(0,[z199,z20,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z9,z45,z5]),(0,[z389,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z480,z3,z4,z5]),(0,[z6,z7,z146,z2,z3,z15,z5]),(0,[z6,z7,z2,z3,z4,z481,z5]),(0,[z482,z6,z7,z2,z3,z4,z5])],[(0,[z20,z6,z7,z1,z2,z3,z5]),(0,[z93,z20,z6,z7,z2,z3,z5]),(0,[z6,z483,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z283,z4,z5]),(0,[z6,z7,z2,z305,z3,z4,z5]),(0,[z6,z7,z484,z2,z3,z4,z5]),(0,[z6,z7,z113,z2,z3,z15,z5])],[(0,[z6,z7,z2,z3,z485,z4,z5]),(0,[z6,z7,z2,z486,z3,z4,z5]),(0,[z20,z6,z12,z7,z2,z3,z5]),(0,[z6,z7,z2,z18,z3,z4,z5])],[(0,[z6,z7,z2,z3,z487,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z5]),(1,[z36,z7,z2,z3,z4,z124]),(0,[z6,z7,z2,z123,z3,z4,z5]),(1,[z6,z7,z2,z3,z5,z488]),(0,[z6,z7,z2,z3,z13,z92,z5]),(0,[z6,z7,z2,z71,z3,z4,z5]),(0,[z6,z7,z2,z489,z3,z15,z5]),(0,[z6,z7,z2,z3,z193,z5,z19])],[(0,[z365,z6,z7,z1,z3,z4,z5]),(1,[z10,z20,z7,z2,z3,z5]),(0,[z20,z6,z7,z2,z3,z287,z5]),(0,[z20,z6,z7,z2,z3,z193,z5]),(0,[z6,z7,z2,z3,z4,z5,z490])],[(0,[z6,z7,z2,z3,z4,z5,z491]),(0,[z10,z6,z7,z2,z480,z3,z5]),(0,[z6,z7,z317,z2,z3,z4,z5]),(0,[z6,z7,z2,z492,z3,z4,z5])],[(0,[z6,z7,z2,z3,z4,z493,z5]),(0,[z6,z494,z7,z2,z3,z4,z5]),(0,[z10,z6,z173,z7,z2,z3,z5]),(0,[z105,z36,z7,z2,z3,z4,z5]),(0,[z6,z76,z7,z113,z2,z3,z5]),(0,[z6,z150,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z495,z5]),(0,[z6,z7,z2,z129,z4,z135,z5])],[(1,[z6,z7,z2,z3,z496,z5]),(1,[z6,z7,z2,z3,z425,z5]),(0,[z6,z7,z2,z174,z82,z3,z5]),(0,[z10,z6,z7,z2,z163,z3,z5]),(0,[z6,z497,z7,z2,z3,z4,z5]),(0,[z6,z498,z7,z2,z3,z4,z5]),(0,[z499,z6,z7,z2,z3,z4,z5]),(0,[z6,z12,z2,z3,z4,z13,z5]),(0,[z6,z7,z2,z163,z3,z4,z5]),(0,[z6,z7,z500,z2,z3,z4,z5])]],
   [[(0,[z7,z2,z82,z3,z9,z4,z5]),(1,[z6,z7,z184,z2,z3,z5]),(0,[z6,z7,z2,z501,z3,z4,z5]),(0,[z6,z40,z7,z2,z129,z3,z4]),(0,[z6,z7,z2,z3,z151,z4,z5]),(0,[z6,z7,z502,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z503,z4,z5]),(0,[z6,z7,z2,z3,z4,z504,z5]),(0,[z505,z6,z7,z2,z3,z4,z5]),(0,[z6,z40,z7,z2,z3,z4,z46]),(1,[z6,z7,z2,z3,z308,z5])],[(0,[z6,z7,z2,z3,z9,z15,z5]),(0,[z20,z6,z7,z2,z3,z5,z11]),(0,[z10,z6,z7,z113,z2,z3,z5]),(1,[z6,z87,z146,z3,z4,z5]),(0,[z6,z7,z2,z3,z506,z4,z5]),(0,[z6,z7,z2,z507,z3,z45,z5])],[],[(0,[z20,z28,z6,z7,z2,z3,z5]),(0,[z6,z7,z451,z2,z218,z3,z5]),(0,[z93,z6,z7,z2,z82,z4,z5]),(0,[z6,z7,z2,z3,z4,z508,z5]),(1,[z6,z7,z2,z3,z4,z243]),(0,[z6,z7,z2,z509,z3,z4,z5])],[(1,[z6,z7,z2,z174,z3,z5]),(0,[z20,z6,z7,z2,z3,z4,z5]),(0,[z6,z38,z7,z2,z163,z4,z5]),(0,[z6,z40,z7,z2,z3,z114,z4])],[(0,[z6,z510,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z511,z5])],[(1,[z6,z130,z7,z2,z4,z5]),(0,[z6,z7,z120,z2,z3,z4,z5])]],
   [[(1,[z6,z7,z2,z3,z512,z5]),(0,[z6,z7,z513,z2,z3,z4,z5]),(0,[z6,z7,z2,z82,z3,z45,z5]),(0,[z20,z6,z60,z7,z2,z3,z5]),(0,[z413,z6,z7,z2,z3,z4,z5]),(0,[z6,z514,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z515,z4,z5]),(0,[z516,z6,z7,z2,z3,z4,z5])],[(0,[z6,z517,z7,z1,z2,z3,z4]),(0,[z6,z7,z2,z3,z4,z5,z518]),(0,[z473,z10,z6,z7,z2,z3,z5]),(0,[z6,z7,z519,z2,z3,z4,z5]),(1,[z6,z7,z2,z139,z3,z5]),(0,[z6,z173,z2,z3,z4,z31,z5]),(0,[z6,z7,z2,z3,z420,z4,z5]),(0,[z6,z7,z2,z3,z15,z193,z5])],[(0,[z6,z7,z2,z520,z3,z4,z5]),(0,[z23,z10,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z521,z4,z5]),(0,[z522,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z523])],[(0,[z23,z156,z6,z7,z3,z4,z5]),(0,[z20,z6,z7,z74,z2,z3,z5]),(0,[z6,z7,z146,z2,z3,z4,z240]),(0,[z6,z76,z2,z3,z55,z4,z5]),(0,[z6,z7,z78,z2,z151,z4,z5])],[(0,[z6,z524,z7,z2,z3,z4,z5]),(0,[z525,z6,z7,z2,z3,z4,z5]),(1,[z6,z7,z120,z3,z4,z46])],[(0,[z6,z7,z2,z3,z526,z4,z5]),(0,[z527,z6,z7,z2,z3,z4,z5]),(0,[z6,z528,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z529]),(0,[z6,z7,z29,z2,z3,z45,z5]),(0,[z105,z6,z40,z7,z2,z3,z4]),(0,[z6,z7,z146,z2,z3,z4,z246]),(0,[z6,z32,z7,z2,z4,z5,z11]),(0,[z6,z7,z2,z3,z45,z45,z5])],[(0,[z10,z6,z7,z2,z3,z45,z5]),(0,[z6,z7,z530,z2,z3,z4,z5]),(0,[z6,z531,z7,z2,z3,z4,z5])],[(0,[z6,z7,z532,z2,z3,z4,z5]),(0,[z6,z7,z2,z533,z3,z4,z5]),(0,[z10,z6,z7,z120,z2,z3,z5]),(0,[z23,z6,z7,z146,z3,z4,z5]),(0,[z6,z364,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z15,z5,z11]),(0,[z6,z7,z2,z534,z3,z4,z5])]],
   [[(0,[z23,z6,z87,z2,z3,z4,z5]),(0,[z6,z7,z2,z151,z4,z5,z16]),(1,[z6,z7,z74,z3,z15,z5])],[(0,[z6,z62,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z535,z5]),(0,[z270,z20,z6,z7,z2,z3,z5]),(0,[z23,z20,z6,z7,z2,z3,z5]),(0,[z20,z6,z76,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z5,z536]),(0,[z10,z6,z39,z7,z2,z3,z5]),(0,[z10,z6,z7,z2,z138,z3,z5]),(0,[z6,z7,z2,z3,z4,z5,z537]),(0,[z6,z7,z538,z2,z3,z4,z5]),(0,[z6,z7,z2,z539,z3,z4,z5])],[(1,[z6,z7,z2,z3,z4,z5]),(0,[z6,z62,z7,z2,z3,z470,z5]),(0,[z6,z7,z2,z82,z3,z15,z5]),(0,[z20,z6,z7,z2,z3,z5,z491]),(0,[z6,z7,z2,z3,z4,z540,z5]),(0,[z7,z2,z3,z4,z37,z5,z124]),(0,[z6,z7,z2,z3,z4,z5,z541]),(0,[z6,z7,z542,z2,z3,z4,z5]),(0,[z6,z543,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z15,z4,z5]),(0,[z6,z65,z7,z2,z3,z45,z5]),(0,[z6,z7,z120,z2,z3,z4,z46]),(0,[z6,z7,z2,z118,z4,z92,z5])],[(1,[z6,z7,z2,z3,z470,z5]),(0,[z6,z7,z2,z3,z4,z544,z5]),(0,[z6,z7,z2,z3,z4,z545,z5])],[(0,[z6,z7,z136,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z546,z5])],[(0,[z20,z6,z7,z2,z3,z101,z5]),(0,[z6,z7,z2,z3,z4,z547,z5]),(0,[z6,z548,z7,z2,z3,z4,z5])],[(0,[z199,z6,z7,z2,z3,z512,z5]),(0,[z6,z2,z3,z4,z31,z5,z11])],[(0,[z6,z7,z29,z2,z3,z15,z5]),(0,[z6,z7,z2,z3,z4,z5,z549]),(0,[z6,z7,z550,z2,z3,z4,z5]),(0,[z6,z7,z2,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z551,z4,z5]),(0,[z552,z6,z7,z2,z3,z4,z5])]],
   [[(0,[z6,z553,z7,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z3,z15,z5]),(0,[z10,z6,z7,z2,z18,z3,z5]),(0,[z6,z7,z2,z3,z4,z24,z5]),(0,[z6,z7,z2,z3,z165,z4,z5]),(0,[z6,z7,z2,z3,z554,z4,z5])],[(0,[z6,z7,z2,z3,z555,z4,z5])],[(0,[z6,z556,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z557,z4,z5]),(0,[z6,z56,z7,z2,z3,z15,z5]),(0,[z6,z7,z2,z3,z15,z481,z5]),(0,[z6,z558,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z559,z4,z5])],[(1,[z6,z7,z2,z533,z4,z5]),(0,[z6,z7,z2,z3,z4,z560,z5]),(0,[z20,z6,z7,z2,z3,z511,z5]),(0,[z6,z39,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z79,z3,z45,z5])],[(0,[z20,z6,z152,z7,z2,z3,z5]),(0,[z10,z36,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z5,z488]),(0,[z6,z561,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z45,z5,z11]),(0,[z562,z6,z7,z2,z3,z4,z5])],[(0,[z6,z130,z7,z2,z3,z4,z5]),(0,[z563,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z564,z5]),(0,[z20,z6,z7,z2,z3,z9,z5]),(0,[z23,z6,z2,z145,z3,z4,z5]),(0,[z6,z7,z2,z43,z3,z5,z11]),(0,[z6,z7,z2,z3,z4,z220,z5]),(0,[z6,z7,z565,z2,z3,z4,z5]),(0,[z566,z6,z7,z2,z3,z4,z5])],[(0,[z6,z7,z2,z567,z3,z4,z5]),(0,[z6,z7,z2,z9,z151,z4,z5]),(0,[z568,z20,z6,z7,z2,z3,z5]),(0,[z10,z6,z7,z2,z3,z5,z294]),(1,[z6,z7,z267,z2,z3,z5])],[(0,[z20,z6,z7,z2,z118,z3,z5]),(0,[z10,z6,z7,z2,z3,z569,z5])]],
   [[(0,[z20,z20,z6,z7,z2,z3,z5]),(0,[z10,z6,z7,z2,z3,z5,z124]),(0,[z6,z7,z2,z3,z4,z46,z5]),(0,[z570,z6,z7,z2,z3,z4,z5])],[(0,[z93,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z571,z3,z4,z5]),(0,[z6,z7,z2,z3,z572,z4,z5]),(0,[z6,z7,z383,z2,z3,z4,z5]),(0,[z6,z7,z132,z2,z3,z45,z5]),(0,[z6,z7,z2,z2,z3,z15,z5])],[(0,[z6,z223,z7,z1,z2,z3,z4]),(0,[z6,z7,z1,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z15,z101,z5]),(0,[z6,z7,z2,z138,z3,z45,z5])],[(1,[z6,z7,z2,z465,z4,z5]),(0,[z573,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z145,z3,z45,z5]),(0,[z6,z574,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z575,z3,z4,z5]),(0,[z6,z576,z7,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z308,z4,z5])],[(0,[z6,z577,z7,z1,z2,z3,z5]),(0,[z6,z39,z7,z2,z3,z15,z5]),(0,[z6,z7,z2,z578,z3,z4,z5]),(0,[z6,z7,z2,z79,z3,z15,z5]),(1,[z187,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z5,z42])],[(0,[z579,z6,z7,z2,z3,z4,z5]),(0,[z6,z580,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z414,z37,z5]),(0,[z6,z581,z7,z2,z3,z4,z5]),(0,[z6,z7,z582,z2,z3,z4,z5])],[(0,[z28,z6,z62,z2,z3,z4,z5]),(0,[z6,z583,z7,z2,z3,z4,z5]),(0,[z6,z7,z451,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z584]),(0,[z6,z7,z585,z2,z3,z4,z5])]],
   [[(0,[z282,z156,z6,z7,z2,z3,z5]),(0,[z527,z20,z6,z7,z2,z3,z5]),(0,[z20,z6,z40,z7,z2,z3,z5]),(0,[z6,z146,z2,z145,z3,z4,z5]),(0,[z6,z7,z2,z3,z13,z45,z5]),(0,[z586,z6,z7,z2,z3,z4,z5]),(0,[z6,z152,z7,z2,z3,z45,z5])],[(0,[z199,z6,z7,z2,z533,z4,z5]),(0,[z6,z7,z2,z3,z569,z4,z5]),(0,[z587,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z397,z4,z5]),(0,[z6,z150,z7,z2,z79,z4,z5]),(0,[z6,z7,z2,z3,z588,z4,z5])],[(0,[z6,z7,z589,z2,z3,z4,z5]),(1,[z6,z7,z2,z43,z3,z5]),(1,[z6,z7,z2,z3,z387,z5]),(0,[z6,z7,z2,z3,z590,z4,z5])],[(0,[z6,z7,z2,z3,z4,z591,z5]),(0,[z6,z7,z2,z592,z3,z4,z5]),(0,[z6,z7,z2,z3,z15,z21,z5]),(0,[z6,z12,z7,z2,z163,z3,z5]),(0,[z6,z7,z2,z3,z55,z5,z19]),(0,[z6,z40,z7,z2,z3,z4,z11]),(0,[z6,z7,z132,z2,z3,z15,z5]),(0,[z6,z7,z2,z163,z4,z92,z5])],[(0,[z6,z7,z1,z2,z3,z15,z5]),(0,[z93,z6,z7,z2,z9,z4,z5]),(0,[z6,z7,z2,z3,z37,z5,z488]),(0,[z593,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z594,z2,z3,z4,z5]),(0,[z6,z7,z2,z138,z3,z15,z5]),(0,[z6,z150,z7,z78,z3,z4,z5]),(0,[z6,z595,z7,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z512,z4,z5]),(0,[z6,z7,z2,z218,z3,z4,z5]),(0,[z6,z7,z596,z2,z3,z4,z5]),(0,[z6,z7,z2,z145,z3,z15,z5]),(0,[z6,z597,z7,z2,z3,z4,z5]),(0,[z6,z173,z7,z2,z3,z4,z11]),(0,[z6,z7,z2,z163,z3,z5,z19])],[(0,[z10,z6,z349,z7,z2,z3,z5]),(0,[z6,z39,z7,z2,z151,z4,z5]),(0,[z6,z12,z7,z113,z2,z3,z5]),(0,[z6,z7,z2,z3,z598,z4,z5])],[(0,[z20,z6,z7,z2,z129,z3,z5]),(1,[z6,z7,z2,z363,z3,z5]),(0,[z6,z38,z7,z2,z79,z4,z5]),(0,[z6,z7,z2,z3,z15,z112,z5]),(0,[z6,z7,z2,z3,z4,z5,z599])]],
   [[(0,[z600,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z601]),(0,[z6,z76,z7,z2,z3,z13,z5])],[(0,[z6,z577,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z602]),(0,[z6,z7,z2,z3,z4,z603,z5])],[(1,[z229,z6,z7,z2,z3,z5]),(0,[z81,z7,z2,z82,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z278,z5]),(0,[z6,z7,z2,z604,z3,z4,z5]),(1,[z6,z7,z2,z3,z310,z4]),(0,[z6,z7,z2,z3,z605,z4,z5]),(0,[z6,z152,z7,z2,z3,z15,z5]),(0,[z6,z606,z7,z2,z3,z4,z5])],[(0,[z6,z607,z7,z2,z3,z4,z5]),(0,[z10,z6,z7,z132,z2,z3,z5]),(0,[z6,z7,z2,z3,z608,z4,z5]),(0,[z6,z7,z2,z147,z3,z4,z5]),(0,[z6,z609,z7,z2,z3,z4,z5])],[(0,[z229,z156,z6,z7,z2,z3,z5]),(0,[z93,z6,z39,z7,z2,z4,z5]),(0,[z610,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z441,z2,z3,z4,z5]),(0,[z20,z6,z7,z2,z3,z114,z5]),(0,[z10,z6,z7,z476,z2,z3,z5]),(0,[z10,z6,z7,z2,z3,z13,z5]),(0,[z6,z7,z2,z3,z4,z5,z611])],[(0,[z6,z517,z7,z2,z3,z4,z5]),(0,[z81,z6,z7,z2,z3,z45,z5]),(0,[z20,z6,z7,z2,z3,z46,z5]),(0,[z6,z7,z2,z3,z612,z4,z5]),(0,[z6,z7,z2,z458,z3,z4,z5]),(0,[z6,z60,z7,z2,z3,z4,z5]),(0,[z6,z613,z7,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z4,z5,z614]),(0,[z156,z6,z7,z2,z3,z45,z5]),(0,[z6,z7,z615,z2,z3,z4,z5])],[(0,[z616,z6,z7,z2,z3,z4,z5]),(0,[z156,z6,z87,z7,z3,z4,z5]),(0,[z10,z6,z7,z2,z145,z3,z5]),(1,[z23,z6,z145,z3,z4,z5]),(0,[z6,z7,z2,z71,z4,z13,z5]),(0,[z6,z7,z2,z3,z4,z5,z617])]],
   [[(0,[z618,z6,z7,z2,z3,z4,z5]),(1,[z6,z7,z2,z3,z415,z5]),(0,[z6,z7,z2,z3,z605,z4,z13]),(0,[z6,z7,z2,z3,z55,z92,z5]),(0,[z6,z7,z2,z3,z619,z4,z5]),(0,[z6,z7,z78,z2,z3,z344,z5]),(0,[z6,z7,z2,z129,z79,z4,z5])],[(0,[z6,z7,z2,z3,z4,z72,z5]),(0,[z6,z7,z2,z620,z3,z4,z5]),(0,[z10,z6,z7,z146,z2,z3,z5]),(0,[z23,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z621,z4,z5])],[(0,[z30,z20,z6,z7,z2,z3,z5]),(1,[z6,z7,z2,z3,z24,z5]),(0,[z6,z7,z2,z622,z3,z4,z5]),(0,[z6,z7,z2,z623,z3,z4,z5])],[(0,[z6,z173,z7,z2,z3,z4,z5]),(0,[z6,z7,z78,z2,z3,z45,z5])],[(0,[z6,z7,z2,z3,z624,z4,z5]),(0,[z6,z7,z2,z3,z625,z4,z5]),(1,[z6,z7,z2,z3,z41,z5]),(0,[z6,z7,z2,z3,z4,z626,z5]),(1,[z6,z7,z113,z2,z118,z5])],[(1,[z6,z517,z7,z2,z3,z4]),(0,[z6,z7,z2,z3,z4,z37,z5]),(0,[z6,z7,z2,z3,z4,z5,z627])],[(1,[z6,z577,z7,z2,z3,z5]),(0,[z6,z7,z628,z2,z3,z4,z5]),(0,[z6,z76,z7,z2,z163,z3,z5]),(0,[z6,z7,z2,z3,z4,z5,z629]),(0,[z6,z7,z2,z3,z4,z5,z16])],[(0,[z81,z6,z7,z2,z3,z15,z5]),(0,[z20,z6,z7,z2,z318,z3,z5]),(0,[z10,z20,z7,z2,z3,z4,z5])]],
   [[(0,[z10,z6,z7,z2,z218,z3,z5]),(0,[z156,z6,z7,z2,z3,z15,z5]),(0,[z630,z6,z7,z2,z3,z4,z5]),(0,[z6,z38,z7,z2,z118,z4,z5]),(0,[z6,z7,z2,z3,z4,z631,z5])],[(0,[z6,z62,z7,z2,z3,z496,z5]),(0,[z6,z7,z356,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z3,z55,z5]),(0,[z6,z87,z7,z2,z3,z45,z5]),(0,[z6,z632,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z15,z31,z5])],[(0,[z6,z7,z2,z3,z3,z4,z5]),(0,[z81,z6,z38,z7,z2,z4,z5]),(0,[z105,z6,z173,z7,z2,z3,z4]),(0,[z6,z633,z7,z2,z3,z4,z5]),(1,[z6,z7,z2,z3,z605,z4]),(0,[z6,z7,z2,z3,z634,z45,z5]),(0,[z6,z7,z2,z3,z15,z46,z5])],[(0,[z6,z7,z2,z3,z635,z4,z5]),(0,[z10,z81,z6,z7,z2,z3,z5]),(0,[z6,z7,z146,z2,z3,z4,z5]),(1,[z6,z7,z2,z4,z5,z332]),(0,[z6,z7,z2,z3,z4,z636,z5]),(0,[z6,z7,z2,z3,z637,z4,z5])],[(0,[z6,z7,z638,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z111,z5]),(0,[z6,z12,z7,z2,z18,z3,z5]),(1,[z6,z7,z2,z337,z4,z5]),(0,[z6,z7,z113,z2,z3,z4,z5])],[(0,[z639,z6,z7,z2,z3,z4,z5]),(0,[z23,z6,z7,z145,z3,z4,z5]),(0,[z6,z38,z2,z3,z165,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z640]),(0,[z6,z173,z7,z2,z129,z3,z4]),(0,[z6,z7,z78,z2,z3,z15,z5]),(1,[z6,z7,z2,z97,z4,z5])],[(0,[z6,z196,z7,z1,z2,z3,z5]),(0,[z568,z6,z7,z2,z3,z4,z5]),(0,[z6,z39,z7,z2,z165,z4,z5]),(0,[z641,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z642,z2,z3,z4,z5]),(1,[z6,z12,z2,z3,z13,z5]),(0,[z6,z7,z2,z643,z3,z4,z5]),(0,[z6,z173,z7,z2,z3,z4,z46]),(0,[z6,z644,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z489,z3,z4,z5])],[(1,[z6,z7,z2,z147,z4,z5]),(0,[z6,z7,z2,z3,z4,z645,z5]),(0,[z6,z7,z2,z3,z45,z5,z405]),(0,[z6,z7,z2,z3,z15,z5,z42]),(0,[z646,z6,z7,z2,z3,z4,z5]),(0,[z6,z647,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z648])]],
   [[(1,[z6,z223,z7,z2,z3,z4]),(0,[z6,z7,z649,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z650,z5]),(0,[z6,z7,z651,z2,z3,z4,z5])],[(0,[z156,z6,z7,z29,z3,z4,z5]),(0,[z6,z7,z2,z652,z3,z4,z5]),(0,[z6,z7,z2,z653,z3,z4,z5]),(0,[z654,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z655,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z4,z5,z656]),(0,[z6,z7,z2,z3,z657,z4,z5]),(0,[z6,z173,z7,z2,z3,z114,z4]),(0,[z6,z658,z7,z2,z3,z4,z5]),(0,[z6,z7,z659,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z231,z15,z5]),(0,[z6,z7,z2,z3,z4,z660,z5])],[(0,[z661,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z153,z5,z124]),(0,[z6,z87,z7,z2,z3,z15,z5]),(0,[z6,z7,z2,z3,z4,z387,z5]),(0,[z662,z6,z7,z2,z3,z4,z5])],[(0,[z663,z6,z7,z2,z3,z4,z5]),(1,[z6,z7,z2,z318,z3,z5]),(0,[z6,z7,z2,z3,z4,z21,z5]),(0,[z6,z7,z2,z664,z3,z4,z5]),(0,[z6,z12,z76,z2,z3,z4,z5]),(0,[z6,z7,z2,z129,z3,z4,z135]),(0,[z6,z665,z7,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z4,z666,z5]),(0,[z6,z7,z2,z3,z496,z4,z5]),(0,[z6,z7,z2,z3,z9,z4,z5]),(0,[z6,z667,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z668,z3,z4,z5]),(0,[z669,z6,z7,z2,z3,z4,z5]),(0,[z6,z76,z7,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z670,z4,z5]),(0,[z6,z7,z671,z2,z3,z4,z5])],[(0,[z6,z672,z7,z2,z3,z4,z5]),(0,[z10,z6,z7,z78,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z5,z673]),(0,[z282,z6,z7,z2,z3,z15,z5])],[(0,[z6,z7,z29,z2,z3,z425,z5]),(0,[z6,z7,z2,z4,z5,z332,z11]),(0,[z6,z7,z2,z3,z45,z46,z5]),(0,[z6,z7,z2,z3,z277,z45,z5])]],
   [[(0,[z6,z7,z2,z129,z3,z4,z16]),(0,[z6,z7,z674,z2,z3,z4,z5])],[(0,[z675,z6,z7,z2,z3,z4,z5]),(0,[z62,z7,z1,z2,z3,z4,z5]),(0,[z6,z676,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z634,z5]),(0,[z6,z7,z2,z3,z114,z4,z19])],[(0,[z20,z6,z7,z2,z3,z37,z5])],[(0,[z6,z7,z2,z3,z465,z4,z5]),(1,[z81,z7,z2,z82,z4,z5]),(0,[z20,z6,z7,z2,z3,z5,z16]),(0,[z6,z7,z2,z3,z4,z677,z5]),(0,[z6,z7,z3,z15,z4,z45,z5]),(0,[z6,z7,z2,z3,z114,z45,z5])],[(0,[z6,z7,z2,z3,z4,z678,z5]),(0,[z6,z2,z3,z55,z4,z13,z5]),(0,[z6,z7,z2,z3,z4,z679,z5]),(0,[z6,z7,z680,z2,z3,z4,z5])],[(0,[z6,z7,z2,z681,z3,z4,z5]),(1,[z6,z7,z2,z3,z131,z5]),(0,[z6,z7,z682,z2,z3,z4,z5]),(0,[z6,z7,z74,z2,z3,z45,z5]),(0,[z6,z7,z2,z683,z3,z4,z5])],[(0,[z6,z7,z2,z3,z4,z684,z5])],[(0,[z0,z28,z7,z2,z3,z4,z5]),(0,[z10,z6,z7,z1,z2,z3,z5]),(0,[z6,z685,z7,z2,z3,z4,z5]),(0,[z6,z686,z7,z2,z3,z4,z5]),(0,[z6,z76,z7,z2,z3,z15,z5]),(0,[z6,z76,z7,z2,z18,z3,z5]),(0,[z6,z7,z2,z507,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z687])]],
   [[(0,[z20,z6,z38,z7,z2,z3,z5]),(0,[z10,z6,z12,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z291,z4,z5]),(0,[z6,z7,z78,z2,z3,z420,z5]),(0,[z6,z7,z2,z3,z15,z515,z5]),(0,[z6,z7,z2,z102,z129,z3,z5])],[(0,[z6,z7,z2,z3,z688,z4,z5]),(1,[z6,z7,z2,z3,z153,z5]),(0,[z6,z38,z7,z2,z3,z291,z5]),(0,[z6,z7,z689,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z380,z5]),(0,[z6,z7,z2,z3,z45,z193,z5]),(0,[z6,z690,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z42,z16])],[(0,[z6,z7,z2,z691,z3,z4,z5]),(0,[z10,z6,z7,z2,z3,z193,z5]),(0,[z692,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z693,z2,z3,z4,z5]),(0,[z6,z694,z7,z2,z3,z4,z5]),(0,[z6,z695,z7,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z4,z5,z696]),(0,[z6,z7,z2,z3,z101,z45,z5]),(0,[z697,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z5,z698])],[(0,[z6,z7,z2,z3,z4,z699,z5]),(0,[z6,z7,z2,z3,z700,z4,z5]),(1,[z6,z7,z2,z102,z3,z5])],[(0,[z6,z7,z2,z3,z701,z4,z5]),(0,[z6,z7,z2,z82,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z702,z5]),(0,[z6,z7,z2,z3,z4,z41,z5]),(0,[z6,z7,z2,z3,z114,z15,z5]),(0,[z6,z7,z2,z703,z3,z4,z5])],[(0,[z704,z6,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z460,z4,z5]),(1,[z6,z7,z2,z3,z397,z5]),(1,[z6,z150,z7,z151,z4,z5]),(0,[z6,z7,z113,z2,z118,z3,z5]),(0,[z6,z7,z2,z3,z450,z4,z5]),(0,[z6,z7,z705,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z4,z210,z5]),(0,[z6,z7,z2,z3,z4,z5,z706]),(0,[z36,z6,z173,z7,z2,z3,z4]),(0,[z6,z7,z2,z3,z15,z37,z5]),(0,[z23,z6,z7,z2,z3,z415,z5]),(0,[z6,z7,z146,z2,z460,z4,z5]),(0,[z6,z7,z74,z2,z3,z15,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z6,z7,z2,z3,z5,z707]),(0,[z6,z7,z708,z2,z3,z5])],[(0,[z365,z6,z223,z7,z3,z4]),(0,[z6,z223,z7,z2,z3,z15]),(0,[z6,z709,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z710,z5]),(0,[z36,z695,z7,z2,z3,z4])],[(0,[z30,z6,z7,z318,z3,z5]),(0,[z6,z7,z2,z3,z711,z5]),(0,[z6,z7,z2,z194,z15,z5])],[(0,[z6,z173,z638,z2,z3,z4]),(0,[z6,z7,z2,z4,z135,z611]),(0,[z6,z7,z2,z3,z712,z5]),(0,[z6,z7,z2,z3,z713,z5])],[(0,[z6,z517,z7,z2,z3,z4]),(0,[z6,z286,z7,z2,z15,z5]),(0,[z6,z7,z2,z3,z5,z714])],[(0,[z6,z7,z2,z715,z3,z5])],[(0,[z6,z7,z2,z3,z716,z5]),(0,[z6,z7,z2,z717,z3,z5]),(0,[z6,z60,z7,z2,z4,z718])],[(0,[z6,z286,z7,z268,z4,z5]),(0,[z6,z719,z7,z2,z4,z5]),(0,[z20,z7,z2,z3,z155,z5]),(0,[z6,z7,z2,z3,z720,z5])],[(0,[z6,z7,z2,z721,z4,z5]),(0,[z6,z722,z145,z3,z4,z5])],[(0,[z36,z7,z2,z3,z153,z124]),(0,[z6,z38,z241,z2,z165,z4]),(0,[z6,z7,z132,z3,z723,z5])],[(0,[z6,z7,z2,z724,z3,z5]),(0,[z20,z7,z2,z703,z3,z5]),(0,[z6,z40,z32,z7,z2,z4])],[(0,[z6,z7,z2,z3,z725,z5]),(0,[z6,z196,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z726,z5])],[(0,[z6,z7,z727,z2,z3,z5]),(0,[z156,z7,z29,z3,z45,z5]),(0,[z6,z32,z7,z2,z43,z5]),(0,[z6,z7,z2,z3,z4,z728])],[(0,[z6,z7,z2,z3,z729,z5]),(0,[z20,z6,z730,z2,z3,z5]),(0,[z6,z731,z7,z2,z3,z5]),(0,[z6,z7,z2,z732,z4,z5])],[(0,[z6,z7,z2,z3,z733,z5]),(0,[z6,z7,z2,z3,z734,z5]),(0,[z6,z2,z3,z4,z5,z735])],[(0,[z365,z6,z7,z3,z45,z5]),(0,[z6,z7,z2,z3,z4,z736]),(0,[z6,z7,z3,z45,z5,z115])]],
   [[(0,[z6,z7,z2,z3,z4,z210]),(0,[z6,z7,z2,z3,z4,z737])],[(0,[z6,z738,z7,z2,z3,z5]),(0,[z6,z173,z7,z2,z102,z3]),(0,[z6,z7,z739,z2,z3,z5])],[(0,[z314,z7,z2,z82,z4,z5]),(0,[z6,z7,z2,z740,z4,z5])],[(0,[z6,z7,z2,z3,z4,z741]),(0,[z6,z7,z113,z2,z569,z5]),(0,[z6,z7,z2,z3,z742,z5])],[(0,[z0,z517,z1,z2,z3,z4]),(0,[z6,z7,z2,z3,z743,z5])],[(0,[z6,z7,z744,z3,z4,z5]),(0,[z6,z745,z7,z2,z4,z5]),(0,[z6,z746,z7,z2,z4,z5]),(0,[z6,z87,z146,z3,z397,z5]),(0,[z6,z7,z2,z3,z747,z5]),(0,[z6,z7,z2,z3,z748,z5])],[(0,[z6,z7,z226,z2,z3,z5]),(0,[z156,z7,z29,z3,z15,z5]),(0,[z6,z7,z113,z2,z154,z5]),(0,[z6,z7,z2,z683,z92,z5])],[(0,[z6,z7,z2,z3,z749,z5]),(0,[z6,z7,z2,z750,z4,z5]),(0,[z6,z7,z2,z3,z751,z5]),(0,[z6,z752,z7,z2,z3,z5])],[(0,[z6,z241,z7,z2,z139,z3]),(0,[z6,z100,z2,z3,z55,z5]),(0,[z6,z7,z2,z3,z753,z5])],[(0,[z365,z6,z7,z3,z15,z5]),(0,[z93,z7,z2,z9,z45,z5]),(0,[z6,z7,z2,z3,z109,z5]),(0,[z6,z38,z651,z2,z4,z5])],[(0,[z81,z7,z2,z82,z4,z5]),(0,[z6,z7,z754,z2,z3,z5]),(0,[z6,z7,z2,z460,z45,z5]),(0,[z755,z6,z7,z2,z3,z5])],[(0,[z0,z196,z1,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z240]),(0,[z6,z7,z2,z71,z114,z5]),(0,[z6,z7,z2,z3,z756,z5])],[(0,[z6,z7,z2,z3,z757,z5]),(0,[z6,z7,z2,z43,z5,z332]),(0,[z6,z7,z2,z3,z114,z758])],[(0,[z6,z7,z2,z759,z4,z5]),(0,[z6,z7,z78,z79,z344,z5]),(0,[z6,z760,z7,z2,z3,z5]),(0,[z761,z6,z7,z2,z3,z5])],[(0,[z6,z7,z2,z3,z762,z5]),(0,[z6,z763,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z764,z5])],[(0,[z6,z7,z2,z3,z765,z5]),(0,[z6,z7,z2,z292,z3,z114])]],
   [[(0,[z6,z7,z766,z2,z3,z5]),(0,[z6,z38,z7,z2,z450,z5])],[(0,[z6,z7,z2,z465,z4,z210]),(0,[z6,z7,z2,z3,z767,z5]),(1,[z6,z722,z3,z4,z5]),(0,[z768,z6,z7,z2,z3,z5])],[(0,[z156,z7,z744,z3,z4,z5]),(0,[z20,z7,z530,z2,z3,z5]),(0,[z769,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z15,z398])],[(0,[z20,z28,z62,z2,z3,z5]),(0,[z93,z7,z2,z9,z15,z5])],[(0,[z6,z577,z517,z7,z2,z3]),(0,[z10,z6,z7,z2,z3,z210]),(0,[z6,z7,z2,z3,z5,z770]),(0,[z20,z6,z7,z2,z771,z5]),(0,[z57,z20,z7,z2,z3,z5]),(0,[z20,z6,z38,z2,z165,z5]),(0,[z6,z7,z2,z460,z15,z5])],[(0,[z6,z7,z2,z3,z772,z5]),(0,[z10,z7,z2,z3,z200,z5]),(0,[z6,z7,z2,z3,z4,z773]),(0,[z6,z7,z2,z3,z4,z774]),(0,[z6,z38,z7,z2,z139,z5]),(0,[z6,z7,z25,z3,z4,z46]),(0,[z6,z150,z7,z151,z4,z5]),(0,[z6,z152,z7,z3,z4,z775])],[],[(0,[z6,z326,z2,z3,z45,z5]),(0,[z776,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z14,z5]),(0,[z6,z777,z7,z2,z3,z5]),(0,[z6,z152,z7,z3,z204,z42])],[],[(0,[z20,z6,z7,z2,z337,z5]),(0,[z20,z6,z152,z7,z3,z42]),(0,[z91,z7,z2,z3,z72,z5]),(0,[z6,z7,z2,z3,z15,z778])],[(0,[z10,z6,z7,z2,z779,z5])],[(0,[z62,z780,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z781,z5]),(0,[z6,z7,z2,z151,z4,z398]),(0,[z6,z7,z2,z3,z782,z5])],[(0,[z6,z7,z2,z3,z5,z783])],[(0,[z105,z7,z2,z3,z414,z37]),(0,[z6,z7,z2,z784,z4,z5]),(0,[z6,z38,z2,z165,z4,z5]),(0,[z6,z2,z3,z785,z4,z5]),(0,[z6,z7,z2,z786,z3,z45]),(0,[z6,z7,z2,z129,z4,z718])],[],[(0,[z10,z6,z7,z2,z3,z240]),(0,[z6,z7,z2,z3,z787,z5]),(0,[z6,z7,z2,z788,z3,z5])]],
   [[(0,[z10,z6,z286,z7,z2,z5]),(0,[z6,z789,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z790,z5]),(0,[z6,z326,z2,z3,z15,z5]),(0,[z10,z6,z7,z2,z3,z246]),(0,[z6,z7,z2,z791,z3,z5])],[(0,[z6,z7,z2,z792,z3,z5]),(0,[z6,z793,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z794]),(0,[z6,z7,z2,z795,z4,z5]),(0,[z6,z7,z78,z79,z4,z5])],[(0,[z6,z7,z2,z3,z4,z796]),(0,[z6,z797,z7,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z798]),(0,[z199,z7,z744,z3,z4,z5]),(0,[z6,z7,z2,z799,z3,z5]),(0,[z10,z6,z40,z2,z3,z11]),(0,[z6,z7,z2,z4,z5,z800]),(0,[z6,z7,z2,z801,z4,z5])],[(0,[z6,z7,z2,z3,z802,z5]),(0,[z6,z7,z2,z3,z803,z5]),(0,[z6,z7,z2,z3,z804,z5])],[(0,[z20,z6,z7,z2,z3,z805]),(0,[z6,z7,z2,z3,z806,z5]),(0,[z6,z7,z2,z807,z3,z5])],[(0,[z6,z7,z2,z3,z808,z5])],[(0,[z187,z7,z2,z3,z101,z5]),(0,[z6,z809,z7,z2,z3,z5]),(0,[z6,z7,z2,z460,z4,z240]),(0,[z6,z7,z2,z3,z810,z5])],[(0,[z6,z2,z3,z811,z4,z5]),(0,[z570,z20,z7,z2,z3,z5])],[(0,[z6,z7,z2,z812,z4,z5]),(0,[z10,z7,z2,z3,z504,z5]),(0,[z6,z7,z2,z460,z4,z246]),(0,[z6,z7,z2,z118,z546,z5]),(0,[z6,z7,z655,z3,z45,z5])],[(0,[z0,z780,z2,z3,z4,z5]),(0,[z6,z7,z2,z813,z3,z5])],[(0,[z6,z814,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z815]),(0,[z6,z7,z2,z4,z5,z816]),(0,[z817,z6,z7,z2,z3,z5]),(0,[z6,z7,z120,z3,z45,z46]),(0,[z6,z818,z2,z3,z4,z5])],[(0,[z6,z38,z241,z7,z2,z4])],[(0,[z6,z7,z2,z3,z193,z294])],[(0,[z6,z7,z532,z3,z45,z5])],[(0,[z0,z10,z1,z2,z3,z5]),(0,[z6,z7,z74,z3,z723,z5])]],
   [[(0,[z10,z6,z60,z7,z2,z16])],[(0,[z6,z7,z2,z3,z45,z5]),(0,[z0,z20,z1,z2,z3,z5]),(0,[z6,z7,z215,z3,z4,z46]),(0,[z6,z7,z2,z3,z5,z819])],[(0,[z91,z62,z7,z2,z3,z5]),(0,[z820,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z821,z3,z5])],[(0,[z6,z7,z822,z2,z3,z5]),(0,[z6,z7,z2,z3,z88,z5]),(0,[z6,z128,z2,z3,z13,z5]),(0,[z6,z7,z2,z3,z823,z5])],[(0,[z6,z356,z2,z3,z249,z5]),(0,[z6,z824,z7,z2,z3,z4]),(0,[z20,z6,z7,z2,z3,z825])],[(0,[z199,z266,z7,z3,z4,z5]),(0,[z6,z7,z2,z826,z3,z5]),(0,[z6,z7,z120,z3,z15,z46])],[(0,[z6,z827,z7,z2,z4,z5])],[(0,[z10,z6,z7,z2,z97,z5]),(0,[z6,z7,z2,z828,z4,z5]),(0,[z6,z7,z2,z3,z829,z45])],[(0,[z6,z7,z2,z3,z830,z5]),(0,[z20,z350,z7,z2,z3,z5]),(0,[z6,z7,z705,z3,z15,z5])],[(0,[z6,z7,z2,z3,z4,z831]),(0,[z6,z7,z2,z3,z832,z5]),(0,[z10,z6,z241,z7,z2,z3]),(0,[z6,z7,z2,z3,z5,z833])],[(0,[z61,z1,z2,z3,z4,z5])],[(0,[z6,z7,z2,z3,z15,z5]),(0,[z10,z6,z834,z2,z3,z5]),(0,[z6,z7,z3,z134,z45,z5])],[(0,[z6,z7,z2,z3,z835,z5]),(0,[z6,z7,z836,z2,z3,z5]),(0,[z6,z7,z2,z3,z5,z837])],[(0,[z6,z7,z838,z2,z3,z5])],[(0,[z6,z7,z2,z3,z45,z366]),(0,[z156,z7,z29,z3,z425,z5]),(0,[z50,z6,z7,z2,z569,z5]),(0,[z6,z7,z2,z147,z109,z5]),(0,[z6,z7,z615,z3,z45,z5]),(0,[z6,z7,z2,z839,z4,z5])],[(0,[z20,z6,z7,z2,z3,z840])]],
   [[(0,[z6,z356,z2,z3,z4,z366]),(0,[z6,z7,z2,z3,z841,z5]),(0,[z6,z7,z2,z147,z4,z240])],[(0,[z93,z7,z2,z842,z4,z5]),(0,[z10,z7,z2,z3,z843,z5]),(0,[z10,z6,z7,z2,z3,z605])],[(0,[z6,z7,z2,z465,z45,z5]),(0,[z6,z7,z2,z3,z844,z5]),(0,[z20,z6,z7,z2,z3,z845]),(0,[z568,z6,z7,z2,z3,z491]),(0,[z6,z7,z2,z846,z4,z5]),(0,[z6,z7,z2,z129,z45,z135]),(0,[z6,z7,z2,z3,z288,z193])],[(0,[z6,z7,z2,z847,z4,z5])],[(0,[z6,z7,z2,z3,z848,z5]),(0,[z6,z7,z2,z3,z277,z193]),(0,[z6,z7,z2,z3,z849,z5])],[(0,[z6,z7,z2,z850,z4,z5])],[(0,[z6,z7,z2,z3,z5,z851]),(0,[z6,z2,z3,z4,z5,z852]),(0,[z6,z7,z2,z3,z355,z5])],[(0,[z10,z105,z7,z2,z3,z37]),(0,[z6,z7,z149,z3,z15,z5]),(0,[z6,z7,z2,z3,z853,z5])],[(0,[z6,z7,z2,z3,z15,z366]),(0,[z91,z156,z7,z2,z3,z5])],[(0,[z6,z7,z2,z3,z854,z5]),(0,[z10,z6,z7,z2,z194,z5]),(0,[z6,z12,z2,z3,z112,z5])],[(0,[z6,z7,z2,z123,z3,z5]),(0,[z855,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z283,z398]),(0,[z6,z7,z3,z4,z5,z775])],[(0,[z199,z326,z218,z3,z4,z5]),(0,[z6,z7,z2,z3,z45,z398])],[(0,[z6,z7,z2,z465,z15,z5]),(0,[z6,z7,z2,z533,z4,z210]),(0,[z6,z7,z2,z129,z15,z135])],[(0,[z6,z7,z856,z2,z3,z5]),(0,[z6,z857,z7,z2,z4,z5]),(0,[z282,z156,z7,z29,z3,z5]),(0,[z6,z7,z2,z3,z605,z45]),(0,[z6,z7,z2,z71,z5,z19]),(0,[z6,z32,z7,z2,z387,z5]),(0,[z6,z7,z2,z3,z4,z858]),(0,[z6,z859,z2,z3,z4,z5]),(0,[z6,z7,z2,z860,z3,z15]),(0,[z6,z152,z7,z3,z4,z42]),(0,[z6,z7,z861,z2,z3,z5])],[(0,[z6,z7,z2,z862,z3,z5]),(0,[z20,z6,z7,z2,z846,z5]),(0,[z6,z7,z2,z3,z5,z863]),(0,[z6,z7,z47,z3,z15,z5])],[(0,[z6,z7,z2,z71,z605,z4])]],
   [[(0,[z6,z7,z2,z864,z4,z5]),(0,[z6,z7,z2,z3,z4,z246])],[(0,[z6,z7,z2,z3,z865,z5]),(0,[z6,z7,z2,z866,z4,z5]),(0,[z6,z7,z2,z3,z867,z5]),(0,[z6,z7,z2,z3,z868,z5])],[(0,[z10,z6,z7,z268,z3,z5]),(0,[z20,z6,z7,z2,z869,z5]),(0,[z870,z6,z7,z2,z3,z5]),(0,[z6,z38,z2,z670,z4,z5]),(0,[z6,z7,z2,z871,z4,z5])],[(0,[z6,z223,z7,z2,z3,z45]),(0,[z6,z7,z872,z2,z3,z5]),(0,[z6,z12,z2,z71,z13,z5]),(0,[z6,z7,z2,z292,z3,z15]),(0,[z6,z7,z2,z3,z193,z393]),(0,[z6,z7,z582,z3,z4,z46])],[(0,[z6,z7,z268,z3,z4,z5]),(0,[z6,z40,z651,z2,z3,z4])],[(0,[z6,z7,z312,z79,z4,z5]),(0,[z35,z6,z7,z2,z185,z5])],[(0,[z23,z6,z145,z3,z45,z5])],[(0,[z6,z7,z2,z3,z4,z873]),(0,[z6,z7,z2,z874,z3,z5]),(0,[z6,z7,z2,z18,z3,z549]),(0,[z6,z7,z2,z3,z875,z5])],[(0,[z389,z6,z7,z2,z3,z511]),(0,[z6,z7,z2,z3,z5,z876]),(0,[z6,z7,z2,z3,z450,z5])],[(0,[z28,z62,z2,z3,z4,z5])],[(0,[z780,z1,z2,z3,z4,z5]),(0,[z6,z7,z2,z779,z4,z5]),(0,[z6,z7,z2,z877,z3,z5]),(0,[z20,z6,z878,z7,z2,z5]),(0,[z6,z173,z2,z3,z4,z31])],[],[(0,[z6,z7,z2,z879,z3,z5])],[(0,[z199,z10,z7,z218,z3,z5]),(0,[z6,z7,z2,z3,z880,z5]),(0,[z6,z7,z2,z3,z881,z5])],[(0,[z0,z91,z7,z2,z3,z5]),(0,[z697,z20,z7,z2,z3,z5])],[(0,[z199,z20,z7,z218,z3,z5]),(0,[z6,z7,z2,z3,z882,z5])]],
   [[(0,[z10,z6,z7,z2,z883,z5]),(0,[z23,z6,z145,z3,z15,z5]),(0,[z6,z7,z2,z3,z355,z398]),(0,[z6,z7,z2,z884,z3,z5]),(0,[z6,z56,z2,z3,z285,z5])],[(0,[z6,z7,z2,z3,z4,z885]),(0,[z6,z7,z2,z3,z886,z5]),(0,[z6,z7,z120,z3,z396,z46])],[(0,[z6,z326,z2,z3,z512,z5])],[],[(0,[z6,z7,z2,z3,z277,z220]),(0,[z6,z7,z2,z255,z4,z135])],[(0,[z6,z7,z2,z3,z289,z5])],[(0,[z199,z7,z218,z3,z249,z5]),(0,[z6,z7,z2,z147,z45,z5]),(1,[z6,z2,z3,z4,z887]),(0,[z6,z7,z2,z888,z3,z5])],[(0,[z6,z7,z2,z3,z889,z5]),(0,[z6,z2,z785,z165,z4,z5]),(0,[z6,z7,z2,z3,z396,z5])],[(0,[z6,z890,z2,z3,z4,z5]),(0,[z20,z7,z2,z3,z612,z5])],[(0,[z20,z6,z130,z7,z2,z5]),(0,[z482,z20,z7,z2,z3,z5]),(0,[z891,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z129,z450,z135])],[(0,[z20,z6,z7,z120,z3,z46])],[(0,[z20,z6,z223,z7,z2,z3]),(0,[z20,z6,z7,z2,z3,z366]),(0,[z6,z892,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z3,z873]),(0,[z10,z7,z2,z3,z636,z5]),(0,[z6,z39,z7,z2,z450,z5]),(0,[z6,z7,z2,z3,z114,z679]),(0,[z6,z7,z3,z252,z15,z5])],[(0,[z6,z7,z893,z2,z3,z5]),(0,[z6,z7,z256,z3,z15,z5]),(0,[z6,z7,z2,z3,z894,z5])],[(0,[z6,z7,z2,z194,z605,z4]),(0,[z6,z7,z2,z3,z895,z5]),(0,[z896,z6,z7,z2,z3,z5])],[(0,[z6,z7,z2,z897,z3,z4]),(0,[z6,z32,z173,z7,z2,z4]),(0,[z6,z65,z2,z3,z634,z5]),(0,[z6,z7,z2,z898,z3,z4])],[(0,[z6,z7,z2,z899,z4,z5]),(0,[z36,z7,z2,z3,z4,z124]),(0,[z900,z6,z7,z2,z3,z5])]],
   [[(0,[z23,z6,z356,z3,z4,z5]),(0,[z10,z262,z7,z2,z3,z5]),(0,[z10,z7,z85,z2,z3,z5]),(0,[z6,z7,z2,z147,z15,z5]),(0,[z6,z39,z7,z2,z139,z5])],[(0,[z6,z7,z2,z3,z901,z5]),(0,[z6,z87,z356,z3,z4,z5]),(0,[z902,z6,z7,z2,z3,z5]),(0,[z6,z7,z903,z2,z3,z5])],[(0,[z199,z7,z218,z3,z4,z366]),(0,[z6,z7,z2,z3,z904,z5]),(0,[z6,z905,z7,z2,z3,z5]),(0,[z6,z241,z7,z2,z3,z15]),(0,[z6,z7,z2,z906,z15,z5])],[(0,[z6,z7,z2,z3,z425,z5]),(0,[z6,z7,z2,z3,z283,z5]),(0,[z6,z907,z7,z2,z3,z5])],[(0,[z6,z60,z7,z2,z4,z16])],[(0,[z6,z7,z2,z3,z308,z5]),(0,[z6,z7,z908,z3,z4,z5])],[(0,[z6,z356,z2,z3,z4,z5]),(0,[z6,z7,z3,z4,z5,z909]),(0,[z6,z87,z146,z3,z4,z5]),(0,[z6,z7,z2,z129,z289,z135])],[(0,[z6,z7,z2,z3,z910,z5]),(0,[z6,z7,z2,z3,z911,z5])],[(0,[z0,z268,z1,z3,z4,z5]),(0,[z20,z6,z7,z2,z3,z398]),(0,[z912,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z913,z4,z5]),(0,[z6,z7,z2,z3,z4,z243])],[(0,[z6,z87,z264,z3,z4,z5]),(0,[z6,z7,z2,z3,z914,z5]),(0,[z6,z7,z2,z3,z114,z511])],[(0,[z6,z7,z2,z3,z915,z5]),(0,[z6,z7,z2,z3,z916,z5])],[(0,[z6,z917,z7,z2,z3,z5]),(0,[z20,z7,z2,z3,z21,z5]),(0,[z20,z341,z7,z2,z3,z5]),(0,[z6,z7,z2,z254,z3,z481])],[(0,[z365,z6,z577,z7,z3,z5])],[(0,[z6,z7,z2,z533,z45,z5]),(0,[z6,z7,z2,z3,z918,z5])],[(0,[z6,z7,z2,z163,z287,z5]),(0,[z919,z6,z7,z2,z3,z5]),(0,[z6,z76,z7,z2,z71,z5])],[(0,[z6,z356,z2,z533,z4,z5]),(0,[z6,z7,z453,z2,z118,z5])]],
   [[(0,[z6,z7,z2,z3,z920,z5])],[(0,[z6,z7,z2,z3,z921,z5]),(0,[z6,z7,z2,z3,z5,z922]),(0,[z6,z647,z2,z3,z55,z5]),(0,[z923,z6,z7,z2,z3,z5]),(0,[z6,z924,z7,z2,z3,z4])],[(0,[z6,z7,z2,z3,z4,z925]),(0,[z7,z2,z3,z843,z21,z5]),(0,[z6,z926,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z927]),(0,[z6,z7,z2,z292,z3,z92]),(0,[z6,z7,z928,z2,z3,z5])],[(0,[z929,z6,z7,z2,z3,z5]),(0,[z6,z2,z722,z3,z4,z5]),(0,[z6,z241,z39,z7,z2,z4]),(0,[z6,z7,z2,z97,z204,z5])],[(0,[z6,z7,z2,z930,z45,z5]),(0,[z931,z6,z7,z2,z3,z5])],[(0,[z6,z7,z2,z3,z4,z932]),(0,[z6,z7,z2,z3,z933,z5]),(0,[z10,z91,z7,z2,z3,z5]),(0,[z6,z7,z2,z147,z4,z246])],[(0,[z934,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z786,z3,z4]),(0,[z6,z7,z935,z2,z4,z5])],[(0,[z6,z7,z2,z3,z470,z5]),(0,[z6,z356,z2,z465,z4,z5]),(0,[z6,z7,z2,z533,z15,z5]),(0,[z6,z936,z2,z3,z4,z5]),(0,[z199,z7,z226,z218,z3,z5]),(0,[z189,z6,z7,z363,z3,z5]),(0,[z6,z40,z7,z2,z43,z3]),(0,[z6,z150,z7,z151,z15,z5])],[(0,[z6,z7,z2,z937,z4,z5]),(0,[z10,z156,z7,z29,z3,z5]),(0,[z20,z6,z7,z2,z3,z310]),(0,[z938,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z939,z5]),(0,[z6,z7,z3,z940,z4,z5])],[(0,[z28,z62,z2,z3,z496,z5]),(0,[z6,z7,z2,z3,z512,z366]),(0,[z941,z6,z7,z2,z3,z5]),(0,[z6,z39,z2,z26,z4,z5]),(0,[z942,z6,z7,z2,z3,z5])],[(0,[z6,z7,z2,z3,z943,z5])],[(0,[z6,z7,z2,z944,z4,z5]),(0,[z6,z7,z2,z3,z945,z5]),(0,[z6,z2,z3,z4,z31,z887]),(0,[z6,z7,z2,z95,z380,z5])],[(0,[z10,z6,z7,z2,z3,z243]),(0,[z6,z7,z2,z3,z946,z5])],[(0,[z20,z6,z7,z2,z71,z5]),(0,[z6,z7,z2,z3,z947,z5])],[(0,[z6,z7,z2,z3,z109,z240]),(0,[z6,z7,z358,z3,z15,z5]),(0,[z6,z7,z2,z3,z948,z5])],[(0,[z6,z7,z949,z3,z4,z5]),(0,[z6,z7,z2,z3,z950,z5]),(0,[z6,z40,z2,z3,z4,z11])]],
   [[(0,[z6,z7,z2,z3,z951,z4]),(0,[z93,z7,z2,z8,z9,z5]),(0,[z20,z6,z150,z7,z151,z5]),(0,[z6,z7,z2,z952,z3,z5])],[(0,[z6,z7,z2,z953,z3,z5])],[(0,[z6,z7,z2,z3,z954,z5]),(0,[z6,z7,z2,z3,z955,z5]),(0,[z156,z6,z7,z318,z3,z5]),(0,[z6,z956,z7,z2,z3,z5]),(0,[z10,z552,z7,z2,z3,z5]),(0,[z10,z7,z2,z3,z301,z5]),(0,[z6,z87,z146,z460,z4,z5])],[(0,[z6,z957,z7,z2,z3,z4]),(0,[z10,z6,z7,z2,z3,z958]),(0,[z6,z7,z2,z3,z959,z5]),(0,[z6,z7,z383,z2,z133,z5])],[(0,[z6,z130,z223,z7,z2,z4]),(0,[z10,z93,z7,z2,z9,z5]),(0,[z6,z960,z2,z3,z4,z5]),(0,[z6,z961,z7,z2,z3,z5]),(0,[z6,z962,z7,z2,z3,z5])],[(0,[z963,z6,z7,z2,z3,z5])],[(0,[z6,z7,z2,z3,z5,z964]),(0,[z6,z7,z2,z3,z4,z965])],[(0,[z6,z7,z2,z3,z966,z5])],[(0,[z10,z6,z7,z2,z465,z5]),(0,[z6,z12,z2,z3,z711,z5]),(0,[z6,z7,z2,z3,z967,z5])],[(0,[z187,z6,z7,z2,z3,z5]),(0,[z6,z364,z2,z3,z112,z5])],[],[(0,[z6,z7,z113,z2,z133,z5])],[],[(0,[z6,z7,z78,z940,z4,z5])],[(0,[z7,z780,z2,z3,z4,z5]),(0,[z20,z6,z326,z2,z3,z5]),(0,[z20,z6,z7,z2,z129,z135]),(0,[z6,z7,z2,z3,z968,z5]),(0,[z6,z7,z3,z723,z4,z5])],[(0,[z6,z7,z2,z4,z969,z5]),(0,[z6,z7,z2,z970,z4,z5]),(0,[z6,z971,z7,z2,z3,z5]),(0,[z6,z972,z7,z2,z3,z5]),(0,[z973,z7,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z5,z974])]],
   [[(0,[z6,z7,z975,z3,z4,z5]),(0,[z20,z6,z7,z976,z3,z5]),(0,[z6,z7,z2,z3,z829,z4]),(0,[z6,z2,z3,z4,z887,z11]),(0,[z6,z7,z2,z95,z92,z5]),(0,[z6,z7,z2,z18,z3,z17])],[(0,[z20,z6,z7,z2,z3,z5]),(0,[z365,z6,z286,z7,z4,z5]),(0,[z6,z7,z318,z145,z3,z5]),(0,[z6,z7,z2,z3,z977,z5]),(0,[z6,z7,z585,z3,z45,z5]),(0,[z6,z7,z2,z18,z3,z19])],[(0,[z6,z7,z978,z2,z3,z5]),(0,[z7,z2,z3,z979,z4,z5]),(0,[z980,z6,z7,z2,z3,z5])],[(0,[z199,z6,z7,z318,z3,z5]),(0,[z156,z7,z295,z3,z4,z5]),(0,[z6,z7,z2,z981,z4,z5]),(0,[z6,z40,z32,z2,z4,z11]),(0,[z6,z7,z2,z3,z982,z5])],[(0,[z20,z6,z7,z2,z983,z5]),(0,[z229,z6,z7,z247,z3,z5]),(0,[z6,z76,z7,z2,z292,z3]),(0,[z6,z7,z2,z292,z3,z19])],[(0,[z6,z7,z2,z129,z4,z417]),(0,[z6,z7,z2,z3,z984,z5])],[(0,[z229,z6,z7,z2,z3,z5]),(0,[z6,z7,z649,z3,z45,z5])],[(0,[z6,z7,z442,z3,z15,z5]),(0,[z6,z60,z7,z2,z4,z324])],[(0,[z199,z7,z218,z3,z4,z5]),(0,[z6,z7,z2,z985,z3,z5]),(1,[z6,z7,z2,z4,z718])],[(0,[z6,z7,z2,z986,z3,z5]),(0,[z987,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z118,z879,z5])],[(0,[z6,z988,z7,z2,z3,z4]),(0,[z6,z7,z2,z3,z414,z5]),(0,[z989,z6,z7,z2,z3,z5]),(0,[z7,z2,z3,z101,z843,z5]),(0,[z6,z990,z7,z2,z3,z4]),(1,[z6,z7,z940,z4,z5])],[(0,[z365,z10,z6,z7,z3,z5]),(0,[z6,z7,z2,z3,z45,z210]),(0,[z6,z7,z722,z3,z4,z5]),(0,[z6,z87,z146,z147,z4,z5]),(0,[z6,z7,z2,z3,z991,z4]),(0,[z6,z7,z2,z992,z3,z5])],[(0,[z6,z517,z7,z268,z3,z4]),(0,[z6,z7,z2,z3,z993,z5]),(0,[z6,z7,z2,z3,z415,z5])],[(0,[z365,z20,z6,z7,z3,z5]),(0,[z6,z7,z994,z2,z3,z5]),(0,[z516,z7,z2,z3,z4,z37]),(0,[z6,z694,z7,z2,z18,z3]),(0,[z6,z7,z995,z2,z3,z5])],[(0,[z6,z7,z2,z996,z3,z5]),(0,[z6,z7,z2,z3,z997,z5]),(0,[z6,z7,z3,z15,z104,z5]),(0,[z6,z7,z2,z998,z4,z5])],[(0,[z6,z7,z2,z3,z999,z5]),(0,[z527,z6,z455,z2,z3,z5]),(0,[z10,z6,z7,z78,z79,z5]),(0,[z6,z7,z280,z3,z45,z5])]],
   [[(0,[z6,z7,z2,z3,z1000,z5]),(0,[z6,z7,z113,z2,z118,z5])],[(0,[z199,z7,z218,z533,z4,z5]),(0,[z6,z7,z2,z3,z15,z728])],[(0,[z6,z7,z2,z3,z1001,z5]),(0,[z6,z7,z2,z3,z1002,z5]),(0,[z6,z7,z2,z118,z88,z5]),(0,[z6,z7,z2,z3,z1003,z5])],[(0,[z6,z196,z7,z268,z3,z5]),(0,[z6,z7,z2,z3,z4,z1004]),(0,[z10,z20,z7,z2,z3,z5]),(0,[z20,z6,z7,z2,z292,z3]),(0,[z6,z7,z2,z3,z1005,z5])],[(0,[z6,z7,z2,z3,z4,z1006]),(0,[z6,z12,z2,z194,z13,z5])],[(0,[z6,z7,z2,z3,z15,z210]),(0,[z6,z1007,z7,z2,z4,z5]),(0,[z81,z7,z2,z82,z45,z5]),(0,[z6,z7,z2,z292,z3,z45]),(0,[z282,z7,z2,z3,z155,z5]),(0,[z6,z7,z3,z452,z15,z5])],[(0,[z6,z7,z2,z3,z45,z240]),(0,[z6,z128,z2,z3,z111,z5])],[(0,[z6,z7,z1008,z3,z4,z5]),(0,[z6,z7,z2,z3,z1009,z5])],[(0,[z6,z7,z2,z1010,z4,z5]),(0,[z6,z7,z2,z1011,z3,z5]),(0,[z6,z7,z2,z3,z1012,z5])],[(0,[z10,z6,z517,z7,z2,z3]),(0,[z6,z7,z3,z4,z5,z1013]),(0,[z199,z7,z218,z465,z4,z5]),(0,[z6,z7,z2,z97,z4,z5])],[(0,[z7,z744,z218,z3,z4,z5]),(0,[z6,z1014,z7,z2,z3,z4]),(0,[z1015,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z1016,z5]),(0,[z105,z632,z7,z2,z3,z4])],[(0,[z6,z1017,z2,z3,z4,z5]),(0,[z6,z7,z2,z771,z4,z5])],[(0,[z6,z223,z7,z2,z3,z4]),(0,[z7,z2,z744,z3,z4,z5]),(0,[z6,z7,z1018,z3,z4,z5]),(0,[z20,z7,z2,z242,z3,z5]),(0,[z6,z7,z2,z1019,z3,z5])],[(0,[z6,z517,z286,z7,z2,z4]),(0,[z187,z282,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z1020,z5]),(0,[z6,z7,z2,z3,z1021,z5]),(0,[z6,z7,z2,z3,z4,z887])],[(0,[z6,z130,z7,z2,z4,z5]),(0,[z6,z7,z2,z1022,z3,z5]),(0,[z93,z7,z184,z2,z9,z5])],[(0,[z6,z7,z2,z3,z512,z5]),(0,[z81,z7,z2,z82,z15,z5]),(0,[z6,z7,z2,z3,z1023,z5]),(0,[z6,z7,z2,z3,z4,z1024]),(0,[z6,z150,z7,z151,z283,z5])]],
   [[(0,[z6,z7,z2,z3,z1025,z5]),(0,[z6,z7,z2,z318,z3,z5]),(0,[z322,z20,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z15,z240]),(0,[z6,z76,z2,z3,z86,z5]),(0,[z6,z150,z7,z151,z45,z5])],[(0,[z6,z7,z2,z1026,z4,z5]),(0,[z20,z6,z39,z2,z138,z5])],[(0,[z6,z7,z2,z3,z1027,z5]),(0,[z6,z7,z2,z3,z4,z958]),(0,[z6,z7,z2,z3,z1028,z5]),(0,[z6,z7,z3,z4,z775,z42])],[(0,[z365,z6,z7,z3,z1029,z5]),(0,[z6,z7,z3,z1030,z4,z5]),(0,[z6,z7,z2,z3,z1031,z5]),(0,[z6,z7,z2,z337,z4,z46])],[(0,[z6,z7,z1032,z2,z3,z5]),(0,[z6,z196,z286,z7,z2,z5]),(0,[z1033,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z1034,z5]),(0,[z1035,z6,z7,z2,z3,z5])],[(0,[z6,z1036,z7,z2,z3,z5]),(0,[z6,z7,z2,z1037,z4,z5]),(0,[z10,z6,z7,z2,z5,z332]),(0,[z6,z12,z2,z3,z605,z13]),(0,[z6,z7,z2,z337,z204,z5])],[(0,[z6,z7,z3,z4,z5,z1038]),(0,[z10,z6,z7,z2,z981,z5]),(0,[z6,z7,z2,z1039,z4,z5])],[(0,[z6,z7,z2,z3,z1040,z5])],[(0,[z6,z1041,z7,z2,z4,z5]),(0,[z6,z7,z2,z533,z512,z5]),(0,[z6,z38,z2,z165,z45,z5]),(0,[z6,z7,z2,z1042,z4,z5]),(0,[z6,z7,z2,z784,z45,z5])],[(0,[z6,z7,z2,z3,z131,z5]),(0,[z6,z7,z2,z118,z185,z5]),(0,[z6,z7,z2,z1043,z4,z5]),(0,[z6,z7,z2,z3,z4,z1044])],[(0,[z6,z7,z2,z3,z5,z1045]),(0,[z6,z38,z2,z165,z88,z5])],[(0,[z93,z228,z7,z2,z4,z5]),(0,[z6,z7,z2,z3,z1046,z5]),(0,[z20,z7,z2,z408,z3,z5]),(0,[z1047,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z79,z4,z398])],[(0,[z0,z223,z1,z2,z3,z4])],[(0,[z6,z7,z2,z3,z1048,z5]),(0,[z156,z7,z29,z3,z214,z5]),(0,[z1049,z7,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z1050,z5]),(0,[z6,z7,z2,z1051,z3,z5]),(0,[z6,z7,z78,z79,z45,z5])],[(0,[z0,z130,z1,z2,z4,z5]),(0,[z1052,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z114,z684]),(0,[z6,z173,z2,z3,z637,z4])],[(0,[z10,z6,z173,z2,z3,z31]),(0,[z6,z7,z247,z3,z45,z5])]],
   [[(0,[z6,z7,z2,z1053,z4,z5]),(0,[z6,z7,z2,z465,z512,z5])],[(0,[z6,z56,z2,z3,z55,z5])],[(0,[z6,z7,z2,z4,z5,z1054]),(0,[z6,z1055,z2,z3,z4,z5]),(0,[z6,z38,z2,z165,z15,z5]),(0,[z6,z7,z2,z539,z4,z16])],[(0,[z6,z7,z2,z3,z109,z246])],[(0,[z6,z7,z2,z3,z1056,z5]),(0,[z6,z7,z2,z883,z4,z5]),(0,[z10,z6,z7,z2,z1057,z5]),(0,[z6,z241,z7,z2,z3,z45]),(0,[z6,z40,z2,z3,z4,z887]),(0,[z6,z7,z347,z3,z45,z5]),(0,[z6,z1058,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z193,z758])],[(1,[z6,z2,z785,z4,z5]),(0,[z6,z150,z7,z151,z355,z5])],[(0,[z6,z7,z2,z3,z1059,z5]),(0,[z20,z6,z988,z7,z2,z3]),(0,[z6,z7,z539,z3,z45,z5]),(0,[z6,z7,z2,z3,z1060,z5])],[(0,[z20,z6,z7,z2,z533,z5]),(0,[z6,z7,z78,z79,z15,z5]),(0,[z6,z7,z3,z15,z45,z5])],[(0,[z6,z7,z1061,z3,z4,z5]),(0,[z6,z7,z2,z1062,z4,z5]),(0,[z6,z1063,z7,z2,z3,z4]),(0,[z6,z7,z2,z1064,z3,z5]),(0,[z6,z7,z2,z3,z1065,z5]),(0,[z6,z7,z2,z3,z1066,z5]),(0,[z6,z7,z2,z1067,z3,z5])],[(0,[z6,z7,z146,z318,z3,z5]),(0,[z20,z6,z7,z2,z460,z5]),(0,[z6,z7,z2,z3,z1068,z4])],[],[(0,[z6,z7,z2,z3,z310,z15]),(0,[z6,z7,z2,z1069,z3,z5])],[(0,[z282,z6,z7,z318,z3,z5]),(0,[z6,z7,z2,z71,z4,z5]),(0,[z6,z7,z2,z489,z3,z73])],[(0,[z20,z6,z1070,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z758])],[(0,[z10,z6,z7,z2,z147,z5]),(0,[z6,z7,z2,z1071,z3,z5])],[(0,[z6,z7,z2,z1072,z3,z15])]],
   [[(0,[z20,z6,z356,z2,z3,z5])],[(0,[z6,z7,z2,z43,z3,z5]),(0,[z6,z7,z2,z3,z387,z5])],[(0,[z6,z7,z1073,z3,z4,z5]),(0,[z6,z7,z2,z1074,z4,z5]),(0,[z6,z1070,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z1075,z5]),(1,[z7,z2,z3,z843,z5]),(0,[z54,z6,z7,z2,z3,z294]),(0,[z6,z7,z2,z3,z1076,z5]),(0,[z6,z7,z2,z3,z1077,z5])],[(0,[z6,z814,z7,z268,z3,z5]),(0,[z1078,z6,z7,z2,z3,z5])],[(0,[z6,z7,z2,z3,z4,z1079])],[(0,[z6,z7,z2,z1080,z3,z5])],[(0,[z6,z517,z7,z2,z3,z15]),(0,[z6,z7,z2,z3,z723,z5])],[(0,[z6,z7,z2,z3,z1081,z5])],[],[(0,[z6,z7,z2,z1082,z4,z5]),(0,[z6,z7,z2,z3,z1083,z5])],[(0,[z6,z7,z1084,z2,z3,z5]),(0,[z6,z7,z2,z3,z1085,z5]),(1,[z7,z2,z842,z4,z5]),(0,[z6,z39,z2,z4,z5,z648]),(0,[z6,z12,z2,z292,z3,z13]),(0,[z6,z7,z578,z3,z45,z5])],[(0,[z6,z7,z2,z3,z1086,z5]),(0,[z6,z7,z2,z3,z1087,z5])],[],[(0,[z6,z7,z2,z3,z4,z1088]),(0,[z6,z7,z2,z1089,z3,z5]),(0,[z6,z558,z7,z2,z18,z3])],[(0,[z105,z7,z2,z3,z4,z1090]),(0,[z6,z7,z2,z460,z397,z5])],[(0,[z6,z7,z2,z983,z4,z5]),(0,[z6,z1091,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z1092,z5])]],
   [[(0,[z6,z356,z2,z3,z4,z210]),(0,[z6,z7,z2,z3,z1093,z5]),(0,[z6,z7,z2,z3,z4,z1094]),(0,[z6,z7,z2,z3,z1095,z5])],[(0,[z6,z7,z3,z4,z1096,z5]),(0,[z6,z7,z2,z1097,z4,z5]),(0,[z6,z7,z2,z1098,z3,z5]),(0,[z205,z7,z2,z3,z4,z124])],[(1,[z780,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z1099]),(0,[z6,z32,z7,z2,z4,z5])],[(0,[z10,z646,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z41,z5]),(0,[z6,z7,z2,z1100,z3,z5])],[(0,[z6,z7,z1101,z3,z4,z5]),(0,[z6,z7,z2,z3,z1102,z5]),(0,[z10,z472,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z1103,z5])],[(0,[z6,z577,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z1029,z5]),(0,[z6,z7,z309,z79,z4,z5])],[(0,[z6,z7,z2,z3,z1104,z5]),(0,[z6,z7,z1105,z2,z3,z5]),(0,[z10,z6,z7,z2,z3,z1106]),(1,[z6,z7,z3,z4,z775])],[],[(0,[z6,z39,z2,z138,z4,z5]),(0,[z6,z7,z1107,z3,z4,z5]),(0,[z6,z152,z7,z3,z45,z42]),(0,[z6,z7,z935,z2,z15,z5])],[(0,[z6,z7,z2,z3,z1108,z5]),(0,[z6,z87,z146,z3,z109,z5]),(0,[z6,z7,z2,z3,z605,z4]),(0,[z6,z7,z2,z4,z5,z1109])],[(0,[z6,z7,z2,z4,z5,z332])],[(0,[z365,z6,z196,z7,z3,z5]),(0,[z6,z455,z2,z3,z55,z5]),(0,[z6,z7,z2,z3,z45,z246]),(0,[z6,z531,z2,z3,z13,z5]),(0,[z6,z7,z2,z337,z4,z5]),(0,[z6,z531,z7,z2,z163,z5])],[(0,[z6,z7,z2,z1110,z4,z5]),(0,[z6,z7,z2,z1111,z4,z5])],[(0,[z10,z6,z7,z2,z740,z5]),(0,[z6,z12,z2,z3,z13,z5]),(0,[z6,z7,z2,z3,z5,z1112])],[(0,[z6,z7,z2,z4,z5,z1113]),(0,[z6,z7,z2,z3,z1114,z5])],[(0,[z6,z7,z268,z3,z45,z5]),(0,[z6,z7,z2,z4,z5,z1115]),(0,[z6,z7,z2,z3,z1116,z5]),(0,[z6,z7,z2,z3,z1117,z5]),(0,[z6,z173,z7,z2,z43,z3])]],
   [[(0,[z6,z7,z2,z3,z1118,z5])],[(0,[z371,z6,z136,z2,z3,z5])],[(0,[z6,z7,z2,z3,z1119,z5]),(0,[z6,z7,z2,z3,z214,z5]),(0,[z10,z7,z284,z2,z3,z5]),(0,[z1120,z6,z7,z2,z3,z5]),(0,[z6,z152,z7,z3,z15,z42])],[(0,[z6,z1121,z7,z2,z4,z5]),(0,[z6,z7,z2,z480,z92,z5]),(0,[z1122,z7,z2,z3,z4,z5]),(0,[z6,z7,z1123,z2,z3,z5])],[(0,[z28,z62,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z1124,z5]),(0,[z207,z6,z7,z2,z287,z5]),(0,[z6,z7,z2,z879,z4,z5]),(0,[z6,z7,z2,z4,z5,z718])],[(0,[z0,z577,z1,z2,z3,z5]),(0,[z6,z7,z2,z1125,z4,z5]),(0,[z6,z7,z2,z3,z15,z246]),(0,[z6,z173,z2,z3,z45,z31]),(0,[z6,z1126,z7,z2,z4,z5]),(0,[z6,z7,z2,z163,z92,z5])],[(0,[z6,z7,z2,z1127,z3,z5]),(0,[z10,z7,z2,z3,z5,z428]),(0,[z6,z7,z2,z3,z5,z1128]),(0,[z6,z7,z2,z1129,z4,z5]),(0,[z6,z7,z2,z3,z1130,z5])],[(0,[z6,z7,z2,z3,z1131,z5]),(0,[z6,z150,z7,z151,z4,z243]),(0,[z6,z7,z2,z871,z15,z5])],[(0,[z6,z7,z2,z3,z4,z1132]),(0,[z6,z7,z2,z3,z1133,z5])],[(0,[z6,z7,z268,z3,z15,z5]),(0,[z6,z7,z2,z1134,z3,z5]),(0,[z6,z7,z2,z3,z1135,z5]),(0,[z6,z7,z2,z3,z1136,z5])],[(0,[z6,z7,z2,z1137,z3,z5]),(0,[z36,z20,z7,z2,z3,z124]),(0,[z6,z7,z2,z1138,z3,z4]),(0,[z6,z2,z3,z711,z13,z5]),(0,[z6,z613,z7,z3,z4,z42])],[(0,[z6,z7,z1139,z2,z3,z5]),(0,[z6,z2,z1140,z3,z4,z5])],[(0,[z10,z28,z62,z2,z3,z5]),(0,[z6,z1141,z7,z2,z3,z5])],[(0,[z6,z7,z2,z1142,z3,z5]),(0,[z20,z6,z7,z1073,z3,z5]),(0,[z10,z6,z38,z2,z165,z5]),(0,[z6,z1143,z7,z2,z4,z5])],[(0,[z28,z62,z2,z3,z15,z5]),(0,[z20,z6,z87,z146,z3,z5]),(0,[z6,z7,z2,z3,z1144,z5]),(0,[z7,z2,z3,z4,z1145,z5]),(0,[z6,z38,z2,z310,z165,z4])],[(0,[z6,z7,z1146,z2,z3,z5]),(0,[z6,z7,z2,z3,z1147,z5]),(0,[z6,z173,z2,z3,z15,z31])]],
   [[(0,[z6,z7,z2,z1148,z4,z5]),(0,[z6,z7,z2,z3,z153,z5]),(0,[z6,z7,z2,z3,z4,z1149]),(0,[z6,z7,z2,z1150,z4,z5]),(0,[z6,z7,z2,z163,z515,z5]),(0,[z6,z7,z2,z102,z129,z135])],[(0,[z365,z6,z145,z3,z4,z5])],[(0,[z20,z6,z32,z7,z2,z5]),(0,[z10,z6,z7,z2,z337,z5]),(0,[z10,z6,z152,z7,z3,z42]),(0,[z6,z7,z2,z3,z4,z1151]),(0,[z6,z7,z2,z3,z1152,z5])],[(0,[z6,z7,z2,z102,z3,z5]),(0,[z6,z7,z2,z4,z718,z16])],[(0,[z23,z6,z145,z3,z415,z5]),(0,[z6,z39,z2,z598,z4,z5]),(0,[z6,z12,z2,z534,z3,z5]),(0,[z6,z40,z2,z3,z4,z106]),(0,[z6,z7,z2,z1153,z3,z5])],[(0,[z81,z7,z2,z842,z4,z5]),(0,[z10,z6,z7,z2,z3,z1154]),(0,[z6,z7,z2,z3,z397,z5])],[(0,[z6,z7,z2,z3,z1155,z5]),(0,[z6,z1156,z7,z2,z3,z5]),(0,[z10,z375,z7,z2,z3,z5]),(0,[z6,z7,z2,z1157,z3,z5]),(0,[z6,z7,z2,z3,z1158,z5]),(0,[z6,z7,z2,z3,z114,z547])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z6,z7,z1159,z2,z3,z5]),(0,[z6,z7,z2,z3,z1160,z5])],[(0,[z6,z7,z2,z3,z1161,z5]),(0,[z6,z7,z2,z3,z1162,z5]),(0,[z6,z7,z2,z1163,z3,z5]),(0,[z6,z7,z2,z860,z3,z4])],[(0,[z6,z7,z2,z3,z4,z1164]),(0,[z6,z7,z1165,z3,z4,z5])],[(0,[z6,z1166,z2,z3,z4,z5]),(0,[z199,z7,z218,z3,z15,z5]),(0,[z36,z7,z2,z3,z45,z124]),(0,[z6,z7,z940,z151,z4,z5]),(0,[z6,z7,z2,z1167,z3,z5])],[(0,[z20,z6,z7,z2,z3,z210])],[],[(0,[z6,z60,z7,z2,z621,z4])],[(0,[z20,z6,z7,z2,z3,z741]),(0,[z20,z6,z7,z2,z1026,z5]),(0,[z6,z7,z2,z3,z291,z5]),(0,[z6,z7,z2,z292,z3,z4])],[(0,[z10,z6,z130,z7,z2,z5]),(0,[z6,z130,z577,z7,z2,z5]),(0,[z6,z60,z7,z2,z45,z16])]],
   [[(0,[z10,z6,z7,z120,z3,z46]),(0,[z6,z40,z2,z3,z14,z11])],[(0,[z6,z356,z2,z3,z45,z5]),(0,[z6,z87,z146,z3,z45,z5]),(0,[z6,z7,z2,z3,z1168,z5]),(0,[z6,z76,z2,z3,z55,z5]),(0,[z229,z7,z2,z3,z200,z5])],[(0,[z199,z7,z218,z3,z4,z210]),(0,[z6,z7,z2,z3,z1169,z5]),(0,[z6,z40,z2,z534,z3,z4]),(0,[z6,z7,z2,z129,z135,z27])],[(0,[z6,z7,z2,z3,z4,z1170]),(0,[z6,z7,z2,z3,z1171,z5]),(0,[z6,z7,z2,z3,z45,z243]),(0,[z6,z576,z60,z7,z2,z4]),(0,[z6,z7,z2,z3,z5,z1172])],[(0,[z6,z7,z2,z3,z4,z840]),(0,[z36,z7,z2,z3,z15,z124]),(0,[z6,z2,z3,z4,z5,z887]),(0,[z6,z173,z2,z3,z4,z523])],[(0,[z6,z7,z2,z3,z4,z1106]),(0,[z6,z7,z2,z337,z4,z42])],[(0,[z6,z7,z2,z3,z4,z1173]),(0,[z20,z6,z7,z2,z3,z240])],[(0,[z20,z6,z286,z7,z2,z5])],[(0,[z93,z20,z7,z2,z9,z5]),(0,[z20,z6,z7,z2,z3,z246]),(0,[z10,z7,z2,z3,z101,z5])],[(0,[z6,z7,z976,z3,z4,z5]),(0,[z593,z62,z2,z3,z4,z5]),(0,[z6,z7,z1174,z2,z3,z5]),(0,[z6,z7,z2,z1175,z3,z5]),(0,[z6,z7,z2,z45,z5,z332]),(0,[z6,z60,z7,z2,z15,z16])],[(0,[z6,z326,z2,z3,z249,z5])],[(0,[z6,z356,z2,z3,z15,z5]),(0,[z105,z7,z2,z3,z37,z488]),(0,[z6,z87,z146,z3,z15,z5])],[(0,[z91,z7,z2,z3,z21,z5]),(0,[z23,z10,z6,z145,z3,z5]),(0,[z6,z7,z2,z785,z4,z5]),(0,[z6,z7,z2,z3,z1176,z4])],[(0,[z6,z7,z2,z3,z1177,z5]),(0,[z81,z514,z7,z2,z4,z5]),(1,[z7,z2,z3,z4,z1090]),(0,[z6,z7,z2,z3,z15,z243]),(0,[z6,z7,z1178,z3,z4,z5])],[(0,[z23,z20,z6,z145,z3,z5]),(0,[z6,z7,z2,z3,z278,z19]),(0,[z6,z7,z113,z2,z879,z5]),(0,[z6,z7,z2,z3,z5,z1179])],[(0,[z6,z7,z74,z363,z3,z5]),(0,[z6,z7,z2,z3,z1180,z5]),(0,[z6,z7,z2,z3,z1181,z5]),(0,[z6,z7,z2,z1182,z4,z5])]],
   [[(0,[z6,z38,z2,z785,z4,z5]),(0,[z6,z7,z2,z3,z1183,z5])],[(0,[z6,z7,z2,z3,z4,z1184]),(0,[z36,z7,z2,z3,z4,z1090]),(0,[z6,z7,z682,z79,z4,z5]),(0,[z6,z464,z7,z2,z4,z16])],[(0,[z6,z7,z2,z1185,z3,z5]),(0,[z6,z7,z1186,z2,z3,z5]),(0,[z6,z7,z2,z3,z1187,z5])],[(0,[z6,z7,z2,z3,z1188,z5]),(0,[z36,z7,z2,z123,z3,z124]),(0,[z6,z7,z2,z3,z1189,z5]),(0,[z6,z7,z2,z3,z1190,z5])],[(0,[z6,z7,z2,z3,z1191,z4]),(0,[z1192,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z163,z88,z5])],[],[(0,[z6,z326,z2,z3,z4,z366])],[(0,[z6,z7,z2,z3,z1193,z5]),(0,[z6,z7,z2,z3,z1194,z5]),(0,[z187,z7,z2,z218,z3,z5]),(0,[z20,z6,z60,z7,z2,z16]),(0,[z6,z7,z300,z3,z45,z5])],[(0,[z6,z7,z2,z292,z118,z3])],[(0,[z6,z7,z2,z3,z512,z210]),(0,[z6,z7,z1195,z2,z3,z5])],[(0,[z6,z40,z2,z3,z45,z11]),(0,[z6,z7,z2,z3,z1196,z5])],[(0,[z10,z81,z7,z2,z82,z5])],[(0,[z28,z780,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z1197,z5]),(0,[z105,z7,z2,z3,z4,z37]),(0,[z6,z40,z186,z2,z3,z4]),(0,[z6,z7,z2,z1198,z3,z5]),(0,[z6,z152,z7,z3,z308,z42])],[(0,[z6,z7,z2,z18,z3,z491]),(0,[z6,z7,z2,z3,z1199,z5]),(0,[z6,z7,z2,z3,z310,z45]),(0,[z6,z7,z2,z194,z4,z5])],[(0,[z20,z6,z7,z2,z97,z5]),(0,[z1200,z7,z2,z3,z4,z5]),(0,[z6,z87,z146,z3,z4,z240]),(0,[z1201,z6,z7,z2,z3,z5])],[(0,[z6,z7,z1202,z3,z4,z5]),(0,[z6,z286,z7,z2,z4,z5]),(0,[z6,z7,z2,z3,z1203,z5]),(0,[z6,z7,z2,z3,z4,z1204])]],
   [[(0,[z20,z6,z241,z7,z2,z3]),(0,[z6,z87,z146,z3,z4,z246]),(0,[z6,z150,z7,z940,z4,z5]),(0,[z1205,z6,z7,z2,z3,z5])],[(0,[z6,z1206,z2,z3,z4,z5])],[(0,[z6,z7,z1207,z3,z4,z5]),(0,[z6,z7,z317,z2,z305,z5])],[],[(0,[z6,z7,z2,z3,z249,z5]),(0,[z6,z7,z2,z3,z4,z1154]),(0,[z7,z2,z3,z842,z4,z5]),(0,[z6,z40,z2,z3,z15,z11]),(0,[z6,z7,z132,z3,z45,z5]),(1,[z6,z7,z2,z879,z5])],[(0,[z6,z7,z225,z3,z4,z42])],[(0,[z365,z6,z517,z7,z3,z4]),(0,[z6,z7,z2,z3,z1208,z5]),(0,[z6,z7,z2,z8,z3,z5]),(0,[z6,z7,z1209,z2,z3,z5]),(0,[z6,z7,z120,z3,z236,z46])],[(0,[z6,z7,z2,z3,z1210,z5]),(0,[z6,z7,z2,z3,z1211,z5])],[(0,[z6,z7,z2,z1212,z3,z5]),(0,[z6,z834,z2,z3,z4,z5]),(0,[z20,z7,z2,z3,z843,z5]),(0,[z20,z6,z7,z2,z3,z605])],[(0,[z229,z6,z7,z363,z3,z5]),(0,[z20,z6,z7,z2,z866,z5]),(0,[z6,z7,z3,z723,z45,z5])],[(0,[z319,z6,z476,z2,z3,z5]),(0,[z6,z7,z2,z147,z397,z5]),(0,[z6,z7,z2,z3,z4,z1213])],[(0,[z6,z7,z2,z3,z4,z1214]),(0,[z81,z7,z2,z174,z82,z5]),(0,[z6,z7,z2,z3,z1215,z5])],[(0,[z6,z173,z2,z3,z4,z887]),(0,[z6,z7,z2,z3,z236,z5]),(0,[z6,z7,z424,z3,z45,z5])],[(0,[z6,z7,z2,z3,z4,z805]),(0,[z6,z7,z2,z3,z4,z1216]),(0,[z81,z7,z2,z82,z131,z5]),(0,[z6,z7,z2,z292,z71,z4])],[(0,[z6,z7,z2,z1057,z4,z5]),(0,[z10,z36,z7,z2,z3,z124]),(0,[z1217,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z420,z5]),(0,[z6,z1218,z7,z2,z3,z5])],[(0,[z0,z286,z1,z2,z4,z5]),(0,[z6,z7,z2,z1219,z3,z5])]],
   [[(0,[z20,z6,z7,z2,z194,z5]),(0,[z6,z7,z1220,z2,z3,z5]),(0,[z6,z7,z2,z3,z204,z5])],[(0,[z156,z7,z29,z3,z4,z5]),(0,[z6,z7,z2,z3,z249,z366]),(0,[z6,z7,z2,z3,z1221,z5]),(0,[z6,z241,z7,z267,z2,z3])],[(0,[z91,z6,z7,z2,z3,z5]),(0,[z6,z1222,z7,z2,z3,z5]),(0,[z6,z2,z138,z785,z4,z5])],[(0,[z199,z7,z218,z3,z45,z5]),(0,[z6,z7,z2,z1223,z3,z5])],[(0,[z6,z223,z577,z7,z2,z3]),(0,[z10,z6,z326,z2,z3,z5])],[(0,[z199,z356,z218,z3,z4,z5]),(0,[z6,z7,z2,z465,z249,z5]),(0,[z6,z87,z197,z3,z4,z5]),(0,[z6,z7,z2,z3,z1224,z5]),(0,[z6,z543,z7,z2,z4,z16])],[(0,[z413,z6,z7,z2,z3,z278]),(0,[z6,z7,z2,z3,z1225,z5])],[(0,[z10,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z1226,z4,z5]),(0,[z6,z7,z2,z1227,z3,z5]),(0,[z6,z7,z2,z3,z5,z1228])],[(0,[z365,z6,z7,z3,z1210,z5]),(0,[z1229,z6,z7,z2,z3,z5]),(1,[z6,z2,z3,z711,z5]),(0,[z6,z7,z2,z3,z699,z19])],[(0,[z20,z6,z7,z268,z3,z5]),(0,[z439,z7,z2,z9,z4,z5]),(0,[z6,z1230,z7,z3,z4,z5])],[(0,[z28,z62,z2,z3,z470,z5]),(0,[z10,z6,z1166,z2,z3,z5]),(0,[z10,z334,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z1231,z5]),(0,[z6,z146,z722,z3,z4,z5]),(0,[z6,z7,z2,z71,z92,z5])],[(0,[z6,z7,z1232,z2,z3,z5]),(0,[z6,z7,z441,z3,z15,z5]),(0,[z6,z2,z3,z55,z711,z5]),(0,[z6,z613,z7,z151,z4,z5])],[(0,[z6,z7,z2,z869,z4,z5]),(0,[z6,z7,z2,z3,z4,z825]),(0,[z20,z7,z2,z3,z360,z5])],[(0,[z6,z196,z517,z7,z2,z3]),(0,[z20,z6,z7,z2,z3,z932])],[(0,[z93,z7,z2,z9,z4,z5]),(0,[z6,z7,z671,z3,z45,z5])],[(0,[z6,z7,z2,z3,z4,z1233]),(0,[z6,z7,z2,z3,z1234,z5]),(0,[z282,z6,z7,z2,z3,z5]),(0,[z6,z39,z475,z2,z4,z5]),(0,[z7,z2,z82,z842,z4,z5]),(0,[z6,z7,z2,z460,z4,z5]),(0,[z6,z38,z2,z139,z165,z5])]],
   [[(0,[z6,z38,z391,z2,z4,z5]),(0,[z6,z7,z2,z3,z1235,z5])],[(0,[z0,z365,z1,z3,z4,z5]),(0,[z6,z1236,z7,z2,z3,z5]),(0,[z6,z7,z2,z1237,z3,z5])],[(0,[z6,z7,z2,z3,z1238,z5])],[(0,[z1239,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z114,z193])],[(0,[z10,z6,z223,z7,z2,z3]),(0,[z10,z6,z7,z2,z3,z366]),(0,[z6,z7,z2,z3,z1240,z5]),(0,[z6,z7,z2,z3,z4,z778]),(0,[z6,z7,z2,z97,z45,z5])],[(0,[z6,z7,z2,z3,z283,z243])],[],[(0,[z6,z7,z2,z3,z1241,z5])],[(0,[z208,z6,z349,z2,z3,z5]),(0,[z6,z7,z2,z3,z5,z1242]),(0,[z6,z7,z2,z3,z1243,z5])],[(0,[z6,z130,z7,z2,z45,z5]),(0,[z20,z654,z7,z2,z3,z5]),(0,[z7,z2,z3,z843,z4,z5])],[(0,[z6,z7,z2,z3,z4,z845])],[(0,[z6,z7,z2,z18,z3,z41])],[(0,[z6,z326,z2,z3,z4,z5]),(0,[z6,z356,z2,z3,z512,z5]),(0,[z6,z7,z2,z1244,z3,z5])],[(0,[z365,z6,z87,z3,z4,z5]),(0,[z6,z7,z2,z3,z1245,z5]),(0,[z20,z6,z40,z2,z3,z11]),(0,[z6,z7,z2,z337,z15,z5])],[(0,[z6,z7,z2,z292,z3,z41]),(0,[z6,z7,z2,z97,z15,z5])],[(0,[z1246,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z940,z4,z5]),(0,[z6,z7,z3,z4,z46,z775])]],
   [[(0,[z6,z7,z2,z3,z1247,z5]),(0,[z6,z7,z2,z3,z1248,z5]),(0,[z6,z7,z2,z3,z1249,z5])],[(0,[z10,z6,z7,z2,z3,z398]),(0,[z6,z7,z2,z3,z344,z5]),(0,[z6,z7,z321,z3,z15,z5])],[(0,[z6,z7,z1250,z2,z3,z5]),(0,[z1251,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z1252,z4,z5])],[(0,[z6,z130,z7,z2,z15,z5]),(0,[z6,z38,z2,z575,z4,z5])],[(0,[z6,z223,z7,z268,z3,z4]),(0,[z1253,z6,z7,z2,z3,z5]),(0,[z6,z38,z267,z2,z165,z5])],[(0,[z6,z326,z2,z533,z4,z5]),(0,[z156,z6,z7,z363,z3,z5]),(0,[z473,z6,z7,z2,z480,z5]),(0,[z1254,z6,z7,z2,z3,z5])],[(0,[z6,z130,z7,z268,z4,z5]),(0,[z6,z7,z2,z1255,z4,z5]),(0,[z1047,z7,z2,z3,z45,z5])],[(0,[z1256,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z1257,z5])],[(0,[z10,z275,z7,z2,z3,z5])],[(0,[z6,z7,z2,z174,z3,z5])],[(0,[z6,z7,z3,z327,z45,z5]),(0,[z1258,z6,z7,z2,z3,z5]),(0,[z6,z7,z317,z2,z118,z5])],[(0,[z6,z7,z2,z1259,z3,z5]),(0,[z6,z577,z286,z7,z2,z5]),(0,[z6,z7,z2,z3,z1260,z5]),(1,[z7,z744,z3,z4,z5]),(0,[z6,z7,z2,z3,z1261,z5]),(0,[z6,z7,z2,z3,z355,z243])],[(0,[z6,z7,z1262,z3,z4,z5]),(0,[z6,z7,z2,z1263,z3,z5]),(0,[z6,z7,z2,z3,z4,z1264]),(0,[z6,z7,z113,z2,z5,z445])],[(0,[z6,z326,z2,z465,z4,z5]),(0,[z6,z7,z2,z139,z3,z5]),(0,[z6,z7,z2,z3,z1265,z5])],[(0,[z6,z7,z2,z3,z1266,z5])],[(0,[z6,z152,z7,z337,z4,z42])]],
   [[(0,[z10,z6,z7,z2,z3,z1267]),(0,[z6,z7,z2,z3,z5,z1268]),(0,[z6,z241,z7,z2,z3,z4]),(0,[z7,z2,z3,z45,z1145,z5]),(0,[z6,z7,z120,z3,z4,z46]),(0,[z6,z152,z7,z97,z4,z42])],[(0,[z6,z7,z2,z3,z1269,z5]),(0,[z6,z7,z2,z3,z1270,z5]),(0,[z6,z7,z2,z3,z1271,z5]),(0,[z10,z6,z7,z2,z3,z310])],[(0,[z6,z7,z318,z3,z15,z5]),(0,[z7,z2,z3,z4,z37,z1090]),(0,[z6,z87,z722,z3,z4,z5]),(0,[z6,z7,z2,z3,z1272,z5]),(0,[z6,z7,z2,z879,z92,z5])],[(0,[z6,z7,z2,z3,z1273,z5])],[(0,[z6,z7,z74,z3,z15,z5])],[(0,[z6,z223,z286,z7,z2,z4]),(0,[z10,z478,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z1274]),(0,[z6,z7,z2,z1275,z3,z5])],[(0,[z6,z7,z2,z3,z4,z5]),(0,[z10,z6,z7,z2,z71,z5]),(0,[z1276,z7,z2,z3,z4,z5])],[(0,[z6,z7,z2,z1277,z3,z5]),(0,[z6,z7,z2,z71,z45,z5]),(0,[z6,z558,z2,z3,z13,z5]),(0,[z6,z7,z339,z3,z15,z5])],[(0,[z6,z1278,z7,z2,z3,z5])],[(0,[z6,z7,z2,z3,z1279,z4]),(0,[z10,z6,z150,z7,z151,z5]),(0,[z1280,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z71,z88,z5]),(0,[z6,z40,z7,z2,z102,z3]),(0,[z6,z7,z2,z1281,z3,z5]),(0,[z6,z7,z2,z4,z5,z1282])],[],[(0,[z6,z517,z7,z2,z3,z45]),(0,[z6,z7,z2,z3,z1283,z5]),(0,[z1284,z6,z7,z2,z3,z5]),(0,[z6,z39,z2,z785,z4,z5]),(0,[z6,z7,z2,z507,z3,z405])],[(0,[z6,z1285,z7,z2,z3,z4]),(0,[z10,z6,z7,z2,z3,z1286]),(0,[z6,z7,z2,z3,z1287,z5]),(0,[z6,z7,z2,z118,z71,z5]),(0,[z6,z7,z3,z15,z723,z5])],[(0,[z6,z497,z7,z3,z4,z42])],[(0,[z6,z1288,z7,z2,z3,z4]),(0,[z6,z7,z2,z3,z4,z718])],[(0,[z187,z156,z7,z2,z3,z5]),(0,[z20,z156,z7,z29,z3,z5]),(0,[z6,z60,z676,z7,z2,z4]),(0,[z6,z7,z3,z15,z677,z5]),(0,[z6,z7,z1289,z2,z3,z5])]],
   [[(0,[z6,z223,z196,z7,z2,z3]),(0,[z6,z7,z2,z533,z249,z5]),(0,[z6,z7,z2,z1290,z4,z5]),(0,[z6,z7,z2,z3,z5,z1291])],[(0,[z7,z2,z3,z4,z1090,z124]),(0,[z6,z2,z3,z4,z711,z5]),(0,[z6,z7,z2,z71,z15,z5])],[(0,[z1292,z6,z7,z2,z3,z5]),(1,[z6,z7,z2,z3,z758]),(0,[z6,z7,z2,z18,z3,z758])],[(0,[z6,z7,z2,z3,z4,z366]),(0,[z20,z6,z7,z2,z3,z243]),(0,[z6,z1293,z7,z2,z3,z4])],[(0,[z6,z7,z2,z1294,z3,z4]),(0,[z105,z20,z7,z2,z3,z37])],[(0,[z6,z7,z2,z1295,z3,z5])],[(0,[z6,z7,z2,z3,z1296,z5])],[(0,[z365,z6,z7,z3,z4,z5]),(0,[z6,z7,z3,z1297,z4,z5]),(0,[z6,z7,z2,z465,z4,z5]),(0,[z6,z7,z2,z3,z5,z1298]),(0,[z10,z6,z7,z2,z129,z135]),(0,[z6,z7,z2,z129,z4,z135])],[(0,[z6,z7,z2,z3,z1299,z5])],[(0,[z1300,z6,z7,z2,z3,z5]),(0,[z6,z7,z1301,z2,z3,z5])],[(0,[z7,z2,z842,z9,z4,z5]),(0,[z6,z7,z2,z3,z397,z240]),(0,[z6,z7,z2,z1302,z4,z5]),(0,[z6,z7,z2,z3,z1303,z5])],[(0,[z6,z7,z2,z3,z1304,z5])],[(0,[z6,z7,z2,z533,z4,z366]),(0,[z282,z6,z7,z441,z3,z5])],[(0,[z6,z7,z451,z2,z3,z5]),(0,[z6,z32,z7,z2,z45,z5])],[(0,[z6,z130,z196,z7,z2,z5]),(0,[z6,z1305,z7,z3,z4,z5]),(0,[z199,z7,z218,z3,z512,z5]),(0,[z6,z7,z2,z3,z1306,z5]),(0,[z6,z12,z136,z2,z3,z5])],[(0,[z20,z6,z7,z2,z465,z5]),(0,[z6,z7,z2,z3,z1307,z5]),(0,[z6,z7,z3,z45,z545,z5])]],
   [[(0,[z6,z7,z2,z3,z1308,z5]),(0,[z6,z7,z2,z3,z1309,z5]),(0,[z6,z7,z2,z3,z4,z398])],[(0,[z6,z7,z2,z3,z4,z1310]),(0,[z6,z7,z2,z1311,z4,z5])],[(0,[z6,z7,z2,z3,z4,z1312])],[(0,[z6,z878,z7,z2,z4,z5]),(0,[z6,z1313,z7,z2,z3,z4]),(0,[z6,z39,z2,z138,z45,z5])],[(0,[z6,z7,z2,z465,z4,z366]),(0,[z105,z7,z2,z3,z45,z37]),(0,[z6,z76,z2,z3,z634,z5])],[],[(0,[z6,z7,z2,z3,z4,z1314]),(0,[z6,z7,z2,z3,z310,z4]),(0,[z6,z7,z2,z337,z45,z5])],[(0,[z6,z1091,z7,z268,z3,z5]),(0,[z6,z7,z2,z3,z1315,z5]),(0,[z6,z7,z2,z139,z3,z310]),(0,[z6,z40,z2,z3,z387,z11]),(0,[z6,z32,z7,z2,z15,z5])],[(0,[z6,z7,z2,z18,z3,z73]),(0,[z6,z7,z2,z97,z308,z5])],[(0,[z6,z1316,z7,z2,z3,z4])],[(0,[z6,z730,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z1317,z5]),(0,[z6,z12,z7,z2,z71,z5])],[(0,[z6,z1318,z7,z2,z4,z5]),(0,[z6,z7,z363,z3,z45,z5]),(0,[z6,z1319,z7,z2,z3,z5]),(0,[z23,z6,z145,z3,z4,z5]),(0,[z6,z7,z2,z1320,z4,z5])],[(0,[z6,z7,z2,z3,z1321,z5]),(0,[z6,z7,z2,z1322,z3,z5]),(0,[z10,z6,z7,z2,z292,z3]),(0,[z6,z7,z2,z3,z1323,z5]),(0,[z6,z7,z2,z3,z1324,z5]),(0,[z1325,z6,z7,z2,z3,z5])],[(0,[z6,z577,z7,z268,z3,z5]),(0,[z91,z7,z2,z218,z3,z5]),(0,[z6,z39,z2,z138,z15,z5])],[(0,[z1326,z6,z7,z2,z3,z5]),(0,[z105,z7,z2,z3,z15,z37]),(0,[z6,z7,z2,z3,z24,z5])],[(0,[z6,z7,z2,z3,z4,z1267]),(0,[z61,z20,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z843,z5]),(0,[z6,z76,z2,z3,z711,z5]),(0,[z6,z7,z2,z1327,z3,z5]),(0,[z6,z7,z2,z3,z1328,z5]),(0,[z6,z7,z2,z1329,z3,z5])]],
   [[(0,[z6,z7,z2,z3,z1330,z5]),(0,[z81,z20,z7,z2,z82,z5]),(0,[z6,z7,z2,z3,z1331,z5]),(0,[z6,z12,z2,z575,z3,z5])],[(0,[z6,z7,z2,z3,z4,z1332])],[(0,[z7,z29,z744,z3,z4,z5]),(0,[z187,z20,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z5,z488]),(0,[z6,z7,z2,z3,z4,z1333])],[(0,[z6,z7,z2,z3,z1334,z5])],[(0,[z6,z7,z2,z3,z1335,z5]),(0,[z20,z6,z719,z7,z2,z5]),(0,[z6,z7,z2,z3,z1336,z5])],[(0,[z1337,z6,z7,z2,z3,z5]),(0,[z6,z38,z2,z165,z291,z5])],[(0,[z6,z7,z2,z3,z496,z5]),(0,[z20,z6,z7,z78,z79,z5]),(0,[z6,z7,z79,z940,z4,z5])],[(0,[z6,z7,z2,z842,z4,z5]),(0,[z6,z7,z184,z2,z3,z5]),(0,[z6,z7,z2,z3,z4,z1090])],[(0,[z6,z7,z2,z3,z5,z1338])],[(0,[z1339,z7,z2,z3,z4,z5]),(0,[z6,z40,z2,z3,z41,z11]),(0,[z6,z7,z459,z3,z15,z5])],[(0,[z6,z7,z2,z3,z1340,z5]),(0,[z10,z6,z39,z2,z138,z5]),(0,[z6,z7,z2,z129,z572,z4]),(0,[z6,z7,z2,z1341,z3,z5]),(0,[z6,z307,z7,z2,z4,z16]),(0,[z6,z7,z2,z118,z338,z5])],[(0,[z6,z7,z2,z3,z4,z1286]),(0,[z6,z483,z7,z151,z4,z5]),(0,[z6,z7,z2,z147,z4,z5]),(0,[z6,z7,z253,z3,z15,z5]),(0,[z6,z7,z2,z3,z114,z481]),(0,[z6,z7,z2,z3,z4,z775])],[(0,[z6,z7,z267,z2,z3,z310])],[(0,[z6,z7,z2,z906,z4,z5])],[(0,[z6,z7,z2,z3,z249,z210])],[(0,[z6,z780,z2,z3,z4,z5])]],
   [[(0,[z20,z6,z517,z7,z2,z3]),(0,[z6,z7,z2,z3,z1342,z5])],[(0,[z6,z7,z2,z3,z4,z1343])],[(0,[z0,z1,z2,z3,z45,z5]),(0,[z6,z7,z2,z3,z1344,z5]),(0,[z6,z7,z2,z4,z135,z718])],[(0,[z6,z7,z2,z3,z1345,z5]),(0,[z6,z7,z2,z3,z1346,z5]),(0,[z6,z7,z2,z3,z1347,z5])],[(0,[z10,z6,z87,z146,z3,z5]),(0,[z23,z6,z722,z3,z4,z5]),(0,[z6,z7,z2,z1348,z3,z5]),(0,[z6,z7,z2,z3,z1349,z5])],[(0,[z6,z1350,z2,z3,z4,z5]),(0,[z6,z7,z2,z3,z4,z1351])],[(0,[z6,z7,z1352,z2,z4,z5]),(0,[z6,z7,z2,z3,z1353,z5]),(0,[z1354,z6,z7,z2,z3,z5])],[(0,[z6,z7,z2,z3,z1355,z5]),(0,[z20,z7,z2,z68,z3,z5])],[(0,[z6,z7,z3,z1356,z4,z5]),(0,[z10,z6,z32,z7,z2,z5])],[(0,[z199,z6,z7,z363,z3,z5])],[(0,[z6,z7,z2,z3,z5,z1357])],[(0,[z6,z7,z2,z3,z1358,z5]),(0,[z6,z7,z2,z1359,z3,z5]),(0,[z6,z7,z2,z3,z1360,z5])],[(0,[z0,z1,z2,z3,z15,z5]),(0,[z6,z7,z2,z1361,z4,z5]),(0,[z20,z6,z7,z2,z5,z332])],[(0,[z1362,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z292,z194,z4])],[],[(0,[z6,z7,z520,z3,z45,z5]),(0,[z6,z7,z2,z3,z1363,z5]),(0,[z6,z7,z3,z521,z45,z5]),(0,[z6,z7,z2,z3,z758,z19])]],
   [[(0,[z10,z6,z7,z2,z533,z5]),(0,[z6,z12,z7,z2,z292,z3])],[(0,[z6,z76,z476,z2,z3,z5])],[(0,[z6,z7,z2,z533,z4,z5]),(0,[z10,z6,z7,z2,z460,z5]),(0,[z6,z1364,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z1365,z5])],[(0,[z20,z6,z1313,z7,z2,z3]),(0,[z6,z7,z132,z318,z3,z5]),(0,[z6,z349,z2,z3,z13,z5]),(0,[z23,z6,z145,z3,z24,z5]),(0,[z6,z574,z7,z2,z163,z5]),(0,[z6,z7,z2,z1366,z3,z5]),(0,[z6,z7,z1367,z2,z4,z5]),(0,[z6,z7,z2,z3,z1368,z5])],[(0,[z6,z7,z2,z1369,z4,z5]),(0,[z229,z91,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z1370,z5]),(0,[z6,z7,z2,z507,z3,z19])],[(0,[z6,z7,z2,z3,z1371,z5]),(0,[z6,z7,z2,z3,z1372,z5]),(0,[z6,z7,z267,z2,z3,z5]),(0,[z6,z7,z2,z3,z5,z27])],[(0,[z365,z6,z356,z3,z4,z5]),(0,[z6,z7,z2,z3,z1373,z5]),(0,[z20,z6,z173,z2,z3,z31]),(0,[z6,z7,z2,z458,z515,z5])],[(0,[z229,z156,z7,z29,z3,z5]),(0,[z6,z2,z3,z4,z5,z1374]),(0,[z6,z7,z2,z163,z559,z5])],[(0,[z10,z6,z7,z2,z970,z5]),(0,[z6,z7,z2,z3,z1375,z5])],[(0,[z10,z6,z356,z2,z3,z5]),(0,[z6,z7,z2,z930,z4,z5]),(0,[z6,z76,z447,z2,z3,z5]),(0,[z6,z7,z2,z15,z5,z332]),(0,[z6,z7,z1376,z2,z3,z5])],[],[(0,[z199,z7,z451,z218,z3,z5]),(0,[z6,z7,z2,z387,z5,z332])],[(0,[z6,z7,z2,z3,z1377,z5]),(0,[z6,z7,z2,z163,z434,z5])],[(0,[z6,z7,z693,z151,z4,z5]),(0,[z6,z7,z2,z3,z1378,z5]),(0,[z6,z7,z2,z3,z1379,z5])],[(0,[z6,z173,z2,z3,z370,z4]),(1,[z6,z7,z3,z723,z5]),(0,[z6,z7,z2,z879,z163,z5])],[(0,[z7,z2,z3,z4,z1090,z5]),(0,[z6,z7,z2,z3,z1380,z5]),(0,[z6,z7,z2,z3,z397,z246])]],
   [[(0,[z6,z7,z2,z3,z1381,z5]),(0,[z6,z7,z2,z1382,z3,z5]),(0,[z6,z1383,z7,z2,z3,z5])],[(0,[z1384,z6,z7,z2,z3,z5])],[(0,[z6,z7,z2,z3,z1385,z5]),(0,[z6,z7,z2,z460,z109,z5])],[(0,[z365,z6,z130,z7,z4,z5]),(0,[z6,z7,z2,z3,z1386,z5]),(0,[z6,z7,z2,z3,z1387,z5])],[(0,[z6,z1388,z7,z2,z3,z5]),(0,[z6,z7,z2,z1389,z3,z5]),(0,[z6,z7,z2,z1182,z15,z5])],[(0,[z6,z7,z2,z1390,z4,z5]),(0,[z20,z6,z7,z2,z147,z5]),(0,[z6,z7,z2,z3,z114,z41]),(0,[z6,z7,z2,z3,z1391,z5]),(0,[z6,z7,z2,z3,z1392,z5])],[(0,[z6,z7,z2,z3,z4,z1393]),(0,[z6,z326,z2,z3,z4,z210]),(0,[z6,z7,z2,z363,z3,z5]),(0,[z187,z7,z2,z3,z231,z5]),(0,[z1394,z6,z7,z2,z3,z5])],[(0,[z1395,z6,z7,z2,z3,z5])],[(0,[z6,z7,z2,z1396,z3,z5]),(0,[z6,z7,z1397,z3,z4,z5]),(0,[z6,z7,z2,z194,z45,z5]),(0,[z6,z7,z2,z3,z5,z758])],[(0,[z6,z130,z517,z7,z2,z4]),(0,[z1398,z6,z7,z2,z3,z5])],[(0,[z6,z286,z7,z2,z45,z5]),(0,[z6,z40,z2,z43,z3,z11]),(0,[z6,z7,z78,z79,z420,z5]),(0,[z6,z7,z2,z337,z308,z5]),(0,[z6,z7,z2,z3,z1399,z5])],[(0,[z1400,z6,z7,z2,z3,z5]),(0,[z6,z7,z2,z3,z605,z15])],[(0,[z6,z7,z2,z3,z1401,z5]),(0,[z6,z7,z2,z1402,z3,z5]),(0,[z6,z150,z7,z151,z4,z398])],[(0,[z6,z40,z2,z4,z332,z11]),(0,[z6,z7,z2,z1072,z3,z4]),(0,[z6,z7,z120,z3,z4,z775])],[(0,[z6,z1403,z2,z3,z4,z5]),(0,[z1404,z6,z7,z2,z3,z5])],[(0,[z6,z7,z2,z1405,z4,z5])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 515) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 515).take 508) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1023).take 367) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1390)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [515, 508, 367] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 176).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 176).take 164).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 340).take 172).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [176, 164, 172] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_47028

theorem PEqualNP.Outside.L_meta_47028 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241320 * 2 ^ 32 + 3974686880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241320 * 2 ^ 32 + 3974686880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_47028.solve