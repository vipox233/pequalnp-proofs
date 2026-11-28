import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38037

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277071040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0100004541313cc0#64 ++ 0x00100004541313cc#64 ++ 0xbec520cfc3737ccf#64 ++ 0x7bec520cfc3737cc#64 : BitVec 256),
   (0x0200411300140552#64 ++ 0x0020041130014055#64 ++ 0x7dcac333049c8ffe#64 ++ 0xf7dcac333049c8ff#64 : BitVec 256),
   (0x34130c2c18e0d0a4#64 ++ 0x534130c2c18e0d0a#64 ++ 0xebb31c3c38e0f0fd#64 ++ 0xeebb31c3c38e0f0f#64 : BitVec 256),
   (0x582c16c02f00ea08#64 ++ 0x8582c16c02f00ea0#64 ++ 0xe7bc1fc03f00ff0b#64 ++ 0xde7bc1fc03f00ff0#64 : BitVec 256),
   (0x603fa00036ca0000#64 ++ 0xe603fa00036ca000#64 ++ 0x1fffe0003fff0007#64 ++ 0xc1fffe0003fff000#64 : BitVec 256),
   (0x803ffbba80000000#64 ++ 0xf803ffbba8000000#64 ++ 0xffbfffffc0000000#64 ++ 0x3ffbfffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [10, 4]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbec520cfc3737ccf 0x7bec520cfc3737cc

def z1 : W := mkw 0x0200411200040112 0x0020041120004011 0x0002c030008c0030 0x00002c030008c003

def z2 : W := mkw 0x0200411300140552 0x0020041130014055 0x7dcac333049c8ffe 0xf7dcac333049c8ff

def z3 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebb31c3c38e0f0fd 0xeebb31c3c38e0f0f

def z4 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03f00ff0b 0xde7bc1fc03f00ff0

def z5 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1fffe0003fff0007 0xc1fffe0003fff000

def z6 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc0000000 0x3ffbfffffc000000

def z7 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0x0803003c00e000f4 0x20803003c00e000f

def z8 : W := mkw 0x36134d3f18f4d5f6 0x536134d3f18f4d5f 0xfffbdf3f3cfcffff 0xffffbdf3f3cfcfff

def z9 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0x1803e03fc0000000 0x21803e03fc000000

def z10 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0x82353cccc0000000 0x082353cccc000000

def z11 : W := mkw 0xa03ffbba90ca0000 0xfa03ffbba90ca000 0xffffffffc0ff0004 0x3ffffffffc0ff000

def z12 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x1fbfe00000000000 0x01fbfe0000000000

def z13 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffffffffffff0007 0xfffffffffffff000

def z14 : W := mkw 0x14000c2c0820d0a4 0x114000c2c0820d0a 0xea811c3c0060f0fd 0x6ea811c3c0060f0f

def z15 : W := mkw 0x0300415741353dd2 0x00300415741353dd 0x7dcac33307ffffff 0xf7dcac33307fffff

def z16 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffffffffc49c0006 0xfffffffffc49c000

def z17 : W := mkw 0xb43fffbe98e0d0a4 0xfb43fffbe98e0d0a 0xffbffffff8e0f0fd 0xfffbffffff8e0f0f

def z18 : W := mkw 0x803ff39280000000 0xe803ff3928000000 0x1fbfe3c3c0000000 0x11fbfe3c3c000000

def z19 : W := mkw 0x0000000400201080 0x0000000040020108 0x00000000006070cd 0x400000000006070c

def z20 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xebbbdf3c00000000 0x2ebbbdf3c0000000

def z21 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xfffd3fc03f73ff0f 0xdfffd3fc03f73ff0

def z22 : W := mkw 0x0200411300140552 0x0020041130014055 0x1040c003001c0000 0x01040c003001c000

def z23 : W := mkw 0x623fe11336de0552 0xe623fe11336de055 0x7fffe3333fff8fff 0xf7fffe3333fff8ff

def z24 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xe0001fffc0000000 0x3e0001fffc000000

def z25 : W := mkw 0x0200411300140552 0x0020041130014055 0x3cc2c033009c0cfe 0x73cc2c033009c0cf

def z26 : W := mkw 0x0200411300140552 0x0020041130014055 0x7fcfe33307ff8fff 0xf7fcfe33307ff8ff

def z27 : W := mkw 0x0000000000000000 0x0000000000000000 0xbe8520cfc0000000 0x3be8520cfc000000

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0x69820030008080fc 0xe69820030008080f

def z29 : W := mkw 0x100004000800c000 0x0100004000800c00 0xe7b81f003c00ff0b 0xde7b81f003c00ff0

def z30 : W := mkw 0x01000005403114c0 0x001000005403114c 0x1841200fc07300c4 0x21841200fc07300c

def z31 : W := mkw 0x582c16802e00c208 0x8582c16802e00c20 0x41381f003c008300 0x841381f003c00830

def z32 : W := mkw 0x3413040418e0d0a4 0x43413040418e0d0a 0x0bb3000038e0f0fd 0xc0bb3000038e0f0f

def z33 : W := mkw 0x793fb6c57ffbfec8 0xe793fb6c57ffbfec 0xffffffcfffffffcf 0xfffffffcfffffffc

def z34 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xfe853fffc0000000 0x3fe853fffc000000

def z35 : W := mkw 0x0200000100140552 0x0020000010014055 0x00400000009c00f4 0x000400000009c00f

def z36 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0x413adf303c8c0000 0x8413adf303c8c000

def z37 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xa00000cfc0007cc8 0x3a00000cfc0007cc

def z38 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x013ac0003c8c0000 0x8013ac0003c8c000

def z39 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xffb73cfff8e0f0fd 0xfffb73cfff8e0f0f

def z40 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x0040000003737ccf 0x40040000003737cc

def z41 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x413adf3000000000 0x0413adf300000000

def z42 : W := mkw 0x0200411300140552 0x0020041130014055 0x1dcac033049c00f6 0xe1dcac033049c00f

def z43 : W := mkw 0x8213e93b80140552 0x78213e93b8014055 0x7dcbe33fc49c8ffe 0xf7dcbe33fc49c8ff

def z44 : W := mkw 0x0100004041012800 0x0010000404101280 0x000420c0c3030000 0x0000420c0c303000

def z45 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x41381f003f00ff0b 0xc41381f003f00ff0

def z46 : W := mkw 0x6000000036ca0000 0x06000000036ca000 0x004000003fff0007 0xc004000003fff000

def z47 : W := mkw 0x783fb6c03fcaea08 0xe783fb6c03fcaea0 0xffffffc03fffff0f 0xdffffffc03fffff0

def z48 : W := mkw 0x180016c00900ea08 0x0180016c00900ea0 0xe0001fc00000ff08 0x1e0001fc00000ff0

def z49 : W := mkw 0x002c128000000000 0x8002c12800000000 0xe7bc1fc000000000 0x1e7bc1fc00000000

def z50 : W := mkw 0x0200415301142d52 0x00200415301142d5 0xffcec3f3079cffff 0xfffcec3f3079cfff

def z51 : W := mkw 0x0300004541353dd2 0x00300004541353dd 0xbec520cfc7ffffff 0xfbec520cfc7fffff

def z52 : W := mkw 0x802cf39280000000 0xa802cf3928000000 0x140ce3c3c0000000 0x1140ce3c3c000000

def z53 : W := mkw 0xa413e93e90e010a4 0x7a413e93e90e010a 0x1803e03fc0e000f4 0x21803e03fc0e000f

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0x7dcac300049c8f0e 0xd7dcac300049c8f0

def z55 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x017ac0003fff0007 0xc017ac0003fff000

def z56 : W := mkw 0x603fb28036ca0000 0xe603fb28036ca000 0xffffffc03fff0007 0xdffffffc03fff000

def z57 : W := mkw 0x580004402f00ea08 0x0580004402f00ea0 0x000000003f00ff0b 0xc000000003f00ff0

def z58 : W := mkw 0xd83ffffaaf00ea08 0xfd83ffffaaf00ea0 0xffbfffffff00ff0b 0xfffbfffffff00ff0

def z59 : W := mkw 0x0100004141112c40 0x00100004141112c4 0x0040000003130c02 0x00040000003130c0

def z60 : W := mkw 0x412ca041671b2c40 0xa412ca041671b2c4 0x144ce0c3c71f0c02 0x1144ce0c3c71f0c0

def z61 : W := mkw 0x823ffbbb80140552 0xf823ffbbb8014055 0xffffffffc49c8ffe 0xfffffffffc49c8ff

def z62 : W := mkw 0x80005bba80000000 0x180005bba8000000 0x40001f3000000000 0x040001f300000000

def z63 : W := mkw 0x582c16802e00c208 0x8582c16802e00c20 0x00301c0038000000 0x000301c003800000

def z64 : W := mkw 0x633fe15777ff3dd2 0xe633fe15777ff3dd 0xffffe3ffffffffff 0xfffffe3fffffffff

def z65 : W := mkw 0x0200411300140552 0x0020041130014055 0x1842c033009c00f4 0x21842c033009c00f

def z66 : W := mkw 0x5a2c57d32f14ef5a 0x85a2c57d32f14ef5 0xfffedff33f9cffff 0xffffedff33f9cfff

def z67 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x87bc1cc03f007003 0xc87bc1cc03f00700

def z68 : W := mkw 0x783fb6c03fcaea08 0xe783fb6c03fcaea0 0xe7bd3fc03f63ff0b 0xde7bd3fc03f63ff0

def z69 : W := mkw 0x8213e93b80140552 0x78213e93b8014055 0x1843e03fc09c00f4 0x21843e03fc09c00f

def z70 : W := mkw 0x582c04402f00ea08 0x8582c04402f00ea0 0x07bc00003f00ff0b 0xc07bc00003f00ff0

def z71 : W := mkw 0x0000000400201080 0x0000000040020108 0xaa81000c006070cd 0x6aa81000c006070c

def z72 : W := mkw 0x0000000100100440 0x0000000010010044 0x7dc2003300908cfe 0xf7dc2003300908cf

def z73 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x963dffcfc0000000 0x1963dffcfc000000

def z74 : W := mkw 0x100004000800c000 0x0100004000800c00 0x82301c0038007001 0x082301c003800700

def z75 : W := mkw 0x100004000800c000 0x0100004000800c00 0xebb21c303880f0fd 0xeebb21c303880f0f

def z76 : W := mkw 0x80135bba80000000 0x580135bba8000000 0xebb31fffc0000000 0x3ebb31fffc000000

def z77 : W := mkw 0x402ca000260a0000 0xa402ca000260a000 0x144ce000071f0002 0x0144ce000071f000

def z78 : W := mkw 0x602ca00036ca0000 0xa602ca00036ca000 0x144ce0003fff0007 0xc144ce0003fff000

def z79 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1843e00000ff0004 0x01843e00000ff000

def z80 : W := mkw 0x580004002e00c208 0x0580004002e00c20 0x000000003c008300 0x8000000003c00830

def z81 : W := mkw 0x0000000000000000 0x0000000000000000 0x1dcac000049c0006 0xc1dcac000049c000

def z82 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xe2353fffc0000000 0x3e2353fffc000000

def z83 : W := mkw 0x14000c2c0820d0a4 0x114000c2c0820d0a 0xe0001c3c0000f0f8 0x2e0001c3c0000f0f

def z84 : W := mkw 0x983ffffa8900ea08 0xf983ffffa8900ea0 0xffbfffffc000ff08 0x3ffbfffffc000ff0

def z85 : W := mkw 0x590004456f31fec8 0x0590004456f31fec 0xbec520cfff73ffcf 0xfbec520cfff73ffc

def z86 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cc0000000100006 0x41cc000000010000

def z87 : W := mkw 0x590004456f31fec8 0x0590004456f31fec 0x004000003f73ffcf 0xc004000003f73ffc

def z88 : W := mkw 0x592c16c56f31fec8 0x8592c16c56f31fec 0xfffd3fcfff73ffcf 0xffffd3fcfff73ffc

def z89 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xffbd3fcfff00ff0b 0xfffbd3fcfff00ff0

def z90 : W := mkw 0x0200411300140552 0x0020041130014055 0x1448c303041c0f02 0x11448c303041c0f0

def z91 : W := mkw 0x100004000800c000 0x0100004000800c00 0xe3b01c003800f009 0xce3b01c003800f00

def z92 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x82311c0c38607001 0x082311c0c3860700

def z93 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc4008f0a 0xfffbfffffc4008f0

def z94 : W := mkw 0x1c001eec0920faac 0x11c001eec0920faa 0xe0001ffc0000fff8 0x3e0001ffc0000fff

def z95 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0bb3000038e00005 0xc0bb3000038e0000

def z96 : W := mkw 0xa03ffbba90c00000 0xfa03ffbba90c0000 0xffbffffff8e00005 0xfffbffffff8e0000

def z97 : W := mkw 0x0013082800000000 0x5001308280000000 0xebb31c3c00000000 0x2ebb31c3c0000000

def z98 : W := mkw 0x603fa82836ca0000 0xf603fa82836ca000 0xfffffc3c3fff0007 0xefffffc3c3fff000

def z99 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe8031c3c00e0f0fc 0x2e8031c3c00e0f0f

def z100 : W := mkw 0x0200000100140552 0x0020000010014055 0x1dcac000049c8ffe 0xc1dcac000049c8ff

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0x1fcfe00007ff0007 0xc1fcfe00007ff000

def z102 : W := mkw 0x0100004141112c40 0x00100004141112c4 0x144420c3c3130c02 0x1144420c3c3130c0

def z103 : W := mkw 0x3500044559f1fce4 0x03500044559f1fce 0x004000003bf3fcff 0xc004000003bf3fcf

def z104 : W := mkw 0x35130c6d59f1fce4 0x535130c6d59f1fce 0xfff73cfffbf3fcff 0xffff73cfffbf3fcf

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000003730007 0x4004000000373000

def z106 : W := mkw 0x783fb6c03fcaea08 0xe783fb6c03fcaea0 0xe7bedfc03f8cff0b 0xde7bedfc03f8cff0

def z107 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x82341cc03b007001 0x082341cc03b00700

def z108 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xfffedfc03f9cff0f 0xdfffedfc03f9cff0

def z109 : W := mkw 0x0000128000000000 0x0000012800000000 0xe0001fc000000000 0x1e0001fc00000000

def z110 : W := mkw 0x0300415741353dd2 0x00300415741353dd 0xffcfe3ffc7ffffff 0xfffcfe3ffc7fffff

def z111 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x0002c000008c0000 0x00002c000008c000

def z112 : W := mkw 0x2013000410e01080 0x42013000410e0108 0xabb3000c38e070cd 0xeabb3000c38e070c

def z113 : W := mkw 0x482c12c027002a08 0x8482c12c027002a0 0x040c03c007000f02 0x1040c03c007000f0

def z114 : W := mkw 0x5a0004412f14ef5a 0x05a0004412f14ef5 0x004000003f9cffff 0xc004000003f9cfff

def z115 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe2341fc03b00ff09 0x1e2341fc03b00ff0

def z116 : W := mkw 0x0013082800000000 0x5001308280000000 0x0803003c00000000 0x20803003c0000000

def z117 : W := mkw 0x402c000026000000 0x8402c00002600000 0x040c000007000002 0x0040c00000700000

def z118 : W := mkw 0x582cb6c02f0aea08 0xa582cb6c02f0aea0 0xf7fcffc03f1fff0b 0xdf7fcffc03f1fff0

def z119 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1dfac0003c9c0006 0xc1dfac0003c9c000

def z120 : W := mkw 0xe03fbaa8b6ca0000 0xfe03fbaa8b6ca000 0x9ffffcccffff0007 0xc9ffffcccffff000

def z121 : W := mkw 0x0000000000000000 0x0000000000000000 0x1ec5200003730007 0x41ec520000373000

def z122 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xe13adfffc0000000 0x3e13adfffc000000

def z123 : W := mkw 0x763fed3f3efed5f6 0xf763fed3f3efed5f 0xffffff3f3fffffff 0xfffffff3f3ffffff

def z124 : W := mkw 0x0300415741353dd2 0x00300415741353dd 0xbecde3cfc77f7fcf 0x7becde3cfc77f7fc

def z125 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbfcfe0cfc7ff7ccf 0xfbfcfe0cfc7ff7cc

def z126 : W := mkw 0x7c3f1eec3fe0faac 0xd7c3f1eec3fe0faa 0xefbf1ffc3fe0ffff 0xfefbf1ffc3fe0fff

def z127 : W := mkw 0x603f000036c00000 0xc603f000036c0000 0x0fbf00003fe00007 0xc0fbf00003fe0000

def z128 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x41321c3038e0f0fd 0xc41321c3038e0f0f

def z129 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0xbfffe0cfffff0007 0xfbfffe0cfffff000

def z130 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xffc720ffc3f3fcff 0xfffc720ffc3f3fcf

def z131 : W := mkw 0x2613493f10f415f6 0x52613493f10f415f 0x7dcbc33f04fc8ffe 0xf7dcbc33f04fc8ff

def z132 : W := mkw 0x402c000026000000 0x8402c00002600000 0x07bc00003f000003 0xc07bc00003f00000

def z133 : W := mkw 0x0000000100100440 0x0000000010010044 0x3cc0000300100cce 0x73cc0000300100cc

def z134 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe1381fc03c00ff08 0x9e1381fc03c00ff0

def z135 : W := mkw 0x36134d3f18f4d5f6 0x536134d3f18f4d5f 0xfbf3dc3f38fcf0fd 0xefbf3dc3f38fcf0f

def z136 : W := mkw 0x743fa4043eead0a4 0xe743fa4043eead0a 0x1fffe0003ffff0ff 0xc1fffe0003ffff0f

def z137 : W := mkw 0x01000005403114c0 0x001000005403114c 0x00400000007300c4 0x000400000007300c

def z138 : W := mkw 0x402c000026000000 0x8402c00002600000 0x67bc03003f008f0b 0xd67bc03003f008f0

def z139 : W := mkw 0x0200411300140552 0x0020041130014055 0x6000033300008ff8 0x36000033300008ff

def z140 : W := mkw 0x482c12c027002a08 0x8482c12c027002a0 0xa68c03c007007f0b 0x5a68c03c007007f0

def z141 : W := mkw 0x813ffbbfc03114c0 0xf813ffbbfc03114c 0xffffffffc07300c4 0x3ffffffffc07300c

def z142 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe2311c3c3860f0f9 0x2e2311c3c3860f0f

def z143 : W := mkw 0x2513086d51f13ce4 0x52513086d51f13ce 0xbec720ffc3f37cff 0x7bec720ffc3f37cf

def z144 : W := mkw 0x0100004441213880 0x0010000444121388 0x820520ccc3637001 0x0820520ccc363700

def z145 : W := mkw 0x0200411200040112 0x0020041120004011 0x410ac330048c8330 0x8410ac330048c833

def z146 : W := mkw 0x0000004001002800 0x0000000400100280 0x040400c003000c02 0x1040400c003000c0

def z147 : W := mkw 0x0000004001002800 0x0000000400100280 0xa68400c003007c0b 0x5a68400c003007c0

def z148 : W := mkw 0x2613493f10f415f6 0x52613493f10f415f 0x1843c03f00fc00f4 0x21843c03f00fc00f

def z149 : W := mkw 0x4a2c53d327142f5a 0x84a2c53d327142f5 0x144cc3c3071c0f02 0x1144cc3c3071c0f0

def z150 : W := mkw 0x002c539200000000 0x8002c53920000000 0xffbedff300000000 0x3ffbedff30000000

def z151 : W := mkw 0x002c128000000000 0x8002c12800000000 0x82341cc000000000 0x082341cc00000000

def z152 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffbffffffb630001 0x3ffbffffffb63000

def z153 : W := mkw 0x4a2c53d327142f5a 0x84a2c53d327142f5 0x7dcec3f3079c8ffe 0xf7dcec3f3079c8ff

def z154 : W := mkw 0x822cf39380140552 0xa822cf3938014055 0x144ce3c3c41c0f02 0x1144ce3c3c41c0f0

def z155 : W := mkw 0x580004402f00ea08 0x0580004402f00ea0 0xe3b01c003f00ff0b 0xce3b01c003f00ff0

def z156 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x0803003c38e0f0fd 0xe0803003c38e0f0f

def z157 : W := mkw 0x34130c2818c0c024 0x534130c2818c0c02 0x41321c3038808030 0x841321c303880803

def z158 : W := mkw 0x3400040418e0d0a4 0x03400040418e0d0a 0x0000000038e0f0fd 0xc0000000038e0f0f

def z159 : W := mkw 0x14000c2c0820d0a4 0x114000c2c0820d0a 0xe3b01c3c3800f0f9 0xee3b01c3c3800f0f

def z160 : W := mkw 0x0200411300140552 0x0020041130014055 0x7dcac333041c0f02 0x37dcac333041c0f0

def z161 : W := mkw 0x613fa04577fb3cc0 0xe613fa04577fb3cc 0xbfffe0cfffff7ccf 0xfbfffe0cfffff7cc

def z162 : W := mkw 0x802cf39280000000 0xa802cf3928000000 0xbe8de3cfc0000000 0x3be8de3cfc000000

def z163 : W := mkw 0x743fac2c3eead0a4 0xf743fac2c3eead0a 0xfffffc3c3ffff0ff 0xefffffc3c3ffff0f

def z164 : W := mkw 0xd82c5ffaaf00ea08 0x9d82c5ffaaf00ea0 0xe7bc1fffff00ff0b 0xfe7bc1fffff00ff0

def z165 : W := mkw 0x2413082810c00024 0x52413082810c0002 0x0002003000800030 0x0000200300080003

def z166 : W := mkw 0x813ffbffc1313cc0 0xf813ffbffc1313cc 0xffffffffc3737ccf 0x7ffffffffc3737cc

def z167 : W := mkw 0x823ffbbb80140552 0xf823ffbbb8014055 0x7dfadf33049c8ffe 0xf7dfadf33049c8ff

def z168 : W := mkw 0x0000000000000000 0x0000000000000000 0x6588030004008f0a 0xd6588030004008f0

def z169 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xffcd23cfc773ffcf 0xfffcd23cfc773ffc

def z170 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x167de0003f7f0003 0x0167de0003f7f000

def z171 : W := mkw 0x823ffbbb80140552 0xf823ffbbb8014055 0xffffffffc41c0f02 0x3ffffffffc41c0f0

def z172 : W := mkw 0x0400082c002010a4 0x10400082c002010a 0x0000003c000000f0 0x20000003c000000f

def z173 : W := mkw 0x492c12c567313ec8 0x8492c12c567313ec 0xbecd23cfc7737fcf 0x7becd23cfc7737fc

def z174 : W := mkw 0x3600451718f4d5f6 0x03600451718f4d5f 0x7dcac3333cfcffff 0xf7dcac3333cfcfff

def z175 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x964520cfc3737c03 0x1964520cfc3737c0

def z176 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc08080fc 0xfffbfffffc08080f

def z177 : W := mkw 0x7c0004443fe0faac 0x07c0004443fe0faa 0x000000003fe0ffff 0xc000000003fe0fff

def z178 : W := mkw 0x0200411300140552 0x0020041130014055 0x6588033304008ffa 0xf6588033304008ff

def z179 : W := mkw 0x0000000000000000 0x0000000000000000 0x010ac000048c0000 0x8010ac000048c000

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x6180000000008008 0xc618000000000800

def z181 : W := mkw 0x01000005403114c0 0x001000005403114c 0x3cc1200fc0730cce 0x73cc1200fc0730cc

def z182 : W := mkw 0x82005bbb80140552 0x182005bbb8014055 0xe0001fffc0008ff8 0x3e0001fffc0008ff

def z183 : W := mkw 0xe23ffbbbb6de0552 0xfe23ffbbbb6de055 0xffffffffffff8fff 0xfffffffffffff8ff

def z184 : W := mkw 0x0000411200000000 0x0000041120000000 0xff8fe3ffc0000000 0x3ff8fe3ffc000000

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0x820520ccc0000000 0x0820520ccc000000

def z186 : W := mkw 0x0000004001002800 0x0000000400100280 0xa00000c000007c08 0x1a00000c000007c0

def z187 : W := mkw 0x643fa82c36ea10a4 0xf643fa82c36ea10a 0x1fffe03c3fff00f7 0xe1fffe03c3fff00f

def z188 : W := mkw 0x6200411336de0552 0x06200411336de055 0x7dcac3333fff8fff 0xf7dcac3333fff8ff

def z189 : W := mkw 0x2113a00550fb14c0 0x62113a00550fb14c 0x1843e00fc0ff00c4 0x21843e00fc0ff00c

def z190 : W := mkw 0x0200411200040112 0x0020041120004011 0x7d8ac333048c8330 0xb7d8ac333048c833

def z191 : W := mkw 0x0200411300140552 0x0020041130014055 0x0000030300000f00 0x10000030300000f0

def z192 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xefbb1f3c3ce0ffff 0xfefbb1f3c3ce0fff

def z193 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa81000c00000000 0x2aa81000c0000000

def z194 : W := mkw 0x592c16c56f31fec8 0x8592c16c56f31fec 0xbef53ccffb737ccf 0x7bef53ccffb737cc

def z195 : W := mkw 0x802cf39280000000 0xa802cf3928000000 0x0008c30000000000 0x00008c3000000000

def z196 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1fbfe0003c8c0000 0x81fbfe0003c8c000

def z197 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x144420c3c3737ccf 0x5144420c3c3737cc

def z198 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0x0bb3003c38e000f5 0xe0bb3003c38e000f

def z199 : W := mkw 0x80001aa880000000 0x180001aa88000000 0x80001cccc0000000 0x080001cccc000000

def z200 : W := mkw 0x0000411200000000 0x0000041120000000 0x7d8ac33300000000 0x37d8ac3330000000

def z201 : W := mkw 0x7c3f1eec3fe0faac 0xd7c3f1eec3fe0faa 0x82351ccc3b607001 0x082351ccc3b60700

def z202 : W := mkw 0x0213493b00140552 0x50213493b0014055 0xfffbdf3f049c8ffe 0xffffbdf3f049c8ff

def z203 : W := mkw 0x0013082800000000 0x5001308280000000 0xffb73cffc0000000 0x3ffb73cffc000000

def z204 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe1321c3c3880f0f8 0xae1321c3c3880f0f

def z205 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x023520003b630001 0x0023520003b63000

def z206 : W := mkw 0x003fa82800000000 0xf003fa8280000000 0xffbffc3c00000000 0x2ffbffc3c0000000

def z207 : W := mkw 0x01000005403114c0 0x001000005403114c 0x1ec5200fc37300c7 0x61ec5200fc37300c

def z208 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x3cc0000303737ccf 0x73cc0000303737cc

def z209 : W := mkw 0x7c3f1eec3fe0faac 0xd7c3f1eec3fe0faa 0xe7bd1fcc3f60ff0b 0xde7bd1fcc3f60ff0

def z210 : W := mkw 0x0200411300140552 0x0020041130014055 0x79c2c033009c80fc 0xe79c2c033009c80f

def z211 : W := mkw 0xd82cf7d2af00ea08 0xad82cf7d2af00ea0 0xf7bcffc3ff00ff0b 0xdf7bcffc3ff00ff0

def z212 : W := mkw 0x0000004001002800 0x0000000400100280 0x820400c003007001 0x0820400c00300700

def z213 : W := mkw 0x0013082800000000 0x5001308280000000 0x41321c3000000000 0x041321c300000000

def z214 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0xbfbfe0cfc0000000 0x3bfbfe0cfc000000

def z215 : W := mkw 0x5a2c57922e04c31a 0x85a2c57922e04c31 0x413adf303c8c8330 0x8413adf303c8c833

def z216 : W := mkw 0x0200411300140552 0x0020041130014055 0x1c4ac333049c0ff6 0x31c4ac333049c0ff

def z217 : W := mkw 0x002c128000000000 0x8002c12800000000 0x040c03c000000000 0x1040c03c00000000

def z218 : W := mkw 0x2000000010c00000 0x02000000010c0000 0x0000000038e00005 0xc0000000038e0000

def z219 : W := mkw 0x15000c6d4931fce4 0x115000c6d4931fce 0xe0001cffc000fcf8 0x3e0001cffc000fcf

def z220 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x1c0fe3ffc0000000 0x31c0fe3ffc000000

def z221 : W := mkw 0x8000e11280000000 0x28000e1128000000 0x1000e003c0000000 0x01000e003c000000

def z222 : W := mkw 0xa43ffbbe90e010a4 0xfa43ffbbe90e010a 0xffbfffffc0e000f4 0x3ffbfffffc0e000f

def z223 : W := mkw 0x743fac2c3eead0a4 0xf743fac2c3eead0a 0x9ffffc0c3fff7007 0xc9ffffc0c3fff700

def z224 : W := mkw 0x180016c00900ea08 0x0180016c00900ea0 0xe3b01fc03800ff09 0xde3b01fc03800ff0

def z225 : W := mkw 0x7c2c16c43fe0faac 0x87c2c16c43fe0faa 0xe7bc1fc03fe0ffff 0xde7bc1fc03fe0fff

def z226 : W := mkw 0x0200411300140552 0x0020041130014055 0x610ac333048c8ff8 0xb610ac333048c8ff

def z227 : W := mkw 0x802cf39280000000 0xa802cf3928000000 0x7d8ee3f3c0000000 0x37d8ee3f3c000000

def z228 : W := mkw 0x823ffbbb80140552 0xf823ffbbb8014055 0xffffffffc09c00f4 0x3ffffffffc09c00f

def z229 : W := mkw 0xf43fffbebeead0a4 0xff43fffbebeead0a 0xfffffffffffff0ff 0xffffffffffffff0f

def z230 : W := mkw 0x2513082d50f114e4 0x52513082d50f114e 0x1843203fc0f300f4 0x21843203fc0f300f

def z231 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x8a331c3c38e070f5 0x28a331c3c38e070f

def z232 : W := mkw 0xd83fbee8af00ea08 0xfd83fbee8af00ea0 0xe7bd3fccff00ff0b 0xde7bd3fccff00ff0

def z233 : W := mkw 0x0000000000000000 0x0000000000000000 0x0408030004000f02 0x10408030004000f0

def z234 : W := mkw 0x0000000000000000 0x0000000000000000 0x00400000049c0006 0xc00400000049c000

def z235 : W := mkw 0x0100004141112c40 0x00100004141112c4 0xb6c420c3c3137c0b 0x5b6c420c3c3137c0

def z236 : W := mkw 0x01000005403114c0 0x001000005403114c 0xbac1200fc07370cd 0x6bac1200fc07370c

def z237 : W := mkw 0x0000411200000000 0x0000041120000000 0x7dcac333049c0006 0xf7dcac333049c000

def z238 : W := mkw 0x0200411300140552 0x0020041130014055 0x7d8ac33300008ff8 0x37d8ac33300008ff

def z239 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1ec7e00003ff0007 0x41ec7e00003ff000

def z240 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffbffffffc8c0000 0xbffbffffffc8c000

def z241 : W := mkw 0x422c411326140552 0x8422c41132614055 0x7ffec3333f9c8fff 0xf7ffec3333f9c8ff

def z242 : W := mkw 0x0100004441213880 0x0010000444121388 0xbe8520cfc3637001 0x3be8520cfc363700

def z243 : W := mkw 0x6000000036ca0000 0x06000000036ca000 0x1dcac0003fff0007 0xc1dcac0003fff000

def z244 : W := mkw 0x0000004001002800 0x0000000400100280 0xbe8520cfc3007c0b 0x7be8520cfc3007c0

def z245 : W := mkw 0x0200411300140552 0x0020041130014055 0x414ac330049c8ffe 0xc414ac330049c8ff

def z246 : W := mkw 0x4800004027002a08 0x04800004027002a0 0x0000000007000f02 0x00000000007000f0

def z247 : W := mkw 0xd83fbee8af00ea08 0xfd83fbee8af00ea0 0x82353cccfb007001 0x082353cccfb00700

def z248 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0xaa83003c00e070fd 0x6aa83003c00e070f

def z249 : W := mkw 0x402c000026000000 0x8402c00002600000 0x1ffec0003f9c0007 0xc1ffec0003f9c000

def z250 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xb44420cfc3137cca 0x3b44420cfc3137cc

def z251 : W := mkw 0x03004117403515d2 0x003004117403515d 0x1843e03fc0ff00f4 0x21843e03fc0ff00f

def z252 : W := mkw 0x023fe11300140552 0xe023fe1130014055 0x7fffe333049c8ffe 0xf7fffe333049c8ff

def z253 : W := mkw 0x783fb6c03fcaea08 0xe783fb6c03fcaea0 0x9ffffcc03fff7007 0xc9ffffcc03fff700

def z254 : W := mkw 0x343fac2c18e0d0a4 0xf343fac2c18e0d0a 0xffbffc3c38e0f0fd 0xeffbffc3c38e0f0f

def z255 : W := mkw 0x802cf39280000000 0xa802cf3928000000 0xf7bcffc3c0000000 0x1f7bcffc3c000000

def z256 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbe8520cfc0007cc8 0x3be8520cfc0007cc

def z257 : W := mkw 0x14000c2c0820d0a4 0x114000c2c0820d0a 0xe9821c3c0080f0fc 0xee9821c3c0080f0f

def z258 : W := mkw 0x0000000100100440 0x0000000010010044 0x3ec5200303730ccf 0x73ec5200303730cc

def z259 : W := mkw 0x0200411300140552 0x0020041130014055 0x60400333049c8ffe 0xf60400333049c8ff

def z260 : W := mkw 0x36134d3e18e4d1b6 0x536134d3e18e4d1b 0xebbbdf3c3cecf3fd 0xeebbbdf3c3cecf3f

def z261 : W := mkw 0x0200411200040112 0x0020041120004011 0x4000033000008330 0x0400003300000833

def z262 : W := mkw 0x7d3f1eed7ff1feec 0xd7d3f1eed7ff1fee 0xffff3ffffff3ffff 0xfffff3ffffff3fff

def z263 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xa20520cfc3637cc9 0x3a20520cfc3637cc

def z264 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3b01c0000000000 0x0e3b01c000000000

def z265 : W := mkw 0x402ca000260a0000 0xa402ca000260a000 0x1ecde000077f0007 0x41ecde000077f000

def z266 : W := mkw 0x613fa00576fb14c0 0xe613fa00576fb14c 0x1fffe00fffff00c7 0xe1fffe00fffff00c

def z267 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xfff73c3c3bf3f0ff 0xefff73c3c3bf3f0f

def z268 : W := mkw 0x34130c2818c0c024 0x534130c2818c0c02 0xebb31c3c38808030 0xaebb31c3c3880803

def z269 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe40c1fc00700ff0a 0x1e40c1fc00700ff0

def z270 : W := mkw 0x203fa00010ca0000 0xe203fa00010ca000 0x1fffe00000ff0004 0x01fffe00000ff000

def z271 : W := mkw 0x823ffbba80040112 0xf823ffbba8004011 0xffbfffffc48c8330 0xbffbfffffc48c833

def z272 : W := mkw 0x613fa04177db2c40 0xe613fa04177db2c4 0x1fffe0c3ffff0c07 0xd1fffe0c3ffff0c0

def z273 : W := mkw 0x98005ffa8900ea08 0x198005ffa8900ea0 0xe0001fffc000ff08 0x3e0001fffc000ff0

def z274 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x0000000000007cc8 0x00000000000007cc

def z275 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xfffbdc3c3cfcf0ff 0xefffbdc3c3cfcf0f

def z276 : W := mkw 0x0000000000000000 0x0000000000000000 0x6d8a033004808ffe 0xf6d8a033004808ff

def z277 : W := mkw 0x140004040820d0a4 0x0140004040820d0a 0x000000000000f0f8 0x0000000000000f0f

def z278 : W := mkw 0x6000000036ca0000 0x06000000036ca000 0x000000003b630001 0x0000000003b63000

def z279 : W := mkw 0x0000000400201080 0x0000000040020108 0xbe8520cfc06070cd 0x7be8520cfc06070c

def z280 : W := mkw 0x2013082810c00000 0x52013082810c0000 0xebb31c3c38e00005 0xeebb31c3c38e0000

def z281 : W := mkw 0x0200411200040112 0x0020041120004011 0x658ac330048c8f3a 0xd658ac330048c8f3

def z282 : W := mkw 0x402c004027002800 0x8402c00402700280 0xa7bc00c03f007c0b 0xda7bc00c03f007c0

def z283 : W := mkw 0xfc3ffffebfe0faac 0xffc3ffffebfe0faa 0xffbfffffffe0ffff 0xfffbfffffffe0fff

def z284 : W := mkw 0x683fb2c037ca2a08 0xe683fb2c037ca2a0 0x1fffe3c03fff0f07 0xd1fffe3c03fff0f0

def z285 : W := mkw 0x343f1eac18e0d0a4 0xd343f1eac18e0d0a 0xefbf1ffc38e0f0fd 0xfefbf1ffc38e0f0f

def z286 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000030000080f8 0x260000030000080f

def z287 : W := mkw 0x0200000100140552 0x0020000010014055 0x00400000041c0f02 0x000400000041c0f0

def z288 : W := mkw 0x803ffbbb80100440 0xf803ffbbb8010044 0xffffffffc0100cce 0x7ffffffffc0100cc

def z289 : W := mkw 0x00000005003014c0 0x000000005003014c 0xbec1000f00707ccf 0x7bec1000f00707cc

def z290 : W := mkw 0x0200411300140552 0x0020041130014055 0x75c8c303041c8f0a 0xd75c8c303041c8f0

def z291 : W := mkw 0x5a0045532f14ef5a 0x05a0045532f14ef5 0x7dcac3333f9cffff 0xf7dcac3333f9cfff

def z292 : W := mkw 0x36134d3f18f4d5f6 0x536134d3f18f4d5f 0xebb31f3f38e0fffd 0xfebb31f3f38e0fff

def z293 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x7fffe0303fff80ff 0xe7fffe0303fff80f

def z294 : W := mkw 0x813fbaedc1313cc0 0xf813fbaedc1313cc 0xbef53ccfc3737ccf 0x7bef53ccfc3737cc

def z295 : W := mkw 0x0113086d41313cc0 0x50113086d41313cc 0xfff73cffc3737ccf 0x7fff73cffc3737cc

def z296 : W := mkw 0x0200000100140552 0x0020000010014055 0x65c80300049c8ffe 0xd65c80300049c8ff

def z297 : W := mkw 0x37134d7f59f5fdf6 0x537134d7f59f5fdf 0xffffffffffffffff 0xffffffffffffffff

def z298 : W := mkw 0xb53fffffd9f1fce4 0xfb53fffffd9f1fce 0xfffffffffbf3fcff 0xffffffffffbf3fcf

def z299 : W := mkw 0x603fa00436ea1080 0xe603fa00436ea108 0xbfffe00c3fff70cf 0xebfffe00c3fff70c

def z300 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x553efff3c0000000 0x1553efff3c000000

def z301 : W := mkw 0x592c16c16f11ee48 0x8592c16c16f11ee4 0xf7fc3fc3ff13ff0b 0xdf7fc3fc3ff13ff0

def z302 : W := mkw 0x7c3f1ee83fc0ea2c 0xd7c3f1ee83fc0ea2 0xe7be1ff03f80ff3b 0xde7be1ff03f80ff3

def z303 : W := mkw 0x0000411200000000 0x0000041120000000 0x1408c30300000000 0x11408c3030000000

def z304 : W := mkw 0xd83ffffaaf00ea08 0xfd83ffffaaf00ea0 0xffbffffffb007001 0x3ffbffffffb00700

def z305 : W := mkw 0x6200000136de0552 0x06200000136de055 0x004000003fff8fff 0xc004000003fff8ff

def z306 : W := mkw 0x0100004141112c40 0x00100004141112c4 0xbec520cfc3130c02 0x3bec520cfc3130c0

def z307 : W := mkw 0x412c004567313cc0 0x8412c004567313cc 0xbffd20cfff737ccf 0xfbffd20cfff737cc

def z308 : W := mkw 0xc82cf3d2a7002a08 0xac82cf3d2a7002a0 0x140ce3c3c7000f02 0x1140ce3c3c7000f0

def z309 : W := mkw 0x402c128026000000 0x8402c12802600000 0xe7bc1fc03f000003 0xde7bc1fc03f00000

def z310 : W := mkw 0x0100004441213880 0x0010000444121388 0x800000ccc0007000 0x0800000ccc000700

def z311 : W := mkw 0x603fa04037ca2800 0xe603fa04037ca280 0xbfffe0c03fff7c0f 0xdbfffe0c03fff7c0

def z312 : W := mkw 0x0000000000000000 0x0000000000000000 0x1448c000041c0002 0x01448c000041c000

def z313 : W := mkw 0x080012c001002a08 0x0080012c001002a0 0x000003c000000f00 0x1000003c000000f0

def z314 : W := mkw 0x14000c2c0820d0a4 0x114000c2c0820d0a 0x80001c0c00007000 0x080001c0c0000700

def z315 : W := mkw 0x822cf39380140552 0xa822cf3938014055 0x7dcee3f3c49c8ffe 0xf7dcee3f3c49c8ff

def z316 : W := mkw 0xc03ffbbaa6000000 0xfc03ffbbaa600000 0xffbfffffff000003 0xfffbfffffff00000

def z317 : W := mkw 0x0200411300140552 0x0020041130014055 0x6982033300808ffc 0xf6982033300808ff

def z318 : W := mkw 0x82005bbb80140552 0x182005bbb8014055 0xfdcadfffc49c8ffe 0xffdcadfffc49c8ff

def z319 : W := mkw 0x0000000100100440 0x0000000010010044 0x2000000300000cc8 0x32000000300000cc

def z320 : W := mkw 0x0200000000040112 0x0020000000004011 0x00000000048c8330 0x800000000048c833

def z321 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x07bd20003f630003 0xc07bd20003f63000

def z322 : W := mkw 0x0200411300140552 0x0020041130014055 0x1dcac303049c0f06 0xd1dcac303049c0f0

def z323 : W := mkw 0x6100004577fb3cc0 0x06100004577fb3cc 0xbec520cfffff7ccf 0xfbec520cfffff7cc

def z324 : W := mkw 0x0300004541353dd2 0x00300004541353dd 0x0040000007ffffff 0xc0040000007fffff

def z325 : W := mkw 0x35130c6d59f1fce4 0x535130c6d59f1fce 0xebf31c3c3bf3fcff 0xeebf31c3c3bf3fcf

def z326 : W := mkw 0x812cf3d3c1112c40 0xa812cf3d3c1112c4 0x144ce3c3c3130c02 0x1144ce3c3c3130c0

def z327 : W := mkw 0x0100004441213880 0x0010000444121388 0xaa8520ccc36370cd 0x6aa8520ccc36370c

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x6588030000000000 0x1658803000000000

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a81000000600005 0x40a8100000060000

def z330 : W := mkw 0x6000000036ca0000 0x06000000036ca000 0x1ec520003fff0007 0xc1ec520003fff000

def z331 : W := mkw 0x0000411200000000 0x0000041120000000 0x6000033300000000 0x3600003330000000

def z332 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x453c1fc03f008f02 0x9453c1fc03f008f0

def z333 : W := mkw 0x0000000000000000 0x0000000000000000 0xbec520cfc3730007 0x7bec520cfc373000

def z334 : W := mkw 0x100004400900e800 0x0100004400900e80 0xe7b41cc03b00fc0b 0xde7b41cc03b00fc0

def z335 : W := mkw 0x190016c54931fec8 0x0190016c54931fec 0xe0001fcfc000ffc8 0x3e0001fcfc000ffc

def z336 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x040c03c03f00ff0b 0xd040c03c03f00ff0

def z337 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xaac1000c03737ccf 0x6aac1000c03737cc

def z338 : W := mkw 0xf83ffffabfcaea08 0xff83ffffabfcaea0 0xffffffffffffff0f 0xfffffffffffffff0

def z339 : W := mkw 0x8000539280000000 0x0800053928000000 0x000003c3c0000000 0x1000003c3c000000

def z340 : W := mkw 0x813ffbfbc1112c40 0xf813ffbfbc1112c4 0xffffffffc3130c02 0x3ffffffffc3130c0

def z341 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x8bb31c0c38e07005 0xc8bb31c0c38e0700

def z342 : W := mkw 0x823ffbba80040112 0xf823ffbba8004011 0x413adf30048c8330 0x8413adf30048c833

def z343 : W := mkw 0x3413ac2c18ead0a4 0x73413ac2c18ead0a 0xfbf3fc3c38fff0fd 0xefbf3fc3c38fff0f

def z344 : W := mkw 0x0000000400201080 0x0000000040020108 0x0801000c006000c4 0x20801000c006000c

def z345 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x593bff3fc0000000 0x2593bff3fc000000

def z346 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x1841200fc3737ccf 0x61841200fc3737cc

def z347 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x1ff720003bf30007 0xc1ff720003bf3000

def z348 : W := mkw 0x34130c2818c0c024 0x534130c2818c0c02 0xe3b21c303880f039 0xce3b21c303880f03

def z349 : W := mkw 0x802cb28080000000 0xa802cb2808000000 0x000420c0c0000000 0x0000420c0c000000

def z350 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1bf3e00038ff0005 0xc1bf3e00038ff000

def z351 : W := mkw 0x0000000000000000 0x0000000000000000 0x4108030004008300 0x8410803000400830

def z352 : W := mkw 0x803fe93a80000000 0xf803fe93a8000000 0x1fbfe03fc0000000 0x21fbfe03fc000000

def z353 : W := mkw 0x6100004577fb3cc0 0x06100004577fb3cc 0x004000003fff7ccf 0xc004000003fff7cc

def z354 : W := mkw 0x743fac2c3eead0a4 0xf743fac2c3eead0a 0xebb73c3c3be3f0fd 0xeebb73c3c3be3f0f

def z355 : W := mkw 0x002c000000000000 0x8002c00000000000 0x07bc000000000000 0x007bc00000000000

def z356 : W := mkw 0x10130c280800c000 0x510130c280800c00 0xebb31c3c3800f009 0xeebb31c3c3800f00

def z357 : W := mkw 0x01000005403114c0 0x001000005403114c 0xbec520cfc07300c4 0x3bec520cfc07300c

def z358 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0xebb31c3c00e000f4 0x2ebb31c3c00e000f

def z359 : W := mkw 0x602c000036ca0000 0x8602c000036ca000 0x07fc00003fff0007 0xc07fc00003fff000

def z360 : W := mkw 0x5a2c57d32f14ef5a 0x85a2c57d32f14ef5 0xe7bc1ff33f00fffb 0xfe7bc1ff33f00fff

def z361 : W := mkw 0x0200000100140552 0x0020000010014055 0x00400000049c8ffe 0xc00400000049c8ff

def z362 : W := mkw 0x94005fbe8820d0a4 0x194005fbe8820d0a 0xe0001fffc000f0f8 0x3e0001fffc000f0f

def z363 : W := mkw 0x403fa000260a0000 0xe403fa000260a000 0x1fffe000071f0002 0x01fffe000071f000

def z364 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x1ec5200003737ccf 0x41ec5200003737cc

def z365 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000008080fc 0xc00000000008080f

def z366 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1a77e0003bff0005 0x01a77e0003bff000

def z367 : W := mkw 0x0000411200000000 0x0000041120000000 0x7d8ac333008080fc 0xf7d8ac333008080f

def z368 : W := mkw 0x5b2c57d76f35ffda 0x85b2c57d76f35ffd 0xffffffffffffffff 0xffffffffffffffff

def z369 : W := mkw 0x592c16c46f21fa88 0x8592c16c46f21fa8 0x82353cccfb637001 0x082353cccfb63700

def z370 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03b007001 0x1e7bc1fc03b00700

def z371 : W := mkw 0xb43fffba98c0c024 0xfb43fffba98c0c02 0xffbffffff8808030 0xbffbffffff880803

def z372 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x7fffe3003fff8f0f 0xd7fffe3003fff8f0

def z373 : W := mkw 0x7a3ff7d33fdeef5a 0xe7a3ff7d33fdeef5 0xfffffff33fffffff 0xffffffff33ffffff

def z374 : W := mkw 0x0200000100140552 0x0020000010014055 0x0000000000008ff8 0x00000000000008ff

def z375 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x0030000038000000 0x0003000003800000

def z376 : W := mkw 0x34134d3e18e0d0a4 0x534134d3e18e0d0a 0xffbbdf3f38e0f0fd 0xfffbbdf3f38e0f0f

def z377 : W := mkw 0x0200411300140552 0x0020041130014055 0x7448c333041c8ffa 0x37448c333041c8ff

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x28800000000000cc 0x628800000000000c

def z379 : W := mkw 0x0000000100100440 0x0000000010010044 0x18400003001000c4 0x218400003001000c

def z380 : W := mkw 0x613fa04477eb3880 0xe613fa04477eb388 0x823520ccfb637001 0x0823520ccfb63700

def z381 : W := mkw 0x180016c00900ea08 0x0180016c00900ea0 0x80001cc000007000 0x080001cc00000700

def z382 : W := mkw 0x120045130814c552 0x0120045130814c55 0xfffadf333c9cffff 0xffffadf333c9cfff

def z383 : W := mkw 0x0000082800000000 0x1000008280000000 0xe0001c3c00000000 0x2e0001c3c0000000

def z384 : W := mkw 0x0000000100100440 0x0000000010010044 0x0040000000100cce 0x40040000000100cc

def z385 : W := mkw 0x0000411300100440 0x0000041130010044 0x7dcac33300100cce 0x77dcac33300100cc

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x0588000004000002 0xc058800000400000

def z387 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xa6c400c003737ccf 0x5a6c400c003737cc

def z388 : W := mkw 0x81005bffc1313cc0 0x181005bffc1313cc 0xfec53fffc3737ccf 0x7fec53fffc3737cc

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0x1444200003130002 0x0144420000313000

def z391 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x863c1fc03f007f03 0x1863c1fc03f007f0

def z392 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0x7d8be33fc0000000 0x37d8be33fc000000

def z393 : W := mkw 0x743f0c2c3ee0d0a4 0xd743f0c2c3ee0d0a 0xefbf1c3c3fe0f0ff 0xeefbf1c3c3fe0f0f

def z394 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000cfc0000000 0x3a00000cfc000000

def z395 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x9a4520cfc37370c5 0x29a4520cfc37370c

def z396 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1dcbe00004ff0006 0xc1dcbe00004ff000

def z397 : W := mkw 0x0000004401203880 0x0000000440120388 0xae8500cc03607ccf 0x7ae8500cc03607cc

def z398 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x7dbadf3300000000 0x37dbadf330000000

def z399 : W := mkw 0x0000004001002800 0x0000000400100280 0xe78c03c00700ff0b 0xde78c03c00700ff0

def z400 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xa6b41cc03b007c0b 0x5a6b41cc03b007c0

def z401 : W := mkw 0x812cf3d7c1313cc0 0xa812cf3d7c1313cc 0xbecde3cfc3737ccf 0x7becde3cfc3737cc

def z402 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbe1ff03f80ffff 0xfefbe1ff03f80fff

def z403 : W := mkw 0x36130c2d18f4d5f6 0x536130c2d18f4d5f 0xebf31c3c3cfcffff 0xeebf31c3c3cfcfff

def z404 : W := mkw 0x110004454931fcc0 0x0110004454931fcc 0xfff53ccffb73fccf 0xffff53ccffb73fcc

def z405 : W := mkw 0x402ca000260a0000 0xa402ca000260a000 0x17fce0003f1f0003 0xc17fce0003f1f000

def z406 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0231000038600001 0x0023100003860000

def z407 : W := mkw 0x802cfbba80000000 0xb802cfbba8000000 0xf40cffffc0000000 0x3f40cffffc000000

def z408 : W := mkw 0x0200411200040112 0x0020041120004011 0x5dcac330049c8336 0xc5dcac330049c833

def z409 : W := mkw 0x813ffbffc1313cc0 0xf813ffbffc1313cc 0xffbfffffc0007cc8 0x3ffbfffffc0007cc

def z410 : W := mkw 0x580004402f00ea08 0x0580004402f00ea0 0xa68400c03f00ff0b 0xda68400c03f00ff0

def z411 : W := mkw 0x623fa00136de0552 0xe623fa00136de055 0x1fffe0003fff8fff 0xc1fffe0003fff8ff

def z412 : W := mkw 0x3c131eec19e0faac 0x53c131eec19e0faa 0xebb31ffc38e0fffd 0xfebb31ffc38e0fff

def z413 : W := mkw 0x35130c2d58f1d4e4 0x535130c2d58f1d4e 0xfbf33c3ff8f3f0fd 0xefbf33c3ff8f3f0f

def z414 : W := mkw 0x03004117403515d2 0x003004117403515d 0x7dcbe33fc4ff8ffe 0xf7dcbe33fc4ff8ff

def z415 : W := mkw 0x582c16c12f10ee48 0x8582c16c12f10ee4 0xfffc1fc33f10ffcf 0xffffc1fc33f10ffc

def z416 : W := mkw 0xe03ff392b6ca0000 0xee03ff392b6ca000 0x1fffe3c3ffff0007 0xd1fffe3c3ffff000

def z417 : W := mkw 0x4000000026000000 0x0400000002600000 0x000000003f000003 0xc000000003f00000

def z418 : W := mkw 0x100004000800c000 0x0100004000800c00 0x41301c0038008000 0x841301c003800800

def z419 : W := mkw 0x3600040518f4d5f6 0x03600040518f4d5f 0x004000003cfcffff 0xc004000003cfcfff

def z420 : W := mkw 0xd93fffffef31fec8 0xfd93fffffef31fec 0xffffffffff73ffcf 0xfffffffffff73ffc

def z421 : W := mkw 0x022c539300140552 0x8022c53930014055 0xfffedff3049c8ffe 0xffffedff3049c8ff

def z422 : W := mkw 0x182c16c00900ea08 0x8182c16c00900ea0 0xe7bc1fc00000ff08 0x1e7bc1fc00000ff0

def z423 : W := mkw 0x3400040018c0c024 0x03400040018c0c02 0x0000000038808030 0x8000000003880803

def z424 : W := mkw 0x0200000100140552 0x0020000010014055 0x69c20030049c8ffe 0xe69c20030049c8ff

def z425 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x9a37fcffc0000000 0x29a37fcffc000000

def z426 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xfd8adfffc0000000 0x3fd8adfffc000000

def z427 : W := mkw 0x0300415741353dd2 0x00300415741353dd 0xe00003ffc000fff8 0x3e00003ffc000fff

def z428 : W := mkw 0x623fe11336de0552 0xe623fe11336de055 0x1fffe3033fff0f07 0xd1fffe3033fff0f0

def z429 : W := mkw 0x580004402f00ea08 0x0580004402f00ea0 0x658803003f00ff0b 0xd658803003f00ff0

def z430 : W := mkw 0x34130c2818c0c024 0x534130c2818c0c02 0x69b21c30388080fc 0xe69b21c30388080f

def z431 : W := mkw 0xb4135fbe98e0d0a4 0x5b4135fbe98e0d0a 0xebb31ffff8e0f0fd 0xfebb31ffff8e0f0f

def z432 : W := mkw 0x002c128000000000 0x8002c12800000000 0x41381f0000000000 0x041381f000000000

def z433 : W := mkw 0xc02cf392a60a0000 0xac02cf392a60a000 0x144ce3c3c71f0002 0x1144ce3c3c71f000

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x4102003000808030 0x8410200300080803

def z435 : W := mkw 0x402ca000260a0000 0xa402ca000260a000 0x0004200003030000 0x0000420000303000

def z436 : W := mkw 0x492c12c167112e48 0x8492c12c167112e4 0x144c23c3c7130f02 0x1144c23c3c7130f0

def z437 : W := mkw 0x0000411200000000 0x0000041120000000 0x1802c03300000000 0x21802c0330000000

def z438 : W := mkw 0x0013082c00201080 0x50013082c0020108 0xebb31c3c006070cd 0x6ebb31c3c006070c

def z439 : W := mkw 0x613fa04577fb3cc0 0xe613fa04577fb3cc 0x1fffe0003fff7ccf 0xc1fffe0003fff7cc

def z440 : W := mkw 0x01000005403114c0 0x001000005403114c 0x0000000fc00000c0 0x20000000fc00000c

def z441 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x1ffbc0003cfc0007 0xc1ffbc0003cfc000

def z442 : W := mkw 0x5a2c57d32f14ef5a 0x85a2c57d32f14ef5 0xf7fcdfc33f1cff0b 0xdf7fcdfc33f1cff0

def z443 : W := mkw 0x0100004141112c40 0x00100004141112c4 0x1ec520c3c3730c07 0x51ec520c3c3730c0

def z444 : W := mkw 0xc03ffbbaa60a0000 0xfc03ffbbaa60a000 0xffffffffc71f0002 0x3ffffffffc71f000

def z445 : W := mkw 0x102c16800800c000 0x8102c16800800c00 0xe7bc1fc03800f009 0xde7bc1fc03800f00

def z446 : W := mkw 0x8000493a80000000 0x18000493a8000000 0x0000003fc0000000 0x20000003fc000000

def z447 : W := mkw 0x592c16c46f21fa88 0x8592c16c46f21fa8 0xe7bd3fccff63ff0b 0xde7bd3fccff63ff0

def z448 : W := mkw 0x2213e11310de0552 0x62213e11310de055 0x1843e03300ff00f4 0x21843e03300ff00f

def z449 : W := mkw 0x2000000010ca0000 0x02000000010ca000 0x0040000000ff0004 0x00040000000ff000

def z450 : W := mkw 0x0000000000000000 0x0000000000000000 0x6982003000000000 0x2698200300000000

def z451 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x1c4520cfc3730cc6 0x31c4520cfc3730cc

def z452 : W := mkw 0x783fb6803ecac208 0xe783fb6803ecac20 0x413adf003c8c8300 0x8413adf003c8c830

def z453 : W := mkw 0x6013a00036ca0000 0x66013a00036ca000 0x1843e0003fff0007 0xc1843e0003fff000

def z454 : W := mkw 0x580004402f00ea08 0x0580004402f00ea0 0x000000003b007001 0x0000000003b00700

def z455 : W := mkw 0x582c57d22f00ea08 0x8582c57d22f00ea0 0xffbedff33f00ff0b 0xfffbedff33f00ff0

def z456 : W := mkw 0x40000000260a0000 0x040000000260a000 0x00400000071f0002 0x000400000071f000

def z457 : W := mkw 0x7e3f5fff3ff4fffe 0xd7e3f5fff3ff4fff 0xffffdfff3ffcffff 0xfffffdfff3ffcfff

def z458 : W := mkw 0x100004000800c000 0x0100004000800c00 0xe0001c000000f008 0x0e0001c000000f00

def z459 : W := mkw 0x802c5bba80000000 0x9802c5bba8000000 0xe7bc1fffc0000000 0x3e7bc1fffc000000

def z460 : W := mkw 0x0200411300140552 0x0020041130014055 0x7cc0033300108ffe 0x77cc0033300108ff

def z461 : W := mkw 0x180004400900ea08 0x0180004400900ea0 0x000000000000ff08 0x0000000000000ff0

def z462 : W := mkw 0x743fac283ecac024 0xf743fac283ecac02 0x5ffffc303fff8037 0xc5ffffc303fff803

def z463 : W := mkw 0xd83fffbaae00c208 0xfd83fffbaae00c20 0xffbffffffc008300 0xbffbffffffc00830

def z464 : W := mkw 0x0300415741353dd2 0x00300415741353dd 0xfdcac3ffc49cfffe 0xffdcac3ffc49cfff

def z465 : W := mkw 0x813fbaecc1213880 0xf813fbaecc121388 0x82353cccc3637001 0x082353cccc363700

def z466 : W := mkw 0x002c12c001002800 0x8002c12c00100280 0xe7bc1fc003007c0b 0x5e7bc1fc003007c0

def z467 : W := mkw 0x34130c2818c0c024 0x534130c2818c0c02 0x00301c0038000000 0x000301c003800000

def z468 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0xbeb53ccfc0000000 0x3beb53ccfc000000

def z469 : W := mkw 0x0200411300140552 0x0020041130014055 0xffcfe3ffc49c8ffe 0xfffcfe3ffc49c8ff

def z470 : W := mkw 0x623fe11236ce0112 0xe623fe11236ce011 0x413ac3303c8c8330 0x8413ac3303c8c833

def z471 : W := mkw 0x0000a000000a0000 0x20000a000000a000 0x1040e000001f0000 0x01040e000001f000

def z472 : W := mkw 0x783f16c03fc0ea08 0xc783f16c03fc0ea0 0xefbf1fc03fe0ff0f 0xdefbf1fc03fe0ff0

def z473 : W := mkw 0xda3ffffbaf14ef5a 0xfda3ffffbaf14ef5 0xffffffffff9cffff 0xfffffffffff9cfff

def z474 : W := mkw 0x7c3f1eec3fe0faac 0xd7c3f1eec3fe0faa 0xebb71cfc3be0f0fd 0xeebb71cfc3be0f0f

def z475 : W := mkw 0x0000000000000000 0x0000000000000000 0x03b0000038000001 0xc03b000003800000

def z476 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xa68400cfc3007ccb 0x7a68400cfc3007cc

def z477 : W := mkw 0x3400040418e0d0a4 0x03400040418e0d0a 0xe3b01c0038e0f0fd 0xce3b01c0038e0f0f

def z478 : W := mkw 0x403fa00026000000 0xe403fa0002600000 0x1fbfe0003f000003 0xc1fbfe0003f00000

def z479 : W := mkw 0xa013e93a90ca0000 0x7a013e93a90ca000 0x1843e03fc0ff0004 0x21843e03fc0ff000

def z480 : W := mkw 0x803ffbbe80201080 0xf803ffbbe8020108 0xffbfffffc06070cd 0x7ffbfffffc06070c

def z481 : W := mkw 0x0100004141112c40 0x00100004141112c4 0x3cc420c3c3130cce 0x73cc420c3c3130cc

def z482 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xb84120cfc0737ccc 0x3b84120cfc0737cc

def z483 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1c4fe00007ff0006 0x01c4fe00007ff000

def z484 : W := mkw 0x34130c2d18f0d4e4 0x534130c2d18f0d4e 0xfff31c3f38f0fcff 0xffff31c3f38f0fcf

def z485 : W := mkw 0x0100004141112c40 0x00100004141112c4 0x000000c3c0000c00 0x1000000c3c0000c0

def z486 : W := mkw 0x100004000800c000 0x0100004000800c00 0x000000003800f009 0xc000000003800f00

def z487 : W := mkw 0x2400000410e010a4 0x02400000410e010a 0x0000000000e000f4 0x00000000000e000f

def z488 : W := mkw 0x3400040418e0d0a4 0x03400040418e0d0a 0xaa81000c38e0f0fd 0xeaa81000c38e0f0f

def z489 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0803000000e00004 0x00803000000e0000

def z490 : W := mkw 0x8013fbba80000000 0x78013fbba8000000 0xf803ffffc0000000 0x3f803ffffc000000

def z491 : W := mkw 0x0100000440211080 0x0010000044021108 0x0001200cc0630000 0x00001200cc063000

def z492 : W := mkw 0x582c16802e00c208 0x8582c16802e00c20 0xe3b81f003c00f309 0xce3b81f003c00f30

def z493 : W := mkw 0x8013a82880000000 0x78013a8288000000 0x0001200cc0000000 0x00001200cc000000

def z494 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0xbe87e0ffc0000000 0x3be87e0ffc000000

def z495 : W := mkw 0x613fa04577fb3cc0 0xe613fa04577fb3cc 0xbef520cffb737ccf 0x7bef520cffb737cc

def z496 : W := mkw 0xc83ffbfaa7002a08 0xfc83ffbfaa7002a0 0xffbfffffc7000f02 0x3ffbfffffc7000f0

def z497 : W := mkw 0x2413a82c10ea10a4 0x72413a82c10ea10a 0x1843e03c00ff00f4 0x21843e03c00ff00f

def z498 : W := mkw 0x15000c6d4931fce4 0x115000c6d4931fce 0xfec53cffc373fcff 0x7fec53cffc373fcf

def z499 : W := mkw 0x743fac2c3eead0a4 0xf743fac2c3eead0a 0xebbbdc3c3cecf0fd 0xeebbbdc3c3cecf0f

def z500 : W := mkw 0x0200411300140552 0x0020041130014055 0x7842c333009c8ffc 0x37842c333009c8ff

def z501 : W := mkw 0x0200000100140552 0x0020000010014055 0x3cc00003049c8ffe 0xf3cc00003049c8ff

def z502 : W := mkw 0x422ce113261e0552 0xa422ce113261e055 0x144ce303071f0f02 0x1144ce303071f0f0

def z503 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x824520ccc3737ccf 0x4824520ccc3737cc

def z504 : W := mkw 0x36134d3b18d4c576 0x536134d3b18d4c57 0x7dfadf333c9c8ffe 0xf7dfadf333c9c8ff

def z505 : W := mkw 0x002c128000000000 0x8002c12800000000 0xffbd3fcfc0000000 0x3ffbd3fcfc000000

def z506 : W := mkw 0x0200411300140552 0x0020041130014055 0x594ac333049c83f4 0xa594ac333049c83f

def z507 : W := mkw 0x002c128000000000 0x8002c12800000000 0xe7bc1fc004008f0a 0xde7bc1fc004008f0

def z508 : W := mkw 0x833ffbffc1353dd2 0xf833ffbffc1353dd 0xffffffffc7ffffff 0xfffffffffc7fffff

def z509 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x0001200000630000 0x0000120000063000

def z510 : W := mkw 0x003fe11200000000 0xe003fe1120000000 0x7fbfe33300000000 0x37fbfe3330000000

def z511 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x0235200000000000 0x0023520000000000

def z512 : W := mkw 0x0100004441213880 0x0010000444121388 0x0000000003637001 0x0000000000363700

def z513 : W := mkw 0x14000c280800c024 0x114000c280800c02 0x40001c3000008030 0x040001c300000803

def z514 : W := mkw 0x180016c00900ea08 0x0180016c00900ea0 0xe5881fc00400ff0a 0xde5881fc00400ff0

def z515 : W := mkw 0x0200411200040112 0x0020041120004011 0x0008c300040c0300 0x00008c300040c030

def z516 : W := mkw 0x16004d3f0834d5f6 0x116004d3f0834d5f 0xe0001f3f0000fff8 0x3e0001f3f0000fff

def z517 : W := mkw 0x0200411300140552 0x0020041130014055 0x1448c303049c8ffe 0xd1448c303049c8ff

def z518 : W := mkw 0xb413ed3e98e0d0a4 0x7b413ed3e98e0d0a 0xfbb3fc3ff8e0f0fd 0xefbb3fc3ff8e0f0f

def z519 : W := mkw 0xe03fbaa8b6ca0000 0xfe03fbaa8b6ca000 0x82353cccfb630001 0x082353cccfb63000

def z520 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x6bb3003038e080fd 0xe6bb3003038e080f

def z521 : W := mkw 0x813ffbfec1213880 0xf813ffbfec121388 0xffbfffffc3637001 0x3ffbfffffc363700

def z522 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0x0002c03000000000 0x00002c0300000000

def z523 : W := mkw 0x36134d3a18c4c136 0x536134d3a18c4c13 0x413adf303c8c8330 0x8413adf303c8c833

def z524 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1fbfe0003b630001 0x01fbfe0003b63000

def z525 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x033fe0003fef0001 0x8033fe0003fef000

def z526 : W := mkw 0x0200411300140552 0x0020041130014055 0x3cc8c303041c0fce 0x73cc8c303041c0fc

def z527 : W := mkw 0x5c2c1eec2f20faac 0x95c2c1eec2f20faa 0xe7bc1ffc3f00fffb 0xfe7bc1ffc3f00fff

def z528 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe3b41cc03b00f009 0xce3b41cc03b00f00

def z529 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0xe7bd3fccc0000000 0x1e7bd3fccc000000

def z530 : W := mkw 0x580016c02f00ea08 0x0580016c02f00ea0 0xe0001fc03f00ff0b 0xde0001fc03f00ff0

def z531 : W := mkw 0x582c16c42f20fa88 0x8582c16c42f20fa8 0xefbd1fcc3f60ffcf 0xfefbd1fcc3f60ffc

def z532 : W := mkw 0x623fe11336de0552 0xe623fe11336de055 0x1fffe0333fff00f7 0xe1fffe0333fff00f

def z533 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0x6983003c00e080fc 0xe6983003c00e080f

def z534 : W := mkw 0x743fac283ecac024 0xf743fac283ecac02 0x413adc303c8c8030 0x8413adc303c8c803

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0x7dcac030049c80fe 0xe7dcac030049c80f

def z536 : W := mkw 0x582c16802e00c208 0x8582c16802e00c20 0xe7bc1fc03c008300 0x9e7bc1fc03c00830

def z537 : W := mkw 0x823ffbbb80140552 0xf823ffbbb8014055 0xffbfffffc0008ff8 0x3ffbfffffc0008ff

def z538 : W := mkw 0x34000c2c18e0d0a4 0x134000c2c18e0d0a 0xe0001c3c38e0f0fd 0xee0001c3c38e0f0f

def z539 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xaab11c0c386070cd 0x6aab11c0c386070c

def z540 : W := mkw 0x81005bffc1313cc0 0x181005bffc1313cc 0xe0001fffc0007cc8 0x3e0001fffc0007cc

def z541 : W := mkw 0x412ca045673b3cc0 0xa412ca045673b3cc 0xbecde0cfc77f7ccf 0x7becde0cfc77f7cc

def z542 : W := mkw 0x002ca00000000000 0xa002ca0000000000 0x140ce00000000000 0x0140ce0000000000

def z543 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1ef520003b730007 0x41ef520003b73000

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000030000008f08 0x16000030000008f0

def z545 : W := mkw 0x2113004551f13cc0 0x42113004551f13cc 0xbff720cffbf37ccf 0xfbff720cffbf37cc

def z546 : W := mkw 0x013fa04541313cc0 0xe013fa04541313cc 0xbfffe0cfc3737ccf 0x7bfffe0cfc3737cc

def z547 : W := mkw 0x783fb6803ecac208 0xe783fb6803ecac20 0x5fffff003fff8307 0xc5fffff003fff830

def z548 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x5fbfff3000000000 0x05fbfff300000000

def z549 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x027520003fff0007 0xc027520003fff000

def z550 : W := mkw 0x5a2c16c12f14ef5a 0x85a2c16c12f14ef5 0xe7fc1fc03f9cffff 0xde7fc1fc03f9cfff

def z551 : W := mkw 0x203fa00010c00000 0xe203fa00010c0000 0x1fbfe00038e00005 0xc1fbfe00038e0000

def z552 : W := mkw 0x180016c00900ea08 0x0180016c00900ea0 0xe6841fc00300ff0b 0x5e6841fc00300ff0

def z553 : W := mkw 0x003f1aa800000000 0xd003f1aa80000000 0xefbf1ffc00000000 0x3efbf1ffc0000000

def z554 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xc33c1fc03f00f301 0x8c33c1fc03f00f30

def z555 : W := mkw 0x5a2c57932e14c75a 0x85a2c57932e14c75 0x7dfadf333c9c8ffe 0xf7dfadf333c9c8ff

def z556 : W := mkw 0x0000000100100440 0x0000000010010044 0x3dcac003049c0cce 0xf3dcac003049c0cc

def z557 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xe7bedff000000000 0x1e7bedff00000000

def z558 : W := mkw 0x16004d3f0834d5f6 0x116004d3f0834d5f 0xfdcadf3f049cfffe 0xffdcadf3f049cfff

def z559 : W := mkw 0x0000000000000000 0x0000000000000000 0x1e85200000000000 0x01e8520000000000

def z560 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffffffffc3730007 0x7ffffffffc373000

def z561 : W := mkw 0x0000000100100440 0x0000000010010044 0xbec520cfc0100cce 0x7bec520cfc0100cc

def z562 : W := mkw 0x603fa00136da0440 0xe603fa00136da044 0x3fffe0033fff0ccf 0xf3fffe0033fff0cc

def z563 : W := mkw 0x592c16c56f31fec8 0x8592c16c56f31fec 0xe7bc1fcfff00ffcb 0xfe7bc1fcfff00ffc

def z564 : W := mkw 0x603fe11236ca0000 0xe603fe11236ca000 0x7fffe3333fff0007 0xf7fffe3333fff000

def z565 : W := mkw 0x623fe11236ce0112 0xe623fe11236ce011 0x5fffe3303fff8337 0xc5fffe3303fff833

def z566 : W := mkw 0x0000000000000000 0x0000000000000000 0x0205200003630001 0x0020520000363000

def z567 : W := mkw 0x482c128026000208 0x8482c12802600020 0x0008030004000300 0x0000803000400030

def z568 : W := mkw 0x703fa4003ecac000 0xe703fa4003ecac00 0xfffffc003ffff00f 0xcfffffc003ffff00

def z569 : W := mkw 0x1a0057d30914ef5a 0x01a0057d30914ef5 0xe0001ff30000fff8 0x3e0001ff30000fff

def z570 : W := mkw 0x7c130c6c3fe0faac 0x57c130c6c3fe0faa 0xebb31c3c3fe0ffff 0xeebb31c3c3fe0fff

def z571 : W := mkw 0x0000000000000000 0x0000000000000000 0x2480000000000c0a 0x52480000000000c0

def z572 : W := mkw 0x743fac2c3eead0a4 0xf743fac2c3eead0a 0x82353c0c3b637001 0x082353c0c3b63700

def z573 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0x0001000c00600000 0x00001000c0060000

def z574 : W := mkw 0x35130c6d59f1fce4 0x535130c6d59f1fce 0xebb31cfff8e0fcfd 0xfebb31cfff8e0fcf

def z575 : W := mkw 0x0000004101102c40 0x00000004101102c4 0xbec400c303107ccf 0x7bec400c303107cc

def z576 : W := mkw 0x623fe11336de0552 0xe623fe11336de055 0x7dfac3333c9c8ffe 0xf7dfac3333c9c8ff

def z577 : W := mkw 0x0000000400201080 0x0000000040020108 0xbec5200c037370cf 0x6bec5200c037370c

def z578 : W := mkw 0x780004403fcaea08 0x0780004403fcaea0 0x004000003fffff0f 0xc004000003fffff0

def z579 : W := mkw 0x8113e97fc1313cc0 0x78113e97fc1313cc 0xbec7e0ffc3737ccf 0x7bec7e0ffc3737cc

def z580 : W := mkw 0x0000000400201080 0x0000000040020108 0x8201000c00607001 0x08201000c0060700

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x0684000003000003 0x4068400000300000

def z582 : W := mkw 0xe13ffbfff7fb3cc0 0xfe13ffbfff7fb3cc 0xffffffffffff7ccf 0xfffffffffffff7cc

def z583 : W := mkw 0xd83ffffaaf00ea08 0xfd83ffffaaf00ea0 0xe7bedff03f00ff0b 0xde7bedff03f00ff0

def z584 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000004008f0a 0xc0000000004008f0

def z585 : W := mkw 0xb43fbeac98e0d0a4 0xfb43fbeac98e0d0a 0x82353cccf8607001 0x082353cccf860700

def z586 : W := mkw 0x482cb2c0270a2a08 0xa482cb2c0270a2a0 0x144ce3c0071f0f02 0x1144ce3c0071f0f0

def z587 : W := mkw 0x0000411200000000 0x0000041120000000 0x7d8ac33304008f0a 0xf7d8ac33304008f0

def z588 : W := mkw 0x5a2c57d22f04eb1a 0x85a2c57d22f04eb1 0xe7bedff03f8cff3b 0xde7bedff03f8cff3

def z589 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x0bb720003be30005 0xc0bb720003be3000

def z590 : W := mkw 0x0100415741313cc0 0x00100415741313cc 0xffcfe3ffc3737ccf 0x7ffcfe3ffc3737cc

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0x1841200000730004 0x0184120000073000

def z592 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebb31c3c38607001 0x2ebb31c3c3860700

def z593 : W := mkw 0x190016c54931fec8 0x0190016c54931fec 0xfec53fcfc373ffcf 0x7fec53fcfc373ffc

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0x08020030008000f4 0x208020030008000f

def z595 : W := mkw 0x482c12c027002a08 0x8482c12c027002a0 0x000400c003000000 0x0000400c00300000

def z596 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0xfbb3fc3fc0000000 0x2fbb3fc3fc000000

def z597 : W := mkw 0x783fb6c03fcaea08 0xe783fb6c03fcaea0 0x82353cc03b637001 0x082353cc03b63700

def z598 : W := mkw 0x14130c2c0820d0a4 0x514130c2c0820d0a 0xebb31c3c0000f0f8 0x2ebb31c3c0000f0f

def z599 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x82311c0c38e0f0fd 0xc82311c0c38e0f0f

def z600 : W := mkw 0x7c3f1ea83ec0c22c 0xd7c3f1ea83ec0c22 0x413a1f303c808330 0x8413a1f303c80833

def z601 : W := mkw 0x0000000000000000 0x0000000000000000 0x1842c000009c0004 0x01842c000009c000

def z602 : W := mkw 0x903fffba8800c000 0xf903fffba8800c00 0xffbffffff800f009 0xfffbffffff800f00

def z603 : W := mkw 0x1a0057d30914ef5a 0x01a0057d30914ef5 0xfdcadff3049cfffe 0xffdcadff3049cfff

def z604 : W := mkw 0x583fb6c02f00ea08 0xe583fb6c02f00ea0 0xffbfffc03f00ff0b 0xdffbfffc03f00ff0

def z605 : W := mkw 0x180016800800c208 0x0180016800800c20 0x40001f0000008300 0x040001f000000830

def z606 : W := mkw 0x2113a04551fb3cc0 0x62113a04551fb3cc 0xbec7e0cfc3ff7ccf 0x7bec7e0cfc3ff7cc

def z607 : W := mkw 0x0200411300140552 0x0020041130014055 0x1842c033049c8ffe 0xe1842c033049c8ff

def z608 : W := mkw 0x0000000000000000 0x0000000000000000 0xa280000000007009 0x4a28000000000700

def z609 : W := mkw 0xb43fffba98c0c024 0xfb43fffba98c0c02 0x413adf3038808030 0x8413adf303880803

def z610 : W := mkw 0x0200411200040112 0x0020041120004011 0x698ac330048c83fc 0xe698ac330048c83f

def z611 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0x9fbffcccc0000000 0x09fbffcccc000000

def z612 : W := mkw 0xe03fe93ab6ca0000 0xfe03fe93ab6ca000 0x1fffe03fffff0007 0xe1fffe03fffff000

def z613 : W := mkw 0x782c16c03fcaea08 0x8782c16c03fcaea0 0xe7fc1fc03fffff0f 0xde7fc1fc03fffff0

def z614 : W := mkw 0x2213411310d40552 0x42213411310d4055 0x7ffbc3333cfc8fff 0xf7ffbc3333cfc8ff

def z615 : W := mkw 0x74130c2c3eead0a4 0x574130c2c3eead0a 0xebf31c3c3ffff0ff 0xeebf31c3c3ffff0f

def z616 : W := mkw 0x34130c6c19e0f8a4 0x534130c6c19e0f8a 0xefb71cfc3be0fcff 0xfefb71cfc3be0fcf

def z617 : W := mkw 0x6000000036ca0000 0x06000000036ca000 0x000000003c8c0000 0x8000000003c8c000

def z618 : W := mkw 0x0000000400201080 0x0000000040020108 0xeb83003c00e0f0fd 0xeeb83003c00e0f0f

def z619 : W := mkw 0x0000000400201080 0x0000000040020108 0xa000000c000070c8 0x2a000000c000070c

def z620 : W := mkw 0x0000004001002800 0x0000000400100280 0xbec520c003737c0f 0x5bec520c003737c0

def z621 : W := mkw 0x592c16c56f31fec8 0x8592c16c56f31fec 0xe7fc1fc03f73ffcf 0xde7fc1fc03f73ffc

def z622 : W := mkw 0x0013493a00000000 0x50013493a0000000 0xffbbdf3f00000000 0x3ffbbdf3f0000000

def z623 : W := mkw 0xb63fffbf98f4d5f6 0xfb63fffbf98f4d5f 0xfffffffffcfcffff 0xffffffffffcfcfff

def z624 : W := mkw 0x0013082800000000 0x5001308280000000 0x82311c0c00000000 0x082311c0c0000000

def z625 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x197be0003cff0004 0x8197be0003cff000

def z626 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x1fffe00003730007 0x41fffe0000373000

def z627 : W := mkw 0x003fb28000000000 0xe003fb2800000000 0xffbfffc000000000 0x1ffbfffc00000000

def z628 : W := mkw 0x422ce113261e0552 0xa422ce113261e055 0x7dcee333079f8ffe 0xf7dcee333079f8ff

def z629 : W := mkw 0x482c12c027002a08 0x8482c12c027002a0 0xe7bc1fc007000f02 0x1e7bc1fc007000f0

def z630 : W := mkw 0x3013040018c0c000 0x43013040018c0c00 0xebb31c0038e0f00d 0xcebb31c0038e0f00

def z631 : W := mkw 0x803ffbfa81002800 0xf803ffbfa8100280 0xffbfffffc3007c0b 0x7ffbfffffc3007c0

def z632 : W := mkw 0x100004040820d080 0x0100004040820d08 0xebb11c0c3860f0cd 0xeebb11c0c3860f0c

def z633 : W := mkw 0xb43fffbe98e0d0a4 0xfb43fffbe98e0d0a 0xffbffffff8607001 0x3ffbffffff860700

def z634 : W := mkw 0x0200411300140552 0x0020041130014055 0x7dcac333009c00f4 0x37dcac333009c00f

def z635 : W := mkw 0x0200411300140552 0x0020041130014055 0x00000033000000f0 0x200000033000000f

def z636 : W := mkw 0x02004117003415d2 0x002004117003415d 0xffcbc33f04fcffff 0xfffcbc33f04fcfff

def z637 : W := mkw 0x0200411300140552 0x0020041130014055 0x554ac333049c8f32 0x9554ac333049c8f3

def z638 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0x5fffff303fff0007 0xc5fffff303fff000

def z639 : W := mkw 0x582c16802e00c208 0x8582c16802e00c20 0x47bc1f003f008303 0xc47bc1f003f00830

def z640 : W := mkw 0x402ca000260a0000 0xa402ca000260a000 0x1dcee000079f0006 0xc1dcee000079f000

def z641 : W := mkw 0x3500044559f1fce4 0x03500044559f1fce 0xbec520cffbf3fcff 0xfbec520cffbf3fcf

def z642 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x157ee0003f9f0002 0x8157ee0003f9f000

def z643 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0x00301c0000000000 0x000301c000000000

def z644 : W := mkw 0x6013000036ca0000 0x46013000036ca000 0x0bf300003fff0007 0xc0bf300003fff000

def z645 : W := mkw 0x0000411200000000 0x0000041120000000 0x410ac33000000000 0x0410ac3300000000

def z646 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x0bbbc0003cec0005 0xc0bbbc0003cec000

def z647 : W := mkw 0x783fa4403fcaea08 0xe783fa4403fcaea0 0x1fffe0003fffff0f 0xc1fffe0003fffff0

def z648 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xc3331c3c38e0f031 0x8c3331c3c38e0f03

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0x0982000000800004 0xc098200000080000

def z650 : W := mkw 0x0300415741353dd2 0x00300415741353dd 0xbec7e0ffc3ff7cff 0x7bec7e0ffc3ff7cf

def z651 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbcc000cfc0107cce 0x7bcc000cfc0107cc

def z652 : W := mkw 0x753fac6d7ffbfce4 0xf753fac6d7ffbfce 0xfffffcfffffffcff 0xffffffcfffffffcf

def z653 : W := mkw 0xb43fffbe98e0d0a4 0xfb43fffbe98e0d0a 0xebbbdf3c38e0f0fd 0xeebbbdf3c38e0f0f

def z654 : W := mkw 0x402c000026000000 0x8402c00002600000 0x023400003b000001 0x0023400003b00000

def z655 : W := mkw 0x0013082800000000 0x5001308280000000 0xebb31c3c008080fc 0xeebb31c3c008080f

def z656 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xa04000cfc3737ccf 0x7a04000cfc3737cc

def z657 : W := mkw 0x613fa04477eb3880 0xe613fa04477eb388 0x9fffe0ccffff7007 0xc9fffe0ccffff700

def z658 : W := mkw 0x0300415741353dd2 0x00300415741353dd 0xfec523ffc373ffff 0x7fec523ffc373fff

def z659 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xc33ffffcc0000000 0x0c33ffffcc000000

def z660 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x07bec0003f8c0003 0xc07bec0003f8c000

def z661 : W := mkw 0x0100000140110440 0x0010000014011044 0x10402003c0130000 0x010402003c013000

def z662 : W := mkw 0x3400040418e0d0a4 0x03400040418e0d0a 0x6982003038e0f0fd 0xe6982003038e0f0f

def z663 : W := mkw 0x7c3fbeec3feafaac 0xf7c3fbeec3feafaa 0xfffffffc3fffffff 0xffffffffc3ffffff

def z664 : W := mkw 0x943fffbe8820d0a4 0xf943fffbe8820d0a 0xffbfffffc000f0f8 0x3ffbfffffc000f0f

def z665 : W := mkw 0x0300415341152d52 0x00300415341152d5 0x7dcee3f3c79f8ffe 0xf7dcee3f3c79f8ff

def z666 : W := mkw 0x402c000026000000 0x8402c00002600000 0x013800003c000000 0x8013800003c00000

def z667 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x013ac00000000000 0x0013ac0000000000

def z668 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xaa8100cfc0607ccd 0x7aa8100cfc0607cc

def z669 : W := mkw 0x0000000000000000 0x0000000000000000 0x1801200fc0000000 0x21801200fc000000

def z670 : W := mkw 0x0100004441213880 0x0010000444121388 0xa68520ccc3637c0b 0x5a68520ccc3637c0

def z671 : W := mkw 0x402c000026000000 0x8402c00002600000 0x1ffd20003f730007 0xc1ffd20003f73000

def z672 : W := mkw 0x34130c2818c0c024 0x534130c2818c0c02 0x4bb31c3038e08035 0xc4bb31c3038e0803

def z673 : W := mkw 0x482c12c027002a08 0x8482c12c027002a0 0x07bc03c03f000f03 0xd07bc03c03f000f0

def z674 : W := mkw 0x0000000100100440 0x0000000010010044 0x7dc8030304108fce 0xf7dc8030304108fc

def z675 : W := mkw 0x0013000000000000 0x4001300000000000 0x0bb3000000000000 0x00bb300000000000

def z676 : W := mkw 0x583f1ee82f00ea08 0xd583f1ee82f00ea0 0xefbf1ffc3f00ff0b 0xfefbf1ffc3f00ff0

def z677 : W := mkw 0x35130c6c59e1f8a4 0x535130c6c59e1f8a 0xebb73cfcfbe3f0fd 0xeebb73cfcfbe3f0f

def z678 : W := mkw 0x8113e93fc03114c0 0x78113e93fc03114c 0x1843e03fc07300c4 0x21843e03fc07300c

def z679 : W := mkw 0x0000004001002800 0x0000000400100280 0x0000000003007c0b 0x40000000003007c0

def z680 : W := mkw 0x012c12c541313cc0 0x8012c12c541313cc 0xfffd3fcfc3737ccf 0x7fffd3fcfc3737cc

def z681 : W := mkw 0xd83fffbaae00c208 0xfd83fffbaae00c20 0x413adf303c008300 0x8413adf303c00830

def z682 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0xebb73cfcc0000000 0x2ebb73cfcc000000

def z683 : W := mkw 0x0000000000000000 0x0000000000000000 0xa68400c000000000 0x1a68400c00000000

def z684 : W := mkw 0x35130c6d59f1fce4 0x535130c6d59f1fce 0xbef53ccffb737ccf 0x7bef53ccffb737cc

def z685 : W := mkw 0x502c04002e00c000 0x8502c04002e00c00 0xe7bc1c003f00f00b 0xce7bc1c003f00f00

def z686 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0132000038800000 0x8013200003880000

def z687 : W := mkw 0x0013a00000000000 0x60013a0000000000 0x1803e00000000000 0x01803e0000000000

def z688 : W := mkw 0x0000000000000000 0x0000000000000000 0x140420c3c0000000 0x1140420c3c000000

def z689 : W := mkw 0x3400040418e0d0a4 0x03400040418e0d0a 0x0000000038607001 0x0000000003860700

def z690 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe3b11c0c3860f009 0xce3b11c0c3860f00

def z691 : W := mkw 0xb43fbeac98e0d0a4 0xfb43fbeac98e0d0a 0xebb73cfcf8e0f0fd 0xeebb73cfcf8e0f0f

def z692 : W := mkw 0x740004043eead0a4 0x0740004043eead0a 0x004000003ffff0ff 0xc004000003ffff0f

def z693 : W := mkw 0x0300415341152d52 0x00300415341152d5 0x144ce3c3c71f0f02 0x1144ce3c3c71f0f0

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c80000300000000 0x33c8000030000000

def z695 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x1fffe000049c0006 0xc1fffe000049c000

def z696 : W := mkw 0x0000000100100440 0x0000000010010044 0x1440000300100c02 0x11440000300100c0

def z697 : W := mkw 0x35130c6c59e1f8a4 0x535130c6c59e1f8a 0x82353cccfb637001 0x082353cccfb63700

def z698 : W := mkw 0x482c12c027002a08 0x8482c12c027002a0 0x658c03c007008f0a 0xd658c03c007008f0

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d8ac00000000000 0x01d8ac0000000000

def z700 : W := mkw 0x402ca000260a0000 0xa402ca000260a000 0x0008c000040c0000 0x00008c000040c000

def z701 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x49331c3c38e080f4 0xa49331c3c38e080f

def z702 : W := mkw 0x0100004441213880 0x0010000444121388 0x9ec520ccc3737007 0x49ec520ccc373700

def z703 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x82341cc03f00ff0b 0xc82341cc03f00ff0

def z704 : W := mkw 0x2213e11310de0552 0x62213e11310de055 0x7dcbe33304ff8ffe 0xf7dcbe33304ff8ff

def z705 : W := mkw 0x582c16802e00c208 0x8582c16802e00c20 0x65b81f003c008f0a 0xd65b81f003c008f0

def z706 : W := mkw 0x7c3f1eac3ee0d2ac 0xd7c3f1eac3ee0d2a 0xebbb1f3c3ce0f3fd 0xeebbb1f3c3ce0f3f

def z707 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x037fe0003fff0007 0xc037fe0003fff000

def z708 : W := mkw 0x35130c2c58e1d0a4 0x535130c2c58e1d0a 0xebb33c3cf8e3f0fd 0xeebb33c3cf8e3f0f

def z709 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xffbd3fc03f00ff0b 0xdffbd3fc03f00ff0

def z710 : W := mkw 0x603fa82836ca0000 0xf603fa82836ca000 0xfffffcffffff0007 0xffffffcffffff000

def z711 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xfec53fffc3730007 0x7fec53fffc373000

def z712 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbe8520cfc3637cc9 0x3be8520cfc3637cc

def z713 : W := mkw 0xa03ffbba90c00000 0xfa03ffbba90c0000 0xffbffffff8e080fd 0xfffbffffff8e080f

def z714 : W := mkw 0x802cfbba80000000 0xb802cfbba8000000 0xf7bcffffc0000000 0x3f7bcffffc000000

def z715 : W := mkw 0x0200411300140552 0x0020041130014055 0x410ac330048c8ff8 0x8410ac330048c8ff

def z716 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xe2353ffffb630001 0x3e2353ffffb63000

def z717 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xfff53ccfc3737ccf 0x7fff53ccfc3737cc

def z718 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bd3fccff00ff0b 0xde7bd3fccff00ff0

def z719 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe6b41fc03b00ff0b 0x5e6b41fc03b00ff0

def z720 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffffffffff7f0003 0x3ffffffffff7f000

def z721 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbe1ff03f00ff0b 0xfefbe1ff03f00ff0

def z722 : W := mkw 0x80005bba80000000 0x180005bba8000000 0x80001fcfc0000000 0x180001fcfc000000

def z723 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xf408dfffc0000000 0x3f408dfffc000000

def z724 : W := mkw 0x3400040418e0d0a4 0x03400040418e0d0a 0xebb21c3038e0f0fd 0xeebb21c3038e0f0f

def z725 : W := mkw 0x683fb28036ca0208 0xe683fb28036ca020 0x1fffe3003fff0307 0xc1fffe3003fff030

def z726 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xea331c3c38e0f0fd 0x2ea331c3c38e0f0f

def z727 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffffffffffff8f0f 0xfffffffffffff8f0

def z728 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xfbf3dc3c38fcf0fd 0xefbf3dc3c38fcf0f

def z729 : W := mkw 0x623fe11336de0552 0xe623fe11336de055 0x623523333b638ff9 0x3623523333b638ff

def z730 : W := mkw 0x0300415641253992 0x0030041564125399 0xc30fe3fcc7eff331 0x8c30fe3fcc7eff33

def z731 : W := mkw 0x002c539200000000 0x8002c53920000000 0xffbfffffc0000000 0x3ffbfffffc000000

def z732 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xebb73fffc0000000 0x3ebb73fffc000000

def z733 : W := mkw 0x6000000036ca0000 0x06000000036ca000 0x1842c0003fff0007 0xc1842c0003fff000

def z734 : W := mkw 0x0200411300140552 0x0020041130014055 0x7fcbc33304fc8fff 0xf7fcbc33304fc8ff

def z735 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffffffffc0100006 0x7ffffffffc010000

def z736 : W := mkw 0xc03ffbbaa6000000 0xfc03ffbbaa600000 0xffbfffffff008f0b 0xfffbfffffff008f0

def z737 : W := mkw 0x823fbaa980140552 0xf823fbaa98014055 0x82753cccc49c8ffe 0xc82753cccc49c8ff

def z738 : W := mkw 0x0000128000000000 0x0000012800000000 0xfe853fcfc0000000 0x3fe853fcfc000000

def z739 : W := mkw 0xa03ffbba90ca0000 0xfa03ffbba90ca000 0xfffffffff8ff0005 0xffffffffff8ff000

def z740 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0xbfffe0003fff700f 0xcbfffe0003fff700

def z741 : W := mkw 0x603fa82836ca0000 0xf603fa82836ca000 0x5ffffc303fff0007 0xc5ffffc303fff000

def z742 : W := mkw 0x80135bba80000000 0x580135bba8000000 0xe8031fffc0000000 0x3e8031fffc000000

def z743 : W := mkw 0x603fb28036ca0000 0xe603fb28036ca000 0x1fffe3c03fff0007 0xd1fffe3c03fff000

def z744 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebb31c3c38e070f5 0x2ebb31c3c38e070f

def z745 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xe0001fffc0008f08 0x3e0001fffc0008f0

def z746 : W := mkw 0x793fa4457ffbfec8 0xe793fa4457ffbfec 0x1fffe0003fffffcf 0xc1fffe0003fffffc

def z747 : W := mkw 0x0000004001002800 0x0000000400100280 0xbec520cfc3737c0f 0x7bec520cfc3737c0

def z748 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffbfffffff8c0003 0xfffbfffffff8c000

def z749 : W := mkw 0x603fb28036ca0000 0xe603fb28036ca000 0xffffffcfffff0007 0xfffffffcfffff000

def z750 : W := mkw 0x34130c2818c0c024 0x534130c2818c0c02 0xebb21c303880f0fd 0xeebb21c303880f0f

def z751 : W := mkw 0x35130c6959d1ec64 0x535130c6959d1ec6 0x55763cf3fb938c32 0x955763cf3fb938c3

def z752 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebf31c3c3cfcf0ff 0xeebf31c3c3cfcf0f

def z753 : W := mkw 0x80001aa880000000 0x180001aa88000000 0xbe853ccfc0000000 0x3be853ccfc000000

def z754 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x820520cfc36370c1 0x2820520cfc36370c

def z755 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7fc1fc03f9cff0f 0xde7fc1fc03f9cff0

def z756 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x4bb31c3038e0f0fd 0xc4bb31c3038e0f0f

def z757 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xfff31c3c38f0f0ff 0xefff31c3c38f0f0f

def z758 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xe33fffffc0000000 0x3e33fffffc000000

def z759 : W := mkw 0x803ffbba800a0000 0xf803ffbba800a000 0xffffffffc01f0000 0x3ffffffffc01f000

def z760 : W := mkw 0x80135bba80000000 0x580135bba8000000 0xe1321fffc0000000 0x3e1321fffc000000

def z761 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xffcd23cfc3737ccf 0x7ffcd23cfc3737cc

def z762 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe3b11c3c3860f0f9 0xee3b11c3c3860f0f

def z763 : W := mkw 0x0300004541353dd2 0x00300004541353dd 0xbec520cfc77f7fcf 0x7bec520cfc77f7fc

def z764 : W := mkw 0xc03ffbbaa60a0000 0xfc03ffbbaa60a000 0xffffffffc79f0006 0xfffffffffc79f000

def z765 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc3630001 0x3ffbfffffc363000

def z766 : W := mkw 0x402ca000260a0000 0xa402ca000260a000 0x1ffde0003f7f0007 0xc1ffde0003f7f000

def z767 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xffbbdc3c38e0f0fd 0xeffbbdc3c38e0f0f

def z768 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xaa8520cfc3637ccd 0x7aa8520cfc3637cc

def z769 : W := mkw 0x0200411300140552 0x0020041130014055 0x5dcac330049c8ffe 0xc5dcac330049c8ff

def z770 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xfffc1fc03f10ff0f 0xdfffc1fc03f10ff0

def z771 : W := mkw 0xe03fbaa8b6ca0000 0xfe03fbaa8b6ca000 0xbffffccfffff0007 0xfbffffccfffff000

def z772 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc4000002 0xfffbfffffc400000

def z773 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x69b21c3038e0f0fd 0xe69b21c3038e0f0f

def z774 : W := mkw 0x542cac2c2e2ad0a4 0xb542cac2c2e2ad0a 0xf44cfc3c071ff0fa 0x2f44cfc3c071ff0f

def z775 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xffbc1fc33f00ff0b 0xfffbc1fc33f00ff0

def z776 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1ff03f00fffb 0xfe7bc1ff03f00fff

def z777 : W := mkw 0x4a2cf3d3271e2f5a 0xa4a2cf3d3271e2f5 0x144ce3c3071f0f02 0x1144ce3c3071f0f0

def z778 : W := mkw 0xf43fffbabecac024 0xff43fffbabecac02 0x413adf303c8c8030 0x8413adf303c8c803

def z779 : W := mkw 0x3013040018c0c000 0x43013040018c0c00 0xebb31c3038e0f0fd 0xeebb31c3038e0f0f

def z780 : W := mkw 0x402c128026000000 0x8402c12802600000 0xfffd3fcfff730007 0xffffd3fcfff73000

def z781 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fcfff00ff0b 0xfe7bc1fcfff00ff0

def z782 : W := mkw 0x0300004541353dd2 0x00300004541353dd 0xbec520cfc373ffff 0x7bec520cfc373fff

def z783 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffffffffc7ff0006 0x3ffffffffc7ff000

def z784 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbecd23cfc7737fcf 0x7becd23cfc7737fc

def z785 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1bf7e0003bff0005 0xc1bf7e0003bff000

def z786 : W := mkw 0x603fbaa836ca0000 0xf603fbaa836ca000 0xfffffffc3fff0007 0xffffffffc3fff000

def z787 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebb31c3c3ce0ffff 0xeebb31c3c3ce0fff

def z788 : W := mkw 0x110004454931fcc0 0x0110004454931fcc 0x004000003b73fccf 0xc004000003b73fcc

def z789 : W := mkw 0xd813ed7aaf00ea08 0x7d813ed7aaf00ea0 0x1803e03fff00ff0b 0xe1803e03fff00ff0

def z790 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7be1ff03f80ff3b 0xde7be1ff03f80ff3

def z791 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1fffe0003fff8f0f 0xc1fffe0003fff8f0

def z792 : W := mkw 0x592c16856e31d6c8 0x8592c16856e31d6c 0x59793f0ffc7383c4 0xa59793f0ffc7383c

def z793 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xffb73c3c38e0f0fd 0xeffb73c3c38e0f0f

def z794 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x87bc1fc03f007f03 0xd87bc1fc03f007f0

def z795 : W := mkw 0xa03ffbba90c00000 0xfa03ffbba90c0000 0xffbffffff8800000 0xbffbffffff880000

def z796 : W := mkw 0xc03ffbbaa6000000 0xfc03ffbbaa600000 0xffffffffff730007 0xfffffffffff73000

def z797 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xe9821fffc0000000 0x3e9821fffc000000

def z798 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0x9ffffcffffff0007 0xe9ffffcffffff000

def z799 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0xffbd3fcfc0000000 0x3ffbd3fcfc000000

def z800 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1ff7e0003bff0007 0xc1ff7e0003bff000

def z801 : W := mkw 0x190004454931fec8 0x0190004454931fec 0x004000000373ffcf 0x4004000000373ffc

def z802 : W := mkw 0x0200411300140552 0x0020041130014055 0xffcbc33f049c8ffe 0xfffcbc33f049c8ff

def z803 : W := mkw 0x0100004441213880 0x0010000444121388 0xbe8520cfc3637c0b 0x7be8520cfc3637c0

def z804 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffbffffff8000000 0x3ffbffffff800000

def z805 : W := mkw 0x4b2c53d367152f5a 0x84b2c53d367152f5 0x144ce3c3c71f0f02 0x1144ce3c3c71f0f0

def z806 : W := mkw 0x0200411300140552 0x0020041130014055 0xffcfe3ffc7ff8fff 0xfffcfe3ffc7ff8ff

def z807 : W := mkw 0x0200411300140552 0x0020041130014055 0x594ac333049c8ffe 0xe594ac333049c8ff

def z808 : W := mkw 0x0100004441213880 0x0010000444121388 0xa20520cfc3637001 0x3a20520cfc363700

def z809 : W := mkw 0x150004454931fce4 0x0150004454931fce 0x000000000000fcf8 0x0000000000000fcf

def z810 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1fffe0003bff0005 0x01fffe0003bff000

def z811 : W := mkw 0xe0005bbab6ca0000 0x1e0005bbab6ca000 0xe0401fffffff0007 0xfe0401fffffff000

def z812 : W := mkw 0x602ca00036ca0000 0xa602ca00036ca000 0x1ecde0003fff0007 0xc1ecde0003fff000

def z813 : W := mkw 0x5a2c57d32f14ef5a 0x85a2c57d32f14ef5 0x9a76dcf33b9c70f5 0x29a76dcf33b9c70f

def z814 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebb73cfcf8e0f0fd 0xeebb73cfcf8e0f0f

def z815 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xf7fcdfc03f1cff0b 0xdf7fcdfc03f1cff0

def z816 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x924520cfc3737001 0x0924520cfc373700

def z817 : W := mkw 0x823ffbba80040112 0xf823ffbba8004011 0xffbfffffc48c83fc 0xfffbfffffc48c83f

def z818 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xe10adfffc0000000 0x3e10adfffc000000

def z819 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbd1fcc3f00ff0b 0xfefbd1fcc3f00ff0

def z820 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1c4fe0003fff0007 0xc1c4fe0003fff000

def z821 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe3b81f003f00ff0b 0xce3b81f003f00ff0

def z822 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x863c1fc03f00ff0b 0xd863c1fc03f00ff0

def z823 : W := mkw 0x0200411300140552 0x0020041130014055 0x7fcfe333049c8ffe 0xf7fcfe333049c8ff

def z824 : W := mkw 0x613fa04577fb3cc0 0xe613fa04577fb3cc 0xa13ac0cffc8c7cc8 0xba13ac0cffc8c7cc

def z825 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc00080f8 0x3ffbfffffc00080f

def z826 : W := mkw 0x602c000036ca0000 0x8602c000036ca000 0x1ffec0003fff0007 0xc1ffec0003fff000

def z827 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x7fffe0303fff0007 0xe7fffe0303fff000

def z828 : W := mkw 0x100004400900e800 0x0100004400900e80 0xe7bc1fc03f00ff0b 0xde7bc1fc03f00ff0

def z829 : W := mkw 0x6013a00036ca0000 0x66013a00036ca000 0x1ec7e0003fff0007 0xc1ec7e0003fff000

def z830 : W := mkw 0x120045130814c552 0x0120045130814c55 0xfbf2dc33389cf0fd 0xefbf2dc33389cf0f

def z831 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0xbfbffccfc0000000 0x3bfbffccfc000000

def z832 : W := mkw 0xe03fbaa8b6ca0000 0xfe03fbaa8b6ca000 0xffffffccffff0007 0xdffffffccffff000

def z833 : W := mkw 0x582cb6c02f0aea08 0xa582cb6c02f0aea0 0xfffeffc03f9fff0f 0xdfffeffc03f9fff0

def z834 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x41381f003c00ff08 0x841381f003c00ff0

def z835 : W := mkw 0x1b0057d74935ffda 0x01b0057d74935ffd 0xe0001fffc000fff8 0x3e0001fffc000fff

def z836 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xfbf33c3c38f3f0fd 0xefbf33c3c38f3f0f

def z837 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe3331c3c38e0f0f9 0xae3331c3c38e0f0f

def z838 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbec520cfc3737c03 0x3bec520cfc3737c0

def z839 : W := mkw 0x80135bba80000000 0x580135bba8000000 0xffb73fffc0000000 0x3ffb73fffc000000

def z840 : W := mkw 0x823ffbba80040112 0xf823ffbba8004011 0xffbfffffc0008330 0x3ffbfffffc000833

def z841 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebbbdc3c3cecf0fd 0xeebbbdc3c3cecf0f

def z842 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1a77e0003fff0007 0xc1a77e0003fff000

def z843 : W := mkw 0xc02c5bbaa6000000 0x9c02c5bbaa600000 0xe7bc1fffff000003 0xfe7bc1fffff00000

def z844 : W := mkw 0xa43ffbba90c00024 0xfa43ffbba90c0002 0xffbfffffc0800030 0x3ffbfffffc080003

def z845 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe0301c3c3800f0f8 0x2e0301c3c3800f0f

def z846 : W := mkw 0x0200411300140552 0x0020041130014055 0x7ffac3333c9c8fff 0xf7ffac3333c9c8ff

def z847 : W := mkw 0x482c12c027002a08 0x8482c12c027002a0 0x6d8e03f007808ffe 0xf6d8e03f007808ff

def z848 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe3b41fc03b00ff09 0xde3b41fc03b00ff0

def z849 : W := mkw 0x36134d3f18f4d5f6 0x536134d3f18f4d5f 0x9679df0f3c7c7f03 0x19679df0f3c7c7f0

def z850 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xffffffc03fffff0f 0xdffffffc03fffff0

def z851 : W := mkw 0xb413ac2c98e0d0a4 0x7b413ac2c98e0d0a 0xebb33c3cf8e0f0fd 0xeebb33c3cf8e0f0f

def z852 : W := mkw 0x0000000000000000 0x0000000000000000 0xffb53ccfc0000000 0x3ffb53ccfc000000

def z853 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0x9a353ccfc0000000 0x29a353ccfc000000

def z854 : W := mkw 0x0200411300140552 0x0020041130014055 0x7fcec333079c8fff 0xf7fcec333079c8ff

def z855 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x9a4520cfc3737ccf 0x69a4520cfc3737cc

def z856 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xfdbadfffc0000000 0x3fdbadfffc000000

def z857 : W := mkw 0x0200411200040112 0x0020041120004011 0x6d8ac330048c8ffe 0xf6d8ac330048c8ff

def z858 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1fffe3003fff0f07 0xd1fffe3003fff0f0

def z859 : W := mkw 0x813ffbffc1313cc0 0xf813ffbffc1313cc 0x417adf3003737ccf 0x4417adf3003737cc

def z860 : W := mkw 0x3413ac2c18ead0a4 0x73413ac2c18ead0a 0xfff7fc3c3bfff0ff 0xefff7fc3c3bfff0f

def z861 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1e7fe0003fff0007 0x01e7fe0003fff000

def z862 : W := mkw 0x0200411300140552 0x0020041130014055 0x554ac333049c8ffe 0xd554ac333049c8ff

def z863 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xf8013fffc0000000 0x3f8013fffc000000

def z864 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xefbb1c3c3ce0f0ff 0xeefbb1c3c3ce0f0f

def z865 : W := mkw 0x8013fbba80000000 0x78013fbba8000000 0xe0013fffc0000000 0x3e0013fffc000000

def z866 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xaab31c3c38e070fd 0x6aab31c3c38e070f

def z867 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbfcd20cfc7737ccf 0xfbfcd20cfc7737cc

def z868 : W := mkw 0x34130c2c18ead0a4 0x534130c2c18ead0a 0xebf31c3c38fff0fd 0xeebf31c3c38fff0f

def z869 : W := mkw 0x590004456f31fec8 0x0590004456f31fec 0x004000003b737ccf 0x4004000003b737cc

def z870 : W := mkw 0x14130c2c0820d0a4 0x514130c2c0820d0a 0xebb31c3c3800f0f9 0xeebb31c3c3800f0f

def z871 : W := mkw 0xa03ffbba90ca0000 0xfa03ffbba90ca000 0xffffffffc3ff0007 0x7ffffffffc3ff000

def z872 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbfcfe0cfc3737ccf 0x7bfcfe0cfc3737cc

def z873 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0xffb7fcffc0000000 0x3ffb7fcffc000000

def z874 : W := mkw 0x3813b6c019caea08 0x63813b6c019caea0 0xf843ffc000ffff0c 0x1f843ffc000ffff0

def z875 : W := mkw 0xb42cf79698e0d0a4 0xab42cf79698e0d0a 0x140ce3c3f8e0f0fd 0xd140ce3c3f8e0f0f

def z876 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc0600005 0x7ffbfffffc060000

def z877 : W := mkw 0x6013a00036ca0000 0x66013a00036ca000 0x0042c0003fff0007 0xc0042c0003fff000

def z878 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x9fbfffcfc0000000 0x19fbfffcfc000000

def z879 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x820520cfc3637c01 0x1820520cfc3637c0

def z880 : W := mkw 0x80005bba80000000 0x180005bba8000000 0x80001cffc0000000 0x280001cffc000000

def z881 : W := mkw 0xa03ffbba90ca0000 0xfa03ffbba90ca000 0xffbfffffc0630000 0x3ffbfffffc063000

def z882 : W := mkw 0x14000c2c0820d0a4 0x114000c2c0820d0a 0xe1301c3c3800f0f8 0xae1301c3c3800f0f

def z883 : W := mkw 0xc83ffbbaa6000208 0xfc83ffbbaa600020 0xffbfffffc4000300 0x3ffbfffffc400030

def z884 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xf7fc3fc03f13ff0b 0xdf7fc3fc03f13ff0

def z885 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbec720ffc3f37cff 0x7bec720ffc3f37cf

def z886 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xff8fffffc0000000 0x3ff8fffffc000000

def z887 : W := mkw 0x753fa4457ffbfce4 0xe753fa4457ffbfce 0x1fffe0003ffffcff 0xc1fffe0003ffffcf

def z888 : W := mkw 0xc03ffbbaa6000000 0xfc03ffbbaa600000 0xffffffffff9c0007 0xfffffffffff9c000

def z889 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1275e0003b7f0001 0x01275e0003b7f000

def z890 : W := mkw 0x80135bba80000000 0x580135bba8000000 0xe2311fffc0000000 0x3e2311fffc000000

def z891 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc0008f08 0x3ffbfffffc0008f0

def z892 : W := mkw 0x0300004541353dd2 0x00300004541353dd 0xbfcfe0cfc7ffffff 0xfbfcfe0cfc7fffff

def z893 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc0808030 0xbffbfffffc080803

def z894 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1d7fe0003fff0006 0x81d7fe0003fff000

def z895 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffffffffff9f0002 0xbffffffffff9f000

def z896 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x5d3fffffc0000000 0x35d3fffffc000000

def z897 : W := mkw 0xc03ffbbaa6000000 0xfc03ffbbaa600000 0xffbffffffc000000 0xbffbffffffc00000

def z898 : W := mkw 0x603fb28036ca0000 0xe603fb28036ca000 0x5fffff003fff0007 0xc5fffff003fff000

def z899 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffffffffffff80ff 0xfffffffffffff80f

def z900 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1fffe0303fff00f7 0xe1fffe0303fff00f

def z901 : W := mkw 0x603fa82836ca0000 0xf603fa82836ca000 0x9ffffc0c3fff0007 0xc9ffffc0c3fff000

def z902 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xba4520cfc3737ccd 0x3ba4520cfc3737cc

def z903 : W := mkw 0x6c3f1aec37e03aac 0xd6c3f1aec37e03aa 0x0c0f03fc07e00ff6 0x30c0f03fc07e00ff

def z904 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x47bc1f003f00ff0b 0xc47bc1f003f00ff0

def z905 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0xbfffe00c3fff0007 0xebfffe00c3fff000

def z906 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xffc720ffc3737ccf 0x7ffc720ffc3737cc

def z907 : W := mkw 0x582cb6c02f00ea08 0xa582cb6c02f00ea0 0xf7bcffc03f00ff0b 0xdf7bcffc03f00ff0

def z908 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xfffd3fcfff73ff0f 0xffffd3fcfff73ff0

def z909 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x3fffe0003fff00cf 0xe3fffe0003fff00c

def z910 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebb31c3c3880f0f8 0xaebb31c3c3880f0f

def z911 : W := mkw 0xe23ffbbab6ce0112 0xfe23ffbbab6ce011 0xffffffffffff8337 0xfffffffffffff833

def z912 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xea811fffc0000000 0x3ea811fffc000000

def z913 : W := mkw 0x602ca00036ca0000 0xa602ca00036ca000 0x1dcee0003fff0007 0xc1dcee0003fff000

def z914 : W := mkw 0x0200411300140552 0x0020041130014055 0xffcec3f3049c8ffe 0xfffcec3f3049c8ff

def z915 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0xbfffe0c03fff0007 0xdbfffe0c03fff000

def z916 : W := mkw 0xe03fa828b6ca0000 0xfe03fa828b6ca000 0x1fffe00cffff0007 0xc1fffe00cffff000

def z917 : W := mkw 0x582c16c02f0aea08 0x8582c16c02f0aea0 0xe7fc1fc03f1fff0b 0xde7fc1fc03f1fff0

def z918 : W := mkw 0x003f1aa800000000 0xd003f1aa80000000 0xffbf3fffc0000000 0x3ffbf3fffc000000

def z919 : W := mkw 0x590004456f31fec8 0x0590004456f31fec 0x000000003f00ffcb 0xc000000003f00ffc

def z920 : W := mkw 0x603fb28036ca0000 0xe603fb28036ca000 0xffffffc03fff8f0f 0xdffffffc03fff8f0

def z921 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbfc720cfc3f37ccf 0xfbfc720cfc3f37cc

def z922 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbec520cfc3f3fcff 0xfbec520cfc3f3fcf

def z923 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xfffffffffc9c0006 0xffffffffffc9c000

def z924 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x17fde0003f7f0003 0xc17fde0003f7f000

def z925 : W := mkw 0x802cfbba80000000 0xb802cfbba8000000 0xe0043fffc0000000 0x3e0043fffc000000

def z926 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbd1fc03f60ff0f 0xdefbd1fc03f60ff0

def z927 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x3fffe0003fff0c0f 0xd3fffe0003fff0c0

def z928 : W := mkw 0x3700044559f5fdf6 0x03700044559f5fdf 0x004000003fffffff 0xc004000003ffffff

def z929 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xfbb33c3ff8e0f0fd 0xefbb33c3ff8e0f0f

def z930 : W := mkw 0xa013fbba90ca0000 0x7a013fbba90ca000 0xf843ffffc0ff0004 0x3f843ffffc0ff000

def z931 : W := mkw 0x180016c00900ea08 0x0180016c00900ea0 0xe7b41fc03b00ff0b 0xde7b41fc03b00ff0

def z932 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xffcf23ffc7f3ffff 0xfffcf23ffc7f3fff

def z933 : W := mkw 0x602ca00036ca0000 0xa602ca00036ca000 0x0048c0003fff0007 0xc0048c0003fff000

def z934 : W := mkw 0x8013fbba80000000 0x78013fbba8000000 0xfbb3ffffc0000000 0x3fbb3ffffc000000

def z935 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xe3b01fffc0000000 0x3e3b01fffc000000

def z936 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xc73c1fc03f00ff03 0x9c73c1fc03f00ff0

def z937 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe1321c3c38e0f0fd 0xee1321c3c38e0f0f

def z938 : W := mkw 0x3513044559f1fce4 0x43513044559f1fce 0x1ff720003bf3fcff 0xc1ff720003bf3fcf

def z939 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffffffffc0730004 0x3ffffffffc073000

def z940 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xfec523cfc373ffcf 0x7fec523cfc373ffc

def z941 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x9fffe0ccffff0007 0xc9fffe0ccffff000

def z942 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffffffffc49c80fe 0xfffffffffc49c80f

def z943 : W := mkw 0x0200411300140552 0x0020041130014055 0x794ac333049c8ffc 0xb794ac333049c8ff

def z944 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe3b81fc03c00ff09 0xde3b81fc03c00ff0

def z945 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x82311c3c386070f1 0x282311c3c386070f

def z946 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe2341fc03f00ff0b 0xde2341fc03f00ff0

def z947 : W := mkw 0x582cb6c02f0aea08 0xa582cb6c02f0aea0 0xe7bcdfc03f0cff0b 0xde7bcdfc03f0cff0

def z948 : W := mkw 0x2013082810c00000 0x52013082810c0000 0xfff73cfffbf30007 0xffff73cfffbf3000

def z949 : W := mkw 0xe03fbaa8b6ca0000 0xfe03fbaa8b6ca000 0x1ffffc003fff0007 0xc1ffffc003fff000

def z950 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x964520cfc3737ccf 0x5964520cfc3737cc

def z951 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xfffffffffbff0005 0x3fffffffffbff000

def z952 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xf4043fffc0000000 0x3f4043fffc000000

def z953 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0x9fffffcfffff0007 0xd9fffffcfffff000

def z954 : W := mkw 0x803f5bba80000000 0xd803f5bba8000000 0xefbf1fffc0000000 0x3efbf1fffc000000

def z955 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xfa37ffffc0000000 0x3fa37ffffc000000

def z956 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xbebdffcfc0000000 0x3bebdffcfc000000

def z957 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03c00ff08 0x9e7bc1fc03c00ff0

def z958 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xe13adffffc8c0000 0xbe13adffffc8c000

def z959 : W := mkw 0x802c5bba80000000 0x9802c5bba8000000 0xe2341fffc0000000 0x3e2341fffc000000

def z960 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xfff73cfffbf3f0ff 0xffff73cfffbf3f0f

def z961 : W := mkw 0x0000082800000000 0x1000008280000000 0xe0001cffc0000000 0x3e0001cffc000000

def z962 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc4808ffe 0xfffbfffffc4808ff

def z963 : W := mkw 0x0200411300140552 0x0020041130014055 0x614ac333049c8ffe 0xf614ac333049c8ff

def z964 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc0000c0a 0x7ffbfffffc0000c0

def z965 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1b7fe0003fff0005 0x81b7fe0003fff000

def z966 : W := mkw 0x823ffbba80040112 0xf823ffbba8004011 0xffffffffc49c8336 0xfffffffffc49c833

def z967 : W := mkw 0xa0135bba90c00000 0x5a0135bba90c0000 0xebb31ffff8e00005 0xfebb31ffff8e0000

def z968 : W := mkw 0x0013493a00000000 0x50013493a0000000 0xffbfffffc0000000 0x3ffbfffffc000000

def z969 : W := mkw 0x0200411300140552 0x0020041130014055 0x754ac333049c8ffa 0xb754ac333049c8ff

def z970 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffffffffc7ff0007 0xfffffffffc7ff000

def z971 : W := mkw 0x643fa82836ca0024 0xf643fa82836ca002 0x1fffe0303fff0037 0xc1fffe0303fff003

def z972 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbec520cfc773ffcf 0xfbec520cfc773ffc

def z973 : W := mkw 0xa03ffbba90ca0000 0xfa03ffbba90ca000 0xffbfffffc08c0000 0x3ffbfffffc08c000

def z974 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc0008008 0xfffbfffffc000800

def z975 : W := mkw 0xc03ffbbaa60a0000 0xfc03ffbbaa60a000 0xffffffffc77f0007 0x7ffffffffc77f000

def z976 : W := mkw 0x14000c2c0820d0a4 0x114000c2c0820d0a 0xe2301c3c3800f0f9 0x2e2301c3c3800f0f

def z977 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xfffbdf3c3cfcffff 0xffffbdf3c3cfcfff

def z978 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0x9a77fcfffbff0005 0x29a77fcfffbff000

def z979 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe1381fc03f00ff0b 0xde1381fc03f00ff0

def z980 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xfec520ffc373fcff 0x7fec520ffc373fcf

def z981 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc08000f4 0x3ffbfffffc08000f

def z982 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xdb3fffffc0000000 0x2db3fffffc000000

def z983 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xa68520cfc3637ccb 0x7a68520cfc3637cc

def z984 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbffffff8000001 0xfffbffffff800000

def z985 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x5fffe3003fff8307 0xc5fffe3003fff830

def z986 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe53c1fc03f00ff0a 0x9e53c1fc03f00ff0

def z987 : W := mkw 0x0200411300140552 0x0020041130014055 0x7dcac33307ff8fff 0xf7dcac33307ff8ff

def z988 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xf93bffffc0000000 0x3f93bffffc000000

def z989 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebb31c3c3860f0f9 0x2ebb31c3c3860f0f

def z990 : W := mkw 0x802c5bba80000000 0x9802c5bba8000000 0xe1381fffc0000000 0x3e1381fffc000000

def z991 : W := mkw 0xa03ffbba90c00000 0xfa03ffbba90c0000 0xffbffffff8600001 0x3ffbffffff860000

def z992 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xcb331c3c38e0f0f5 0xacb331c3c38e0f0f

def z993 : W := mkw 0x2613e93f10fe15f6 0x72613e93f10fe15f 0x1843e03f00ff00f4 0x21843e03f00ff00f

def z994 : W := mkw 0x0200411300140552 0x0020041130014055 0xfdcac3ffc49c8ffe 0xffdcac3ffc49c8ff

def z995 : W := mkw 0x0000128000000000 0x0000012800000000 0xe0001fcfc0000000 0x3e0001fcfc000000

def z996 : W := mkw 0x0013082800000000 0x5001308280000000 0xbeb53ccfc0000000 0x3beb53ccfc000000

def z997 : W := mkw 0xa03ffbba90ca0000 0xfa03ffbba90ca000 0xffffffffc4ff0006 0xfffffffffc4ff000

def z998 : W := mkw 0xe03ffbbab6c00000 0xfe03ffbbab6c0000 0xffbfffffffe00007 0xfffbfffffffe0000

def z999 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbecde0cfc77f7ccf 0x7becde0cfc77f7cc

def z1000 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x1c4520cfc3737ccf 0x71c4520cfc3737cc

def z1001 : W := mkw 0x0300411340150552 0x0030041134015055 0x7dcae333c49f8ffe 0xf7dcae333c49f8ff

def z1002 : W := mkw 0x0200411300140552 0x0020041130014055 0x69cac330049c8ffe 0xe69cac330049c8ff

def z1003 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xf802dfffc0000000 0x3f802dfffc000000

def z1004 : W := mkw 0x823ffbba80040112 0xf823ffbba8004011 0xffbfffffc40c0300 0x3ffbfffffc40c030

def z1005 : W := mkw 0x8013fbba80000000 0x78013fbba8000000 0xe002dfffc0000000 0x3e002dfffc000000

def z1006 : W := mkw 0x8013fbba80000000 0x78013fbba8000000 0xfe87ffffc0000000 0x3fe87ffffc000000

def z1007 : W := mkw 0x180016c00900ea08 0x0180016c00900ea0 0xe1301fc03800ff08 0x9e1301fc03800ff0

def z1008 : W := mkw 0xd82cb6c0af00ea08 0xad82cb6c0af00ea0 0xe7bc3fc0ff00ff0b 0xde7bc3fc0ff00ff0

def z1009 : W := mkw 0x6000000036ca0000 0x06000000036ca000 0x1448c0003fff0007 0xc1448c0003fff000

def z1010 : W := mkw 0x100004000800c000 0x0100004000800c00 0xe3b01c303800f0f9 0xee3b01c303800f0f

def z1011 : W := mkw 0x0000000400201080 0x0000000040020108 0xbec520cfc37370cf 0x7bec520cfc37370c

def z1012 : W := mkw 0x582cb6c02f0aea08 0xa582cb6c02f0aea0 0xe7bc3fc03f03ff0b 0xde7bc3fc03f03ff0

def z1013 : W := mkw 0x7d0004457ff1feec 0x07d0004457ff1fee 0x004000003ff3ffff 0xc004000003ff3fff

def z1014 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xffc520cfc373fccf 0xfffc520cfc373fcc

def z1015 : W := mkw 0x602ca00036ca0000 0xa602ca00036ca000 0x144ce0003f7f0003 0x0144ce0003f7f000

def z1016 : W := mkw 0x4a2c53d327142f5a 0x84a2c53d327142f5 0x040c03c307000f02 0x1040c03c307000f0

def z1017 : W := mkw 0xc03ffbbaa6000000 0xfc03ffbbaa600000 0xffbfffffc7000002 0x3ffbfffffc700000

def z1018 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x9ec520cfc37370c7 0x69ec520cfc37370c

def z1019 : W := mkw 0xe23ffbbab6ce0112 0xfe23ffbbab6ce011 0xffbffffffc8c8330 0xbffbffffffc8c833

def z1020 : W := mkw 0x0200411300140552 0x0020041130014055 0x1c4ac333049c8ffe 0xf1c4ac333049c8ff

def z1021 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xfdcadfffc49c0006 0xffdcadfffc49c000

def z1022 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffbfffffffef0001 0xbffbfffffffef000

def z1023 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe9b21c3c3880f0fc 0xee9b21c3c3880f0f

def z1024 : W := mkw 0x2713493f50f515f6 0x52713493f50f515f 0x1843e03fc0ff00f4 0x21843e03fc0ff00f

def z1025 : W := mkw 0x582c16802e00c208 0x8582c16802e00c20 0xe7b81f003c00ff0b 0xde7b81f003c00ff0

def z1026 : W := mkw 0x0200411300140552 0x0020041130014055 0x7dcbe33304ff8ffe 0xf7dcbe33304ff8ff

def z1027 : W := mkw 0x6000000036ca0000 0x06000000036ca000 0x1fcfe0003fff0007 0xc1fcfe0003fff000

def z1028 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbc4520cfc3737cce 0x3bc4520cfc3737cc

def z1029 : W := mkw 0x150004454931fce4 0x0150004454931fce 0x004000000373fcff 0x4004000000373fcf

def z1030 : W := mkw 0xf83fffbabecac208 0xff83fffbabecac20 0x413adf303c8c8300 0x8413adf303c8c830

def z1031 : W := mkw 0xe03fbaa8b6ca0000 0xfe03fbaa8b6ca000 0xbef53ccffb730007 0x7bef53ccffb73000

def z1032 : W := mkw 0x6000000036ca0000 0x06000000036ca000 0x014ac0003fff0007 0xc014ac0003fff000

def z1033 : W := mkw 0x82005bba80040112 0x182005bba8004011 0xe10adfffc48c8330 0xbe10adfffc48c833

def z1034 : W := mkw 0x580004402f00ea08 0x0580004402f00ea0 0xe7b81f003f00ff0b 0xde7b81f003f00ff0

def z1035 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffffffffc09c0004 0x3ffffffffc09c000

def z1036 : W := mkw 0x0100004441213880 0x0010000444121388 0xbe8520cfc36370cd 0x7be8520cfc36370c

def z1037 : W := mkw 0x180016c00900ea08 0x0180016c00900ea0 0xe2301fc03800ff09 0x1e2301fc03800ff0

def z1038 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebb31cfff8e0f0fd 0xfebb31cfff8e0f0f

def z1039 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0x967dffcfff7f0003 0x1967dffcfff7f000

def z1040 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x65b81f003f00ff0b 0xd65b81f003f00ff0

def z1041 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe2311c3c38e0f0fd 0xee2311c3c38e0f0f

def z1042 : W := mkw 0x3413ac2c18e0d0a4 0x73413ac2c18e0d0a 0xfbb3fc3c38e0f0fd 0xefbb3fc3c38e0f0f

def z1043 : W := mkw 0x0200411300140552 0x0020041130014055 0xffcac333049cffff 0xfffcac333049cfff

def z1044 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x5fffe0303fff8037 0xc5fffe0303fff803

def z1045 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xc33c1fc03f00ff0b 0xcc33c1fc03f00ff0

def z1046 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xa6bc1fc03f007f0b 0x5a6bc1fc03f007f0

def z1047 : W := mkw 0x34000c2c18e0d0a4 0x134000c2c18e0d0a 0xe3b01c3c38e0f0fd 0xee3b01c3c38e0f0f

def z1048 : W := mkw 0x802cf39280000000 0xa802cf3928000000 0xffbdffcfc0000000 0x3ffbdffcfc000000

def z1049 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe0301fc03800ff08 0x1e0301fc03800ff0

def z1050 : W := mkw 0x8013fbba80000000 0x78013fbba8000000 0xfd8bffffc0000000 0x3fd8bffffc000000

def z1051 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xfffedff03f9cffff 0xffffedff03f9cfff

def z1052 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xe5881fffc0000000 0x3e5881fffc000000

def z1053 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x82353cffc0000000 0x282353cffc000000

def z1054 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xebbbdfffc0000000 0x3ebbbdfffc000000

def z1055 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffbffffffcec0005 0xfffbffffffcec000

def z1056 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x9e3fffffc0000000 0x39e3fffffc000000

def z1057 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x7fffe0003fff800f 0xc7fffe0003fff800

def z1058 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xe9821fffc08080fc 0xfe9821fffc08080f

def z1059 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebb31f3c38e0fffd 0xfebb31f3c38e0fff

def z1060 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbec520cfc7ff7ccf 0xfbec520cfc7ff7cc

def z1061 : W := mkw 0x802cfbba80000000 0xb802cfbba8000000 0x940cffcfc0000000 0x1940cffcfc000000

def z1062 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xefbb1f3c38e0f0fd 0xfefbb1f3c38e0f0f

def z1063 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0x6d8b033c04e08ffe 0xf6d8b033c04e08ff

def z1064 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc48c0000 0xbffbfffffc48c000

def z1065 : W := mkw 0x0200411300140552 0x0020041130014055 0x65cac330049c8ffe 0xd65cac330049c8ff

def z1066 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbec7e0cfc3ff7ccf 0x7bec7e0cfc3ff7cc

def z1067 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbff520cffb737ccf 0xfbff520cffb737cc

def z1068 : W := mkw 0x6000a00036ca0000 0x26000a00036ca000 0x1040e0003fff0007 0xc1040e0003fff000

def z1069 : W := mkw 0x802c5bba80000000 0x9802c5bba8000000 0xffbd3fffc0000000 0x3ffbd3fffc000000

def z1070 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbec520cfc37370c5 0x3bec520cfc37370c

def z1071 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xe7bd3fffc0000000 0x3e7bd3fffc000000

def z1072 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0xfffffc003fff0007 0xcfffffc003fff000

def z1073 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0x96353ccfc0000000 0x196353ccfc000000

def z1074 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xfc0fffffc0000000 0x3fc0fffffc000000

def z1075 : W := mkw 0x802c5bba80000000 0x9802c5bba8000000 0xe40c1fffc0000000 0x3e40c1fffc000000

def z1076 : W := mkw 0xc03ffbbaa60a0000 0xfc03ffbbaa60a000 0xffbfffffc40c0000 0x3ffbfffffc40c000

def z1077 : W := mkw 0x582cb6c02f0aea08 0xa582cb6c02f0aea0 0xfffdffc03f7fff0f 0xdfffdffc03f7fff0

def z1078 : W := mkw 0x7c3fbeec3feafaac 0xf7c3fbeec3feafaa 0x82353ccc3b637001 0x082353ccc3b63700

def z1079 : W := mkw 0x0200411300140552 0x0020041130014055 0x698ac333048c8ffc 0xf698ac333048c8ff

def z1080 : W := mkw 0x3413ac2c18ead0a4 0x73413ac2c18ead0a 0xebb3dc3c38ecf0fd 0xeebb3dc3c38ecf0f

def z1081 : W := mkw 0x402c000026000000 0x8402c00002600000 0x1fffe0003fff0007 0xc1fffe0003fff000

def z1082 : W := mkw 0x0200411300140552 0x0020041130014055 0x7d8ac333048c8ff8 0xb7d8ac333048c8ff

def z1083 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7fc1fc03f73ff0f 0xde7fc1fc03f73ff0

def z1084 : W := mkw 0x3413ac2c18ead0a4 0x73413ac2c18ead0a 0xfffbfc3c3cfff0ff 0xefffbfc3c3cfff0f

def z1085 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xe6841fffc0000000 0x3e6841fffc000000

def z1086 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xfffffc3c3ffff0ff 0xefffffc3c3ffff0f

def z1087 : W := mkw 0x592c04456f31fec8 0x8592c04456f31fec 0x1ffd20003f73ffcf 0xc1ffd20003f73ffc

def z1088 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffffffffc49c8f0e 0xfffffffffc49c8f0

def z1089 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x9235fccfc0000000 0x09235fccfc000000

def z1090 : W := mkw 0x0300004541353dd2 0x00300004541353dd 0xffc720ffc7ffffff 0xfffc720ffc7fffff

def z1091 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffbffffffbe30005 0xfffbffffffbe3000

def z1092 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1dfac0003fff0007 0xc1dfac0003fff000

def z1093 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xf53effffc0000000 0x3f53effffc000000

def z1094 : W := mkw 0x0200411300140552 0x0020041130014055 0x658ac333048c8ffa 0xf658ac333048c8ff

def z1095 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x1fffe0003fff0007 0xc1fffe0003fff000

def z1096 : W := mkw 0x0013082800000000 0x5001308280000000 0xebb31cffc0000000 0x3ebb31cffc000000

def z1097 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03b00ff09 0x1e7bc1fc03b00ff0

def z1098 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x177fe0003fff0003 0x8177fe0003fff000

def z1099 : W := mkw 0x592c16c06f01ea08 0x8592c16c06f01ea0 0xe7bc3fc0ff03ff0b 0xde7bc3fc0ff03ff0

def z1100 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xefb71c3c3be0f0ff 0xeefb71c3c3be0f0f

def z1101 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xf7bdffcfc0000000 0x1f7bdffcfc000000

def z1102 : W := mkw 0x003fa82800000000 0xf003fa8280000000 0xffbffcffc0000000 0x3ffbffcffc000000

def z1103 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc3000003 0x7ffbfffffc300000

def z1104 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xefb71cfc38e0f0fd 0xfefb71cfc38e0f0f

def z1105 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xe5881fffc4008f0a 0xfe5881fffc4008f0

def z1106 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x07fec0003fff0007 0xc07fec0003fff000

def z1107 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03f007f03 0x1e7bc1fc03f007f0

def z1108 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bd3fc03f63ff0b 0xde7bd3fc03f63ff0

def z1109 : W := mkw 0xc03ffbbaa60a0000 0xfc03ffbbaa60a000 0xffbfffffc3030000 0x3ffbfffffc303000

def z1110 : W := mkw 0x0200411300140552 0x0020041130014055 0x7dcbe33fc49c8ffe 0xf7dcbe33fc49c8ff

def z1111 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xb6c520cfc3737c0b 0x5b6c520cfc3737c0

def z1112 : W := mkw 0x190004454931fec8 0x0190004454931fec 0x000000000000ffc8 0x0000000000000ffc

def z1113 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xb64520cfc3737ccb 0x3b64520cfc3737cc

def z1114 : W := mkw 0x8013fbba80000000 0x78013fbba8000000 0x9803fcffc0000000 0x29803fcffc000000

def z1115 : W := mkw 0x0100004441213880 0x0010000444121388 0x9a0520cfc3637001 0x29a0520cfc363700

def z1116 : W := mkw 0x182c16c00900ea08 0x8182c16c00900ea0 0xe7bc1fc03800ff09 0xde7bc1fc03800ff0

def z1117 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x167de0003fff0007 0xc167de0003fff000

def z1118 : W := mkw 0x102c16800800c000 0x8102c16800800c00 0xe7bc1fc03c00ff0b 0xde7bc1fc03c00ff0

def z1119 : W := mkw 0x3500044559f1fce4 0x03500044559f1fce 0x0000000038e0fcfd 0xc0000000038e0fcf

def z1120 : W := mkw 0xa613e93f90f415f6 0x7a613e93f90f415f 0x1843e03fc0fc00f4 0x21843e03fc0fc00f

def z1121 : W := mkw 0x802cfbba80000000 0xb802cfbba8000000 0xfd8effffc0000000 0x3fd8effffc000000

def z1122 : W := mkw 0xa03ffbba90c00000 0xfa03ffbba90c0000 0xfffffffffcfc0007 0xffffffffffcfc000

def z1123 : W := mkw 0x8000fbba80000000 0x38000fbba8000000 0xf000ffffc0000000 0x3f000ffffc000000

def z1124 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x8bb31c3c38e070f5 0xe8bb31c3c38e070f

def z1125 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc00000cc 0x7ffbfffffc00000c

def z1126 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe63c1fc03f00ff0b 0x1e63c1fc03f00ff0

def z1127 : W := mkw 0x3500044559f1fce4 0x03500044559f1fce 0x004000003b737ccf 0x4004000003b737cc

def z1128 : W := mkw 0xc02cfbbaa60a0000 0xbc02cfbbaa60a000 0xf44cffffc71f0002 0x3f44cffffc71f000

def z1129 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xc3331c3c38e0f0fd 0xcc3331c3c38e0f0f

def z1130 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x3fffe0033fff0007 0xf3fffe0033fff000

def z1131 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0xffb73cffc0000000 0x3ffb73cffc000000

def z1132 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x0bfbc0003fff0007 0xc0bfbc0003fff000

def z1133 : W := mkw 0x6013000036ca0000 0x46013000036ca000 0x1ffbc0003fff0007 0xc1ffbc0003fff000

def z1134 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x7fffe3303fff8fff 0xf7fffe3303fff8ff

def z1135 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xeab11c3c3860f0fd 0x6eab11c3c3860f0f

def z1136 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x41321c303880f0f8 0x841321c303880f0f

def z1137 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebf31c3c3bf3f0ff 0xeebf31c3c3bf3f0f

def z1138 : W := mkw 0x0100004441213880 0x0010000444121388 0xbec520cfc3737007 0x7bec520cfc373700

def z1139 : W := mkw 0x0200411300140552 0x0020041130014055 0x7dcee333079f8ffe 0xf7dcee333079f8ff

def z1140 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1fffe0003fff80ff 0xc1fffe0003fff80f

def z1141 : W := mkw 0x17004d7f4935fdf6 0x117004d7f4935fdf 0xe0001fffc000fff8 0x3e0001fffc000fff

def z1142 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xe0001fffc00080f8 0x3e0001fffc00080f

def z1143 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xfbb7fcffc0000000 0x2fbb7fcffc000000

def z1144 : W := mkw 0x0300004541353dd2 0x00300004541353dd 0xbec520cfc3ff7cff 0x7bec520cfc3ff7cf

def z1145 : W := mkw 0x003fb28000000000 0xe003fb2800000000 0xffbfffcfc0000000 0x3ffbfffcfc000000

def z1146 : W := mkw 0x0200411300140552 0x0020041130014055 0x5d4ac333049c8ff6 0xb5d4ac333049c8ff

def z1147 : W := mkw 0x790004457ffbfec8 0x0790004457ffbfec 0x004000003fffffcf 0xc004000003fffffc

def z1148 : W := mkw 0x120045130814c552 0x0120045130814c55 0xf7f8df033c1cff0b 0xdf7f8df033c1cff0

def z1149 : W := mkw 0x802c5bba80000000 0x9802c5bba8000000 0xffbedfffc0000000 0x3ffbedfffc000000

def z1150 : W := mkw 0xa03ffbba90c00000 0xfa03ffbba90c0000 0xffbfffffc0e00004 0x3ffbfffffc0e0000

def z1151 : W := mkw 0xc03ffbbaa60a0000 0xfc03ffbbaa60a000 0xffffffffff1f0003 0xfffffffffff1f000

def z1152 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xe7bedfffc0000000 0x3e7bedfffc000000

def z1153 : W := mkw 0x80135bba80000000 0x580135bba8000000 0xffbbdfffc0000000 0x3ffbbdfffc000000

def z1154 : W := mkw 0x14000c2c0820d0a4 0x114000c2c0820d0a 0xebb21c3c3880f0fd 0xeebb21c3c3880f0f

def z1155 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xa24520cfc3737ccf 0x7a24520cfc3737cc

def z1156 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x82341fc03b007f01 0x182341fc03b007f0

def z1157 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1fffe00fffff0007 0xe1fffe00fffff000

def z1158 : W := mkw 0xa03ffbba90c00000 0xfa03ffbba90c0000 0xfffffffffbf30007 0xffffffffffbf3000

def z1159 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebbb1f3c3ce0f3fd 0xeebbb1f3c3ce0f3f

def z1160 : W := mkw 0x603fb28036ca0000 0xe603fb28036ca000 0x9ffffcc03fff0007 0xc9ffffcc03fff000

def z1161 : W := mkw 0x180016c00900ea08 0x0180016c00900ea0 0xe7b81fc03c00ff0b 0xde7b81fc03c00ff0

def z1162 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xf7bc3fc3ff00ff0b 0xdf7bc3fc3ff00ff0

def z1163 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xfffffffffb730007 0x7fffffffffb73000

def z1164 : W := mkw 0x82005bba80040112 0x182005bba8004011 0xe0001fffc0008330 0x3e0001fffc000833

def z1165 : W := mkw 0x5b0004456f35ffda 0x05b0004456f35ffd 0x004000003fffffff 0xc004000003ffffff

def z1166 : W := mkw 0x803fbaa880000000 0xf803fbaa88000000 0xa2353ccfc0000000 0x3a2353ccfc000000

def z1167 : W := mkw 0x580016c02f00ea08 0x0580016c02f00ea0 0xe3b01fc03f00ff0b 0xde3b01fc03f00ff0

def z1168 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1fffe0c3ffff0007 0xd1fffe0c3ffff000

def z1169 : W := mkw 0x0000000000000000 0x0000000000000000 0x7dcac330049c8ffe 0xf7dcac330049c8ff

def z1170 : W := mkw 0x100004040820d080 0x0100004040820d08 0xebb31c3c38e0f0fd 0xeebb31c3c38e0f0f

def z1171 : W := mkw 0xca2cf3d3a7142f5a 0xaca2cf3d3a7142f5 0x144ce3c3c71c0f02 0x1144ce3c3c71c0f0

def z1172 : W := mkw 0x603fa82836ca0000 0xf603fa82836ca000 0xfffffc3c3fff80ff 0xefffffc3c3fff80f

def z1173 : W := mkw 0x823ffbba80040112 0xf823ffbba8004011 0xffbfffffc48c8f3a 0xfffbfffffc48c8f3

def z1174 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x8a331c3c38e0f0fd 0xe8a331c3c38e0f0f

def z1175 : W := mkw 0x603fa82836ca0000 0xf603fa82836ca000 0x1fffe03c3fff0007 0xe1fffe03c3fff000

def z1176 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xffcfe3cfc7ffffcf 0xfffcfe3cfc7ffffc

def z1177 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03f80ffff 0xde7bc1fc03f80fff

def z1178 : W := mkw 0x6013a00036ca0000 0x66013a00036ca000 0x1843e0003bff0005 0x01843e0003bff000

def z1179 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xffbfffffff630003 0xfffbfffffff63000

def z1180 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xe0301fffc0000000 0x3e0301fffc000000

def z1181 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xfeb53fffc0000000 0x3feb53fffc000000

def z1182 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x7fffe3003fff0007 0xd7fffe3003fff000

def z1183 : W := mkw 0xe03ffbbab6ca0000 0xfe03ffbbab6ca000 0xfffffffffcff0004 0xbfffffffffcff000

def z1184 : W := mkw 0x10130c280800c000 0x510130c280800c00 0xebb31c3c3880f0fd 0xeebb31c3c3880f0f

def z1185 : W := mkw 0xe03fbaa8b6ca0000 0xfe03fbaa8b6ca000 0xfffffcfcffff0007 0xefffffcfcffff000

def z1186 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xffbedfc03f00ff0b 0xdffbedfc03f00ff0

def z1187 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xd73fffffc0000000 0x1d73fffffc000000

def z1188 : W := mkw 0x823ffbba80040112 0xf823ffbba8004011 0xffbfffffc08c0030 0x3ffbfffffc08c003

def z1189 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc0800004 0xfffbfffffc080000

def z1190 : W := mkw 0xe03fb280b6ca0000 0xee03fb280b6ca000 0x1fffe0c0ffff0007 0xc1fffe0c0ffff000

def z1191 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x453c1fc03f00ff0b 0xd453c1fc03f00ff0

def z1192 : W := mkw 0x100004000800c000 0x0100004000800c00 0xe3b01f003800ff09 0xde3b01f003800ff0

def z1193 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbc1fc03f00ffcf 0xfefbc1fc03f00ffc

def z1194 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe3b21c3038e0f0fd 0xce3b21c3038e0f0f

def z1195 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1fffe0003f7f0003 0x01fffe0003f7f000

def z1196 : W := mkw 0x0100004441213880 0x0010000444121388 0x960520cfc3637001 0x1960520cfc363700

def z1197 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc0007009 0x7ffbfffffc000700

def z1198 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe3b21c3c3880f0f9 0xee3b21c3c3880f0f

def z1199 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x9ec520cfc3737c07 0x59ec520cfc3737c0

def z1200 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffffffffc41c0002 0x3ffffffffc41c000

def z1201 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0x9e4520cfc3737cc7 0x39e4520cfc3737cc

def z1202 : W := mkw 0x750004457ffbfce4 0x0750004457ffbfce 0x004000003ffffcff 0xc004000003ffffcf

def z1203 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x82353fcfc0000000 0x182353fcfc000000

def z1204 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xf63dffffc0000000 0x3f63dffffc000000

def z1205 : W := mkw 0x602ca00036ca0000 0xa602ca00036ca000 0x17fce0003fff0007 0xc17fce0003fff000

def z1206 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1ef7e0003bff0007 0x41ef7e0003bff000

def z1207 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbe1fc03f80ff0f 0xdefbe1fc03f80ff0

def z1208 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x1efde0003f7f0007 0x41efde0003f7f000

def z1209 : W := mkw 0x80001aa880000000 0x180001aa88000000 0xa0001ccfc0000000 0x3a0001ccfc000000

def z1210 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x157ee0003fff0007 0xc157ee0003fff000

def z1211 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xbeb7fcffc0000000 0x3beb7fcffc000000

def z1212 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xffb31c3f38e0f0fd 0xfffb31c3f38e0f0f

def z1213 : W := mkw 0x0200411300140552 0x0020041130014055 0xfffadf33049c8ffe 0xffffadf33049c8ff

def z1214 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xffcfe0ffc7fffcff 0xfffcfe0ffc7fffcf

def z1215 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xe2053fffc0000000 0x3e2053fffc000000

def z1216 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe5b81fc03c00ff0a 0xde5b81fc03c00ff0

def z1217 : W := mkw 0x0200411300140552 0x0020041130014055 0x7dcee3f3c49c8ffe 0xf7dcee3f3c49c8ff

def z1218 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc4000f02 0x3ffbfffffc4000f0

def z1219 : W := mkw 0xc03ffbbaa6000000 0xfc03ffbbaa600000 0xffbffffffb000001 0x3ffbffffffb00000

def z1220 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xefb31c3c38e0fcff 0xfefb31c3c38e0fcf

def z1221 : W := mkw 0x6013a00036ca0000 0x66013a00036ca000 0x1dcbe0003fff0007 0xc1dcbe0003fff000

def z1222 : W := mkw 0x0200411300140552 0x0020041130014055 0x7c4ac333049c8ffe 0x37c4ac333049c8ff

def z1223 : W := mkw 0x0000082800000000 0x1000008280000000 0xfe853cffc0000000 0x3fe853cffc000000

def z1224 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0x49331c3c38e0f0fd 0xe49331c3c38e0f0f

def z1225 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffbfffffc4008300 0xbffbfffffc400830

def z1226 : W := mkw 0x3413ac2c18ead0a4 0x73413ac2c18ead0a 0xebb33c3c38e3f0fd 0xeebb33c3c38e3f0f

def z1227 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xebb73c3c3be3f0fd 0xeebb73c3c3be3f0f

def z1228 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe33c1fc03f00ff09 0x9e33c1fc03f00ff0

def z1229 : W := mkw 0x14000c2c0820d0a4 0x114000c2c0820d0a 0xebb11c3c3860f0fd 0xeebb11c3c3860f0f

def z1230 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0xffffffffc3130002 0x3ffffffffc313000

def z1231 : W := mkw 0x002c128000000000 0x8002c12800000000 0xbeb53ccfc0000000 0x3beb53ccfc000000

def z1232 : W := mkw 0x2613493f10f415f6 0x52613493f10f415f 0x0803003f00e000f4 0x20803003f00e000f

def z1233 : W := mkw 0x802cfbba80000000 0xb802cfbba8000000 0xe008dfffc0000000 0x3e008dfffc000000

def z1234 : W := mkw 0x802cfbba80000000 0xb802cfbba8000000 0xfe8dffffc0000000 0x3fe8dffffc000000

def z1235 : W := mkw 0x0100004541313cc0 0x00100004541313cc 0xbac520cfc37370cd 0x6bac520cfc37370c

def z1236 : W := mkw 0x603fa00036ca0000 0xe603fa00036ca000 0x197be0003fff0007 0xc197be0003fff000

def z1237 : W := mkw 0x803ffbba80000000 0xf803ffbba8000000 0x9fbffcffc0000000 0x29fbffcffc000000

def z1238 : W := mkw 0x34130c2c18e0d0a4 0x534130c2c18e0d0a 0xe9331c3c38e0f0fc 0xae9331c3c38e0f0f

def z1239 : W := mkw 0x80005bba80000000 0x180005bba8000000 0xfc801fffc0000000 0x3fc801fffc000000

def z1240 : W := mkw 0x6013a00036ca0000 0x66013a00036ca000 0x1bf3e0003fff0007 0xc1bf3e0003fff000

def z1241 : W := mkw 0x0300004541353dd2 0x00300004541353dd 0xffcd23cfc7ffffff 0xfffcd23cfc7fffff

def z1242 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bedfc03f8cff0b 0xde7bedfc03f8cff0

def z1243 : W := mkw 0x502c04002e00c000 0x8502c04002e00c00 0xe7bc1f003f00ff0b 0xde7bc1f003f00ff0

def z1244 : W := mkw 0x002c128000000000 0x8002c12800000000 0xe7bc1fcfc0000000 0x3e7bc1fcfc000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z7,z8,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z9,z10]),(0,[z0,z2,z3,z4,z5,z6,z11]),(0,[z12,z0,z2,z3,z4,z6,z13])],[(0,[z0,z2,z14,z3,z4,z5,z6]),(0,[z0,z2,z15,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z16]),(0,[z0,z2,z3,z4,z5,z10,z17]),(0,[z0,z2,z3,z4,z5,z18,z6])],[(0,[z19,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z20,z6]),(1,[z0,z2,z3,z21,z5,z6]),(0,[z0,z22,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z23,z24])],[(0,[z0,z25,z2,z3,z4,z5,z6]),(1,[z0,z26,z3,z4,z5,z6]),(0,[z27,z0,z2,z3,z4,z5,z13]),(0,[z28,z0,z3,z8,z4,z5,z6]),(0,[z0,z2,z29,z3,z8,z5,z6])],[(0,[z30,z0,z2,z3,z31,z5,z6]),(0,[z0,z2,z32,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z33,z6]),(1,[z0,z2,z3,z4,z5,z34]),(0,[z0,z35,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z24,z6]),(0,[z0,z2,z3,z4,z5,z36,z13])],[(1,[z37,z2,z3,z4,z38,z6]),(0,[z27,z0,z2,z39,z4,z5,z6]),(0,[z40,z0,z2,z3,z4,z5,z41]),(0,[z0,z42,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z43])],[(0,[z44,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z45,z4,z5,z6]),(0,[z0,z2,z3,z4,z46,z47,z6])]],
   [[(0,[z0,z2,z48,z3,z4,z5,z6]),(0,[z49,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z50,z3,z4,z5,z6]),(1,[z2,z51,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z52,z6,z17]),(0,[z0,z2,z3,z4,z5,z6,z53]),(0,[z54,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z55,z6]),(1,[z0,z2,z3,z4,z56,z6]),(0,[z0,z2,z3,z57,z4,z5,z58])],[(0,[z59,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z60,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z61,z58]),(0,[z0,z2,z3,z4,z5,z62,z24])],[(0,[z0,z2,z3,z63,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z64,z6]),(0,[z0,z65,z2,z3,z66,z5,z6]),(0,[z0,z2,z3,z67,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z68,z6]),(0,[z0,z2,z3,z4,z5,z6,z69]),(0,[z0,z2,z3,z70,z4,z5,z24])],[(0,[z71,z0,z2,z3,z4,z5,z13]),(0,[z72,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z73]),(0,[z0,z2,z74,z3,z4,z5,z6]),(0,[z0,z2,z75,z4,z66,z5,z6]),(1,[z0,z2,z3,z4,z5,z76]),(0,[z0,z2,z3,z77,z4,z46,z6]),(0,[z0,z2,z3,z4,z78,z5,z6])],[(0,[z0,z2,z79,z3,z4,z5,z24])],[(0,[z0,z2,z3,z80,z4,z5,z6]),(0,[z81,z0,z2,z3,z4,z5,z82]),(0,[z0,z2,z83,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z6,z84]),(0,[z0,z2,z3,z4,z85,z5,z6]),(0,[z12,z0,z2,z3,z4,z46,z6])]],
   [[(0,[z86,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z87,z88,z5]),(0,[z27,z0,z2,z3,z89,z5,z6]),(0,[z0,z90,z2,z91,z4,z5,z6])],[(0,[z0,z90,z2,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z93]),(0,[z0,z2,z3,z77,z4,z23,z6]),(0,[z0,z2,z94,z3,z4,z5,z6]),(0,[z0,z2,z95,z3,z4,z5,z96]),(0,[z97,z0,z2,z3,z4,z98,z6]),(0,[z0,z2,z99,z3,z4,z5,z6]),(0,[z0,z100,z2,z3,z4,z5,z24])],[(0,[z101,z0,z2,z3,z4,z5,z6]),(0,[z102,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z9,z61])],[(0,[z0,z2,z3,z103,z104,z4,z5]),(0,[z105,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z106,z6]),(0,[z0,z2,z3,z107,z4,z5,z24]),(0,[z81,z0,z2,z3,z108,z5,z6]),(0,[z109,z0,z2,z3,z4,z5,z6])],[(0,[z2,z110,z3,z104,z4,z5,z6]),(0,[z0,z2,z111,z3,z4,z5,z6]),(0,[z0,z2,z112,z3,z4,z5,z6]),(0,[z49,z40,z0,z2,z3,z4,z5]),(0,[z0,z90,z2,z113,z4,z5,z6])],[(0,[z27,z49,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z114,z5,z6]),(0,[z0,z2,z3,z115,z4,z5,z6]),(0,[z0,z2,z91,z3,z4,z5,z6]),(0,[z116,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z117,z4,z5,z6]),(0,[z0,z2,z3,z4,z118,z5,z6])],[(0,[z0,z2,z3,z4,z119,z5,z6]),(0,[z81,z0,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z6,z120]),(0,[z0,z2,z3,z4,z5,z9,z6])],[(0,[z30,z2,z3,z31,z4,z5,z6]),(0,[z121,z0,z2,z3,z4,z5,z122]),(0,[z37,z0,z2,z3,z4,z38,z6]),(0,[z0,z2,z3,z4,z5,z123,z6]),(0,[z0,z2,z124,z3,z4,z5,z6]),(0,[z0,z125,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z126,z6]),(0,[z0,z2,z3,z4,z127,z5,z6])]],
   [[(0,[z0,z2,z128,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z129,z6]),(1,[z130,z2,z3,z4,z5,z6]),(0,[z0,z2,z131,z3,z4,z5,z6]),(0,[z0,z2,z3,z132,z4,z47,z6])],[(0,[z133,z2,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z134,z4,z5,z6]),(0,[z0,z2,z3,z4,z38,z5,z6]),(0,[z0,z2,z3,z135,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z136,z6])],[(0,[z137,z0,z2,z3,z4,z5,z6]),(0,[z81,z0,z3,z4,z5,z23,z6]),(0,[z0,z2,z3,z138,z4,z5,z6]),(0,[z0,z139,z2,z3,z4,z6,z13])],[(0,[z0,z2,z3,z140,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z141]),(0,[z0,z2,z3,z57,z31,z5,z6]),(1,[z0,z2,z128,z4,z5,z6]),(0,[z27,z0,z2,z3,z4,z5,z41]),(0,[z27,z97,z0,z2,z3,z4,z5]),(0,[z81,z0,z2,z142,z4,z5,z6]),(0,[z0,z2,z143,z3,z4,z5,z6])],[(0,[z0,z139,z110,z3,z4,z5,z6]),(1,[z144,z145,z3,z4,z5,z6]),(0,[z144,z2,z3,z104,z4,z5,z6]),(0,[z146,z0,z2,z3,z4,z5,z6]),(1,[z147,z2,z3,z88,z5,z6]),(0,[z40,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z148,z3,z8,z5,z6]),(0,[z0,z2,z149,z4,z66,z5,z6]),(0,[z150,z0,z2,z3,z4,z5,z6]),(0,[z151,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z152]),(0,[z0,z2,z7,z3,z4,z5,z24]),(0,[z0,z2,z3,z153,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z154]),(0,[z0,z2,z3,z155,z4,z5,z6]),(0,[z0,z2,z156,z3,z4,z5,z6])],[(0,[z0,z145,z3,z4,z5,z6,z61]),(0,[z71,z0,z2,z157,z4,z5,z6]),(0,[z0,z2,z158,z3,z4,z5,z13]),(0,[z0,z2,z159,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z24])],[(0,[z0,z2,z83,z95,z4,z5,z6]),(0,[z0,z160,z2,z3,z4,z5,z6]),(1,[z0,z2,z48,z79,z3,z6]),(0,[z0,z2,z3,z4,z5,z24,z58])]],
   [[(0,[z2,z110,z3,z4,z5,z161,z6]),(0,[z0,z2,z3,z4,z5,z162,z6]),(0,[z0,z2,z157,z4,z5,z163,z6]),(0,[z147,z0,z2,z3,z88,z5,z6]),(0,[z0,z2,z3,z4,z161,z6,z13]),(0,[z0,z2,z3,z4,z5,z24,z164])],[(0,[z0,z2,z165,z3,z4,z5,z6]),(1,[z27,z2,z3,z4,z5,z166]),(0,[z0,z2,z3,z4,z5,z6,z167]),(0,[z168,z169,z2,z3,z4,z5,z6])],[(0,[z28,z0,z2,z3,z4,z170,z6]),(0,[z0,z2,z3,z4,z5,z6,z171]),(0,[z81,z0,z2,z3,z115,z5,z6]),(0,[z0,z2,z172,z3,z4,z5,z6]),(0,[z0,z2,z3,z173,z4,z5,z6]),(0,[z0,z2,z95,z3,z4,z5,z6]),(0,[z0,z2,z3,z174,z4,z5,z6])],[(0,[z28,z175,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z56,z6])],[(0,[z71,z102,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z176]),(0,[z0,z2,z3,z107,z5,z126,z6]),(0,[z0,z2,z3,z4,z5,z177,z6]),(0,[z0,z178,z2,z3,z4,z5,z6])],[(0,[z179,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z104,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z180,z0,z2,z3,z4,z5,z6]),(0,[z181,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z182]),(0,[z0,z2,z3,z113,z4,z5,z24])],[(0,[z0,z2,z3,z31,z4,z5,z6]),(0,[z0,z2,z3,z149,z4,z5,z6]),(1,[z0,z2,z159,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z13,z183])],[(0,[z184,z0,z2,z3,z4,z5,z6]),(0,[z185,z0,z2,z3,z4,z5,z6]),(1,[z71,z2,z104,z4,z5,z6]),(0,[z30,z0,z2,z3,z4,z5,z13]),(0,[z121,z2,z3,z4,z5,z161,z6]),(1,[z0,z2,z3,z132,z47,z6])]],
   [[(0,[z186,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z187,z6]),(0,[z0,z2,z3,z4,z5,z188,z6])],[(0,[z0,z2,z189,z3,z4,z5,z6]),(0,[z0,z190,z2,z3,z4,z5,z6]),(0,[z0,z191,z2,z3,z4,z5,z6]),(0,[z0,z2,z92,z4,z5,z126,z6]),(1,[z0,z2,z192,z4,z5,z6]),(0,[z168,z0,z2,z3,z4,z5,z24]),(0,[z0,z139,z2,z3,z4,z46,z6]),(0,[z0,z2,z3,z57,z4,z5,z24])],[(0,[z193,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z92,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z194,z5,z6])],[(0,[z0,z2,z3,z4,z5,z195,z6]),(0,[z27,z0,z2,z3,z4,z129,z6]),(0,[z0,z2,z3,z4,z196,z5,z6]),(0,[z0,z65,z2,z3,z4,z5,z6]),(0,[z197,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z198,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z199,z24])],[(0,[z37,z2,z3,z4,z38,z5,z6]),(1,[z200,z0,z3,z4,z5,z61]),(0,[z0,z2,z3,z4,z5,z201,z6]),(0,[z0,z2,z7,z3,z113,z5,z6]),(0,[z0,z2,z202,z3,z4,z5,z6])],[(0,[z203,z0,z2,z3,z104,z4,z5]),(0,[z102,z2,z157,z3,z4,z5,z6]),(1,[z0,z2,z204,z4,z5,z6]),(0,[z0,z139,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z205,z5,z24]),(0,[z0,z2,z7,z3,z5,z126,z6]),(0,[z0,z2,z3,z77,z4,z5,z6]),(0,[z206,z0,z2,z3,z4,z5,z6]),(0,[z207,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z24,z6,z13])],[(0,[z144,z0,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z88,z5,z6]),(0,[z40,z0,z2,z3,z57,z4,z5]),(0,[z208,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z83,z3,z4,z163,z6])],[(0,[z0,z2,z158,z157,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z209,z6]),(0,[z0,z2,z142,z3,z4,z5,z6]),(0,[z0,z210,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z163,z13]),(0,[z0,z2,z3,z4,z5,z6,z211]),(0,[z12,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z212,z0,z2,z3,z4,z5,z6]),(0,[z213,z0,z2,z3,z4,z5,z6]),(0,[z214,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z41,z6]),(0,[z0,z2,z3,z4,z215,z5,z6]),(0,[z0,z216,z2,z3,z4,z5,z6]),(0,[z217,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z132,z5,z47,z6])],[(0,[z0,z145,z2,z3,z4,z5,z6]),(0,[z27,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z218,z3,z4,z5,z6])],[(0,[z0,z2,z219,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z220,z6]),(0,[z0,z2,z91,z48,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z221,z6]),(0,[z0,z2,z3,z4,z5,z6,z222])],[(0,[z0,z2,z48,z3,z31,z5,z6]),(0,[z121,z0,z2,z3,z4,z38,z6]),(0,[z0,z2,z3,z4,z5,z223,z6]),(0,[z0,z2,z224,z3,z77,z5,z6]),(0,[z0,z2,z3,z4,z5,z225,z6])],[(0,[z0,z2,z26,z3,z4,z5,z6]),(1,[z0,z65,z3,z107,z5,z6]),(0,[z0,z2,z3,z4,z10,z6,z120]),(0,[z0,z2,z91,z7,z4,z5,z6])],[(0,[z0,z226,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z227,z6]),(1,[z0,z2,z75,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z228]),(1,[z0,z2,z3,z4,z5,z96]),(0,[z0,z2,z3,z4,z5,z6,z229])],[(0,[z0,z2,z230,z3,z4,z5,z6]),(0,[z27,z0,z2,z3,z4,z55,z6]),(1,[z0,z2,z231,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z232])]],
   [[(1,[z40,z2,z3,z4,z5,z41]),(0,[z233,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z87,z5,z6]),(0,[z234,z0,z2,z3,z4,z5,z6]),(0,[z235,z0,z2,z3,z4,z5,z6]),(0,[z236,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z57,z5,z9,z6]),(0,[z237,z0,z2,z3,z4,z5,z6]),(0,[z0,z238,z2,z3,z4,z5,z6])],[(0,[z0,z2,z239,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z240]),(0,[z27,z0,z2,z3,z45,z5,z6]),(0,[z97,z0,z2,z3,z4,z78,z6]),(0,[z0,z2,z3,z241,z4,z5,z6])],[(1,[z242,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z243,z5,z6]),(0,[z97,z0,z2,z3,z4,z5,z13]),(0,[z244,z0,z2,z3,z4,z5,z6])],[(1,[z0,z245,z3,z4,z5,z6]),(0,[z0,z2,z3,z246,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z36])],[(0,[z0,z2,z3,z4,z5,z163,z6]),(1,[z0,z2,z83,z77,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z247])],[(0,[z0,z2,z248,z3,z4,z5,z6]),(0,[z37,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z75,z3,z4,z5,z6]),(0,[z0,z2,z3,z249,z4,z5,z6]),(0,[z250,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z24,z24])],[(0,[z0,z2,z251,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z58]),(0,[z0,z2,z252,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z253,z6]),(0,[z0,z2,z3,z254,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z164])],[(0,[z0,z2,z3,z4,z5,z255,z6]),(0,[z0,z2,z48,z3,z4,z5,z24])],[(0,[z256,z0,z2,z3,z4,z5,z6])],[(0,[z27,z0,z2,z3,z57,z4,z5]),(0,[z0,z2,z257,z3,z4,z5,z6])],[(0,[z0,z2,z8,z4,z5,z126,z6]),(0,[z81,z0,z2,z3,z4,z5,z24]),(0,[z258,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z24,z61]),(0,[z0,z259,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z260,z4,z5,z6]),(0,[z0,z261,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z262,z6]),(0,[z28,z0,z2,z3,z4,z5,z73]),(0,[z263,z0,z2,z3,z4,z5,z6]),(0,[z264,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z265,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z266,z6]),(0,[z121,z0,z2,z267,z4,z5,z6]),(0,[z0,z2,z3,z4,z21,z5,z6]),(1,[z0,z2,z3,z4,z5,z122]),(0,[z0,z2,z3,z4,z5,z161,z13]),(0,[z0,z2,z268,z3,z4,z5,z6]),(0,[z0,z2,z3,z269,z4,z5,z6]),(0,[z0,z2,z270,z3,z4,z5,z6])],[(0,[z0,z145,z2,z3,z4,z5,z271]),(0,[z0,z2,z3,z4,z5,z272,z6]),(1,[z263,z2,z3,z4,z5,z6]),(1,[z0,z2,z158,z4,z5,z52])]],
   [[(0,[z133,z0,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z6,z273]),(0,[z0,z2,z3,z4,z46,z5,z6]),(0,[z274,z0,z2,z3,z4,z5,z13])],[(0,[z0,z139,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z275,z4,z5,z6]),(0,[z276,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z277,z3,z4,z5,z13])],[(0,[z0,z2,z110,z3,z4,z5,z6]),(0,[z0,z110,z3,z4,z5,z23,z6]),(0,[z121,z0,z2,z3,z134,z5,z6]),(0,[z0,z90,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z8,z4,z5,z13]),(0,[z0,z2,z3,z4,z278,z5,z6]),(0,[z279,z0,z2,z3,z4,z5,z6])],[(0,[z0,z65,z3,z107,z4,z5,z6]),(0,[z0,z2,z280,z3,z4,z5,z13])],[(0,[z0,z281,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z282,z4,z5,z6]),(0,[z0,z2,z3,z4,z23,z163,z6]),(0,[z0,z2,z3,z4,z205,z163,z6]),(0,[z0,z2,z3,z4,z5,z6,z283]),(0,[z0,z2,z3,z4,z5,z284,z6]),(0,[z0,z2,z158,z3,z4,z5,z24]),(0,[z0,z2,z3,z285,z4,z5,z6]),(0,[z109,z0,z2,z3,z4,z5,z24])],[(1,[z102,z2,z157,z4,z5,z6]),(0,[z286,z0,z2,z3,z4,z5,z6]),(0,[z0,z287,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z288]),(0,[z289,z0,z2,z3,z4,z5,z6]),(0,[z81,z0,z2,z3,z4,z205,z6]),(0,[z0,z290,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z52,z6]),(0,[z0,z2,z3,z4,z291,z5,z6])],[(0,[z40,z0,z2,z158,z3,z4,z5]),(0,[z0,z92,z3,z8,z4,z5,z6]),(0,[z0,z2,z92,z4,z5,z163,z6]),(0,[z0,z65,z2,z3,z107,z5,z6]),(0,[z0,z2,z3,z292,z4,z5,z6])]],
   [[(0,[z28,z130,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z293,z6]),(0,[z0,z2,z3,z4,z5,z10,z6])],[(0,[z0,z2,z3,z57,z88,z5,z6]),(1,[z81,z0,z2,z3,z4,z13]),(0,[z0,z2,z3,z4,z5,z6,z294]),(0,[z0,z295,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z47,z6,z13]),(0,[z0,z296,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z297,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z298])],[(0,[z0,z2,z3,z4,z5,z299,z6]),(0,[z0,z2,z3,z4,z5,z300,z6]),(0,[z0,z2,z3,z4,z301,z5,z6]),(0,[z0,z2,z3,z4,z5,z302,z6]),(0,[z303,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z304]),(0,[z0,z2,z3,z4,z5,z305,z6]),(0,[z306,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z307,z4,z5,z6]),(1,[z0,z2,z3,z4,z47,z13]),(0,[z0,z2,z3,z4,z5,z6,z308]),(0,[z0,z2,z3,z4,z5,z24,z13]),(0,[z0,z2,z3,z309,z4,z5,z6])],[(0,[z310,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z311,z6]),(0,[z312,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z313,z3,z4,z5,z6])],[(0,[z30,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z314,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z315]),(0,[z0,z2,z3,z4,z5,z6,z316])],[(0,[z0,z317,z2,z3,z4,z5,z6]),(0,[z0,z2,z48,z3,z4,z5,z13]),(0,[z49,z0,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z6,z318])],[(0,[z319,z0,z2,z3,z4,z5,z6]),(0,[z0,z320,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z321,z5,z6]),(0,[z200,z0,z2,z3,z4,z5,z10]),(0,[z0,z322,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z323,z6])]],
   [[(0,[z0,z2,z324,z3,z4,z5,z6]),(0,[z0,z2,z3,z325,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z326]),(0,[z327,z0,z2,z3,z4,z5,z6]),(0,[z328,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z132,z4,z5,z6])],[(0,[z329,z0,z2,z3,z4,z5,z6]),(0,[z121,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z330,z5,z6]),(0,[z200,z0,z3,z4,z5,z6,z61]),(0,[z331,z0,z2,z3,z4,z5,z24])],[(0,[z144,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z332,z4,z5,z6]),(0,[z0,z2,z79,z3,z4,z205,z6]),(0,[z333,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z271]),(0,[z0,z2,z334,z3,z4,z5,z6]),(0,[z0,z2,z335,z3,z4,z5,z6]),(0,[z0,z169,z2,z3,z4,z5,z6])],[(0,[z37,z2,z110,z3,z4,z5,z6]),(0,[z27,z0,z2,z3,z4,z5,z166]),(0,[z0,z2,z3,z336,z4,z5,z6]),(0,[z337,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z338]),(0,[z0,z2,z3,z4,z5,z339,z24])],[(0,[z0,z2,z3,z103,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z340]),(0,[z0,z2,z341,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z342]),(1,[z0,z2,z343,z4,z5,z6])],[(0,[z344,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z103,z4,z5]),(0,[z0,z2,z3,z4,z5,z345,z6]),(0,[z0,z2,z3,z4,z5,z61,z17]),(0,[z346,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z347,z3,z4,z5,z6]),(0,[z0,z2,z348,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z349,z6]),(0,[z0,z2,z350,z3,z4,z5,z6])],[(0,[z351,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z31,z4,z88,z5,z6]),(0,[z0,z3,z4,z205,z5,z23,z6]),(0,[z0,z2,z3,z4,z5,z47,z6]),(0,[z0,z2,z3,z4,z5,z352,z6])],[(1,[z203,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z353,z6]),(1,[z0,z90,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z354,z6]),(0,[z355,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z356,z3,z4,z5,z6]),(0,[z357,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z358,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z359,z5,z6])],[(0,[z0,z145,z139,z3,z4,z5,z6]),(0,[z0,z3,z107,z4,z66,z5,z6]),(0,[z0,z2,z3,z4,z360,z5,z6]),(0,[z242,z361,z2,z3,z4,z5,z6]),(0,[z0,z2,z91,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z6,z362]),(0,[z0,z2,z3,z363,z4,z5,z6]),(0,[z0,z2,z79,z3,z4,z6,z13]),(0,[z364,z0,z2,z3,z4,z5,z24])],[(0,[z145,z2,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z46,z38,z6]),(0,[z27,z0,z2,z158,z3,z4,z5]),(0,[z365,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z366,z6]),(0,[z0,z65,z2,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z6,z61]),(0,[z367,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z11]),(0,[z0,z2,z3,z4,z5,z9,z13]),(0,[z0,z2,z3,z4,z5,z13,z229])],[(0,[z121,z0,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z126,z13]),(0,[z49,z0,z2,z3,z4,z5,z58])],[(0,[z0,z2,z3,z4,z368,z5,z6]),(0,[z0,z2,z3,z4,z369,z5,z6]),(0,[z0,z2,z3,z370,z4,z5,z6]),(0,[z0,z2,z3,z77,z4,z5,z24])],[(0,[z0,z2,z3,z4,z5,z6,z371]),(0,[z0,z2,z3,z4,z38,z5,z13]),(0,[z0,z90,z2,z8,z4,z5,z6]),(1,[z0,z2,z3,z4,z372,z6]),(0,[z0,z2,z3,z4,z5,z373,z6]),(0,[z0,z374,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z375,z5,z6]),(0,[z27,z0,z245,z3,z4,z5,z6])],[(0,[z0,z2,z48,z3,z88,z5,z6]),(0,[z97,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z79,z3,z5,z47,z6])],[(0,[z0,z2,z8,z4,z5,z163,z6]),(0,[z0,z2,z3,z376,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z58]),(0,[z0,z377,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z98,z6])],[(0,[z378,z0,z2,z3,z4,z5,z6]),(0,[z379,z0,z2,z3,z4,z5,z6]),(0,[z144,z2,z3,z4,z5,z161,z6]),(0,[z0,z2,z3,z4,z5,z380,z6]),(0,[z0,z2,z3,z4,z5,z24,z41]),(0,[z0,z2,z381,z3,z4,z5,z6]),(0,[z0,z2,z382,z3,z4,z5,z6]),(0,[z383,z0,z2,z3,z4,z5,z6])],[(0,[z384,z0,z2,z3,z4,z5,z6]),(0,[z385,z0,z2,z3,z4,z5,z6]),(0,[z386,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z77,z4,z5,z163,z6]),(0,[z387,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z24,z388])],[(0,[z389,z0,z2,z3,z4,z5,z6]),(0,[z390,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z391,z5,z6]),(0,[z0,z2,z3,z4,z5,z392,z6]),(0,[z200,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z393,z6])],[(0,[z394,z0,z2,z3,z4,z5,z6]),(1,[z395,z2,z3,z4,z5,z6]),(0,[z0,z2,z396,z3,z4,z5,z6]),(0,[z0,z2,z3,z107,z5,z47,z6]),(0,[z397,z0,z2,z3,z4,z5,z6]),(0,[z49,z0,z2,z3,z57,z5,z6]),(0,[z0,z2,z3,z4,z5,z58,z13])],[(0,[z0,z2,z3,z4,z5,z398,z6]),(0,[z27,z144,z2,z3,z4,z5,z6]),(0,[z0,z2,z79,z3,z132,z4,z6])]],
   [[(0,[z399,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z400,z4,z5,z6]),(0,[z0,z2,z104,z4,z5,z6,z17]),(1,[z81,z0,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z23,z47,z6]),(0,[z0,z2,z3,z4,z205,z47,z6]),(0,[z0,z2,z95,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z6,z401])],[(0,[z0,z2,z204,z3,z4,z5,z6]),(1,[z0,z2,z3,z402,z5,z6]),(0,[z0,z2,z3,z403,z4,z5,z6]),(0,[z0,z2,z404,z3,z4,z5,z6]),(0,[z0,z2,z3,z405,z4,z5,z6])],[(0,[z0,z2,z406,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z407,z6]),(0,[z0,z2,z79,z3,z4,z46,z6])],[(0,[z0,z408,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z409]),(0,[z0,z2,z3,z410,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z411,z6]),(0,[z0,z2,z3,z412,z4,z5,z6]),(1,[z0,z2,z79,z3,z4,z13]),(0,[z0,z2,z3,z4,z5,z6,z13])],[(0,[z0,z2,z3,z413,z4,z5,z6]),(0,[z0,z2,z3,z31,z4,z5,z13]),(1,[z121,z2,z3,z4,z161,z6]),(0,[z0,z2,z3,z4,z5,z161,z24]),(0,[z0,z3,z4,z5,z10,z6,z61])],[(0,[z0,z2,z414,z3,z4,z5,z6]),(1,[z0,z2,z267,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z93]),(1,[z125,z2,z3,z4,z5,z6]),(0,[z81,z0,z2,z275,z4,z5,z6])],[(0,[z0,z2,z3,z4,z415,z5,z6]),(0,[z133,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z6,z416]),(0,[z0,z2,z3,z417,z4,z5,z6])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z144,z0,z145,z3,z4,z5,z6]),(0,[z0,z2,z418,z3,z4,z5,z6]),(0,[z37,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z3,z419,z4,z5,z6]),(0,[z168,z0,z65,z3,z4,z5,z6]),(0,[z0,z2,z7,z3,z5,z47,z6])]],
   [[(0,[z0,z361,z110,z3,z4,z5,z6]),(0,[z2,z157,z3,z104,z4,z5,z6]),(0,[z203,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z420]),(0,[z0,z2,z3,z8,z4,z5,z24]),(0,[z0,z2,z421,z3,z4,z5,z6])],[(1,[z0,z2,z3,z134,z5,z6]),(0,[z0,z65,z2,z3,z4,z5,z13]),(0,[z0,z2,z422,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z24,z318])],[(0,[z0,z2,z423,z3,z4,z5,z6]),(0,[z0,z2,z3,z391,z4,z5,z6]),(0,[z168,z0,z2,z91,z3,z5,z6]),(0,[z0,z2,z3,z66,z5,z126,z6]),(0,[z0,z424,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z425]),(1,[z0,z2,z3,z4,z5,z426]),(0,[z0,z2,z3,z4,z5,z52,z10]),(0,[z0,z2,z3,z77,z4,z5,z13])],[(0,[z0,z2,z427,z3,z4,z5,z6]),(0,[z147,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z88,z5,z13]),(0,[z0,z2,z3,z4,z5,z428,z6]),(0,[z0,z2,z3,z429,z4,z5,z6])],[(0,[z0,z2,z430,z3,z4,z5,z6]),(0,[z30,z0,z2,z3,z88,z5,z6]),(0,[z12,z0,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z24,z431])],[(0,[z0,z361,z145,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z41,z13]),(0,[z28,z0,z2,z3,z4,z5,z6]),(0,[z0,z361,z3,z4,z5,z10,z6]),(0,[z0,z2,z159,z79,z4,z5,z6])],[(0,[z0,z145,z2,z3,z4,z5,z13]),(0,[z0,z2,z157,z3,z4,z5,z6]),(0,[z432,z0,z2,z3,z4,z5,z6]),(0,[z0,z245,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z433])]],
   [[(0,[z434,z0,z2,z3,z4,z5,z6]),(0,[z71,z2,z3,z104,z4,z5,z6]),(0,[z0,z2,z3,z435,z4,z5,z6]),(1,[z0,z139,z2,z3,z4,z13]),(0,[z0,z2,z32,z3,z4,z5,z24])],[(0,[z0,z2,z3,z436,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z73,z6]),(0,[z0,z90,z92,z3,z4,z5,z6]),(0,[z437,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z158,z3,z4,z5,z17])],[(0,[z438,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z439,z6]),(0,[z0,z139,z2,z3,z4,z5,z24]),(0,[z0,z2,z158,z4,z5,z52,z6])],[(0,[z0,z2,z110,z3,z4,z5,z24]),(0,[z0,z145,z3,z4,z5,z23,z6]),(0,[z440,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z441,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z442,z5,z6]),(0,[z0,z90,z2,z3,z4,z5,z24]),(0,[z81,z0,z2,z3,z4,z5,z16]),(0,[z0,z139,z3,z4,z205,z5,z6]),(0,[z443,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z57,z5,z9])],[(0,[z0,z2,z3,z4,z5,z34,z6]),(0,[z0,z2,z3,z4,z5,z426,z6]),(0,[z0,z2,z3,z4,z5,z6,z444]),(0,[z0,z2,z445,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z446,z6]),(0,[z49,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z3,z57,z4,z5,z9])],[(0,[z0,z2,z3,z4,z447,z5,z6]),(0,[z0,z2,z448,z3,z4,z5,z6]),(0,[z0,z2,z449,z3,z4,z5,z6])],[(0,[z0,z2,z29,z3,z4,z5,z6]),(0,[z81,z263,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z23,z6]),(0,[z0,z2,z113,z4,z5,z126,z6])],[(0,[z450,z0,z2,z3,z4,z5,z6]),(0,[z28,z0,z2,z91,z4,z5,z6]),(0,[z0,z2,z3,z4,z205,z5,z152]),(1,[z0,z361,z3,z4,z5,z10]),(0,[z237,z0,z2,z3,z4,z5,z13])]],
   [[(0,[z28,z0,z2,z92,z4,z5,z6]),(0,[z28,z0,z2,z3,z4,z293,z6]),(1,[z0,z2,z3,z4,z5,z176]),(0,[z451,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z158,z3,z4,z5,z52]),(0,[z0,z2,z3,z4,z5,z452,z6]),(0,[z0,z2,z3,z4,z453,z5,z6])],[(0,[z71,z0,z2,z104,z4,z5,z6]),(0,[z0,z2,z3,z88,z5,z6,z58]),(0,[z0,z2,z3,z454,z4,z5,z6]),(0,[z0,z2,z3,z4,z455,z5,z6]),(0,[z0,z2,z3,z456,z4,z5,z6])],[(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z27,z0,z2,z128,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z457,z6]),(0,[z0,z2,z458,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z459])],[(0,[z0,z460,z2,z3,z4,z5,z6]),(0,[z40,z0,z2,z3,z4,z5,z166]),(0,[z28,z0,z2,z113,z4,z5,z6]),(1,[z168,z0,z3,z66,z5,z6]),(0,[z0,z2,z3,z4,z5,z163,z13]),(0,[z0,z2,z461,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z462,z6]),(0,[z2,z3,z4,z38,z5,z161,z6]),(0,[z37,z0,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z77,z4,z5,z444]),(0,[z0,z2,z3,z4,z5,z13,z338]),(0,[z0,z2,z3,z4,z5,z6,z388])],[(0,[z0,z2,z3,z4,z5,z6,z463]),(0,[z0,z2,z464,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z82]),(0,[z0,z2,z3,z4,z5,z52,z61])],[(0,[z0,z2,z3,z4,z5,z6,z465]),(0,[z466,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z467,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z468,z6]),(0,[z0,z2,z3,z4,z5,z62,z6]),(1,[z0,z469,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z470,z6]),(0,[z0,z361,z2,z3,z4,z5,z10])]],
   [[(0,[z0,z2,z3,z4,z55,z5,z6]),(0,[z28,z0,z90,z3,z4,z5,z6]),(0,[z168,z0,z2,z192,z4,z5,z6]),(0,[z168,z0,z2,z7,z3,z5,z6]),(0,[z0,z2,z91,z4,z5,z126,z6]),(0,[z0,z2,z3,z70,z4,z5,z6])],[(0,[z0,z2,z3,z4,z170,z5,z6]),(1,[z0,z2,z3,z108,z5,z6]),(0,[z0,z2,z91,z3,z4,z5,z24]),(0,[z471,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z472,z6])],[(0,[z0,z2,z3,z4,z5,z6,z473]),(0,[z0,z2,z3,z4,z5,z474,z6]),(0,[z475,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z79,z3,z4,z5,z6]),(0,[z476,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z477,z3,z4,z5,z6])],[(0,[z102,z144,z2,z3,z4,z5,z6]),(0,[z30,z144,z2,z3,z4,z5,z6]),(0,[z121,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z126,z24]),(0,[z0,z2,z83,z3,z4,z5,z6]),(0,[z0,z2,z224,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z459,z6]),(0,[z0,z2,z3,z478,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z479,z13])],[(0,[z0,z2,z3,z4,z5,z6,z480]),(0,[z37,z0,z2,z3,z4,z161,z6]),(0,[z481,z0,z2,z3,z4,z5,z6]),(0,[z482,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z13])],[(0,[z0,z2,z3,z4,z38,z5,z34]),(0,[z0,z2,z3,z4,z38,z5,z24]),(0,[z361,z2,z51,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z483,z5,z6]),(0,[z0,z100,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z484,z4,z5,z6]),(0,[z102,z0,z2,z3,z4,z5,z6]),(0,[z485,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z486,z3,z4,z5,z6]),(0,[z0,z2,z487,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z46,z5,z13])],[(1,[z0,z2,z39,z4,z5,z6]),(0,[z0,z2,z488,z3,z4,z5,z6]),(0,[z0,z2,z3,z107,z4,z5,z6]),(0,[z0,z139,z2,z3,z4,z5,z13]),(0,[z0,z2,z489,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z490,z6])]],
   [[(1,[z133,z110,z3,z4,z5,z6]),(0,[z0,z2,z110,z3,z4,z5,z13]),(0,[z491,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z492,z4,z5,z6]),(0,[z0,z90,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z493,z6])],[(0,[z2,z110,z3,z4,z88,z5,z6]),(0,[z0,z2,z3,z4,z5,z494,z6]),(1,[z0,z2,z142,z4,z5,z6]),(0,[z81,z0,z2,z3,z4,z6,z13])],[(0,[z0,z2,z158,z104,z4,z5,z6]),(0,[z27,z2,z3,z4,z5,z6,z166]),(0,[z0,z2,z3,z4,z5,z495,z6]),(0,[z0,z2,z3,z4,z5,z47,z24])],[(0,[z2,z110,z3,z4,z5,z41,z6]),(0,[z0,z2,z3,z4,z5,z6,z496]),(0,[z0,z2,z497,z3,z4,z5,z6]),(0,[z0,z2,z498,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z499,z6]),(0,[z395,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z52,z13]),(0,[z0,z500,z2,z3,z4,z5,z6])],[(0,[z0,z501,z2,z3,z4,z5,z6]),(0,[z0,z2,z83,z92,z4,z5,z6]),(0,[z168,z0,z2,z231,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z16]),(0,[z0,z2,z3,z502,z4,z5,z6]),(0,[z503,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z431])],[(0,[z0,z2,z3,z504,z4,z5,z6]),(0,[z505,z0,z2,z3,z4,z88,z5]),(0,[z0,z2,z3,z4,z46,z161,z6]),(0,[z0,z2,z3,z4,z5,z10,z13]),(0,[z0,z2,z95,z3,z4,z5,z24]),(0,[z97,z0,z2,z3,z4,z5,z17])],[(0,[z0,z506,z2,z3,z4,z5,z6]),(0,[z27,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z148,z3,z4,z5,z6]),(0,[z507,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z508]),(0,[z0,z2,z83,z104,z4,z5,z6]),(0,[z40,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z509,z3,z4,z5,z6]),(1,[z0,z2,z3,z115,z5,z6]),(0,[z510,z0,z2,z3,z4,z5,z6]),(0,[z511,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z7,z3,z4,z5,z6]),(0,[z0,z2,z83,z113,z4,z5,z6])],[(0,[z512,z0,z2,z3,z4,z5,z6]),(0,[z144,z2,z3,z4,z88,z5,z6]),(0,[z0,z2,z513,z3,z4,z5,z6]),(1,[z0,z2,z3,z89,z5,z6]),(0,[z0,z2,z514,z3,z4,z5,z6]),(0,[z0,z361,z2,z3,z4,z5,z61]),(0,[z0,z2,z91,z3,z113,z5,z6]),(0,[z0,z2,z3,z309,z4,z5,z13])],[(0,[z0,z515,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z31,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z516,z3,z4,z5,z6]),(0,[z0,z2,z91,z3,z5,z126,z6]),(0,[z0,z517,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z518]),(0,[z0,z2,z3,z4,z5,z13,z13]),(0,[z0,z2,z3,z4,z5,z6,z519]),(1,[z0,z2,z3,z4,z46,z24])],[(0,[z144,z2,z3,z4,z5,z41,z6]),(0,[z102,z0,z2,z104,z4,z5,z6]),(0,[z0,z2,z520,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z521]),(0,[z144,z145,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z522,z6]),(0,[z0,z2,z3,z523,z4,z5,z6]),(0,[z0,z2,z3,z4,z524,z5,z6]),(0,[z0,z2,z48,z79,z3,z4,z6]),(0,[z383,z0,z2,z3,z4,z5,z24])],[(0,[z0,z2,z3,z4,z525,z5,z6]),(0,[z0,z526,z2,z3,z4,z5,z6]),(0,[z28,z0,z2,z3,z391,z5,z6]),(0,[z0,z361,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z527,z5,z6]),(0,[z97,z0,z2,z3,z4,z5,z52])],[(0,[z0,z2,z3,z4,z5,z122,z6]),(1,[z0,z2,z148,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z82,z6]),(0,[z200,z0,z2,z3,z4,z5,z24])],[(0,[z0,z2,z3,z528,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z529,z6]),(1,[z0,z2,z224,z3,z5,z6]),(0,[z0,z2,z3,z132,z4,z5,z13]),(0,[z0,z2,z3,z530,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z531,z5,z6]),(1,[z28,z0,z8,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z532,z6]),(0,[z0,z2,z533,z3,z4,z5,z6]),(0,[z81,z0,z2,z3,z4,z46,z6]),(0,[z0,z2,z48,z7,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z534,z6]),(0,[z535,z0,z2,z3,z4,z5,z6])],[(0,[z144,z0,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z104,z4,z5,z6]),(0,[z0,z2,z3,z536,z4,z5,z6]),(0,[z28,z0,z2,z3,z402,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z537]),(0,[z0,z2,z3,z113,z4,z5,z6]),(0,[z333,z0,z2,z3,z4,z5,z13])],[(0,[z0,z2,z3,z4,z88,z5,z24]),(0,[z0,z2,z7,z92,z4,z5,z6]),(0,[z0,z2,z79,z343,z4,z5,z6])],[(0,[z0,z2,z3,z88,z5,z47,z6]),(0,[z0,z2,z51,z3,z4,z5,z6]),(0,[z0,z2,z538,z3,z4,z5,z6]),(0,[z12,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z46,z24,z6])],[(0,[z0,z2,z539,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z540]),(0,[z0,z2,z3,z4,z5,z293,z6]),(0,[z200,z0,z2,z3,z4,z5,z61]),(0,[z0,z2,z113,z4,z5,z163,z6]),(0,[z0,z2,z3,z541,z4,z5,z6])],[(0,[z0,z145,z2,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z24,z166]),(0,[z168,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z7,z113,z4,z5,z6]),(0,[z542,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z57,z4,z5,z6]),(1,[z12,z0,z2,z3,z4,z13])],[(0,[z0,z2,z3,z4,z543,z5,z6]),(0,[z121,z0,z226,z3,z4,z5,z6]),(0,[z0,z2,z92,z3,z4,z5,z6]),(0,[z544,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z66,z5,z6]),(0,[z0,z2,z545,z3,z4,z5,z6]),(0,[z0,z546,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z547,z6]),(0,[z0,z2,z3,z4,z5,z548,z6]),(0,[z0,z2,z3,z4,z5,z199,z6]),(0,[z0,z2,z3,z4,z549,z5,z6]),(0,[z0,z2,z3,z4,z550,z5,z6]),(0,[z0,z2,z551,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z47,z13])]],
   [[(0,[z121,z0,z2,z3,z4,z161,z6]),(0,[z0,z2,z552,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z38,z13]),(0,[z553,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z95,z4,z163,z6]),(0,[z0,z2,z79,z3,z4,z5,z11])],[(0,[z0,z2,z3,z554,z4,z5,z6]),(0,[z0,z2,z3,z4,z555,z5,z6]),(0,[z0,z2,z3,z4,z205,z5,z6]),(0,[z0,z2,z91,z83,z4,z5,z6])],[(0,[z556,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z557,z6]),(1,[z0,z2,z29,z3,z5,z6]),(0,[z0,z2,z3,z77,z4,z205,z6]),(0,[z0,z2,z558,z3,z4,z5,z6])],[(0,[z133,z144,z2,z3,z4,z5,z6]),(0,[z559,z0,z2,z3,z4,z5,z6]),(0,[z121,z0,z2,z3,z4,z5,z560]),(0,[z81,z125,z2,z3,z4,z5,z6]),(0,[z561,z0,z2,z3,z4,z5,z6]),(1,[z97,z0,z2,z4,z5,z17]),(0,[z0,z2,z3,z343,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z562,z6]),(0,[z0,z145,z2,z3,z4,z5,z468]),(0,[z0,z2,z3,z4,z563,z5,z6]),(0,[z27,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z402,z5,z6]),(0,[z0,z65,z2,z91,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z564,z6]),(0,[z0,z374,z2,z3,z4,z5,z13])],[(0,[z0,z2,z3,z4,z5,z565,z6]),(0,[z97,z40,z0,z2,z3,z4,z5]),(0,[z0,z2,z91,z4,z5,z163,z6]),(0,[z0,z2,z3,z4,z5,z24,z17])],[(0,[z566,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z567,z4,z5,z6]),(0,[z81,z0,z139,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z568,z6])]],
   [[(0,[z0,z2,z569,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z152]),(0,[z0,z2,z3,z77,z118,z5,z6]),(0,[z0,z2,z3,z4,z5,z76,z6]),(0,[z0,z2,z3,z4,z5,z570,z6])],[(0,[z571,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z157,z4,z5,z6,z17]),(0,[z0,z2,z79,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z572,z6]),(0,[z0,z2,z3,z4,z5,z163,z24]),(1,[z0,z2,z3,z4,z5,z316])],[(0,[z0,z130,z2,z3,z4,z5,z6]),(0,[z0,z2,z573,z3,z4,z5,z6]),(1,[z169,z2,z3,z4,z5,z6])],[(1,[z30,z2,z3,z31,z5,z6]),(0,[z121,z37,z2,z3,z4,z5,z6]),(0,[z200,z0,z2,z3,z4,z5,z13]),(0,[z389,z0,z2,z3,z4,z5,z13])],[(1,[z0,z2,z3,z4,z129,z6])],[(0,[z0,z2,z3,z574,z4,z5,z6]),(0,[z575,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z95,z3,z4,z163,z6]),(0,[z0,z2,z3,z4,z5,z24,z52]),(0,[z49,z0,z2,z3,z4,z453,z6]),(0,[z49,z0,z2,z3,z5,z6,z58]),(0,[z0,z2,z3,z4,z5,z446,z24])],[(0,[z0,z2,z3,z4,z5,z576,z6])],[(0,[z71,z0,z2,z3,z4,z5,z6]),(0,[z577,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z469,z3,z4,z5,z6]),(0,[z28,z0,z2,z3,z4,z5,z176]),(0,[z0,z2,z95,z3,z77,z4,z6]),(0,[z0,z2,z3,z4,z5,z578,z6]),(0,[z0,z2,z3,z5,z9,z6,z58]),(0,[z0,z2,z3,z4,z5,z6,z579])],[(0,[z580,z0,z2,z3,z4,z5,z6]),(0,[z581,z0,z2,z3,z4,z5,z6]),(1,[z505,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z582]),(0,[z0,z2,z3,z4,z5,z6,z583]),(0,[z584,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z585]),(1,[z0,z2,z3,z4,z5,z490]),(0,[z0,z2,z3,z586,z4,z5,z6]),(0,[z587,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z588,z5,z6]),(0,[z147,z2,z3,z4,z88,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z560]),(0,[z0,z2,z3,z4,z589,z5,z6]),(0,[z0,z2,z3,z192,z4,z5,z6]),(0,[z0,z590,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z24])],[(0,[z591,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z372,z6]),(0,[z0,z2,z95,z4,z5,z163,z6])],[(0,[z0,z2,z3,z66,z5,z47,z6]),(0,[z200,z0,z361,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z46,z5,z24])],[(0,[z0,z2,z592,z3,z4,z5,z6]),(0,[z0,z2,z593,z3,z4,z5,z6])],[(0,[z147,z30,z2,z3,z4,z5,z6]),(0,[z594,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z595,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z596,z6]),(0,[z0,z2,z3,z4,z5,z98,z6]),(0,[z0,z2,z3,z4,z5,z597,z6])],[(0,[z505,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z48,z3,z4,z47,z6]),(0,[z0,z2,z3,z4,z5,z433,z13]),(0,[z0,z2,z598,z3,z4,z5,z6])]],
   [[(0,[z81,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z599,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z600,z6])],[(0,[z601,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z602]),(0,[z0,z2,z603,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z468]),(0,[z147,z0,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z38,z5,z240]),(0,[z0,z2,z3,z4,z604,z5,z6])],[(0,[z0,z2,z605,z3,z4,z5,z6]),(0,[z0,z2,z3,z267,z4,z5,z6]),(1,[z0,z2,z3,z45,z5,z6]),(0,[z168,z0,z2,z3,z4,z366,z6]),(0,[z0,z65,z2,z7,z3,z5,z6]),(0,[z0,z2,z606,z3,z4,z5,z6]),(0,[z0,z607,z2,z3,z4,z5,z6])],[(0,[z28,z0,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z132,z4,z5,z316]),(0,[z49,z0,z2,z3,z4,z56,z6])],[(0,[z133,z0,z110,z3,z4,z5,z6]),(0,[z608,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z157,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z6,z166]),(0,[z40,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z113,z66,z5,z6]),(0,[z0,z2,z3,z113,z107,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z609])],[(0,[z168,z0,z2,z3,z4,z372,z6]),(0,[z0,z2,z3,z4,z5,z425,z6])],[(0,[z0,z610,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z611,z6]),(0,[z0,z139,z2,z3,z4,z205,z6]),(0,[z0,z2,z3,z4,z5,z6,z612]),(0,[z0,z2,z3,z4,z5,z613,z6])]],
   [[(1,[z0,z2,z149,z4,z5,z6]),(0,[z0,z2,z614,z3,z4,z5,z6]),(0,[z0,z2,z158,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z615,z6])],[(0,[z0,z2,z3,z616,z4,z5,z6]),(0,[z0,z2,z3,z4,z617,z5,z6]),(0,[z168,z0,z2,z3,z107,z5,z6]),(0,[z168,z0,z2,z3,z66,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z96]),(1,[z0,z2,z3,z118,z5,z6])],[(0,[z618,z0,z2,z3,z4,z5,z6]),(0,[z619,z0,z2,z3,z4,z5,z6]),(0,[z620,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z519,z13])],[(0,[z133,z0,z145,z3,z4,z5,z6]),(0,[z121,z0,z2,z3,z21,z5,z6]),(0,[z0,z2,z3,z4,z621,z5,z6]),(0,[z622,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z623]),(0,[z624,z0,z2,z3,z4,z5,z6])],[(0,[z27,z2,z110,z3,z4,z5,z6]),(0,[z121,z0,z26,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z23,z13]),(0,[z0,z2,z3,z132,z4,z5,z490])],[(0,[z0,z2,z3,z4,z625,z5,z6]),(0,[z626,z0,z2,z3,z4,z5,z6]),(0,[z168,z395,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z108,z5,z6]),(0,[z0,z2,z3,z132,z4,z5,z24]),(0,[z627,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z240]),(0,[z0,z2,z3,z628,z4,z5,z6]),(1,[z0,z2,z3,z4,z78,z6]),(0,[z0,z2,z3,z4,z5,z6,z17]),(0,[z0,z2,z3,z629,z4,z5,z6]),(0,[z0,z2,z630,z3,z4,z5,z6]),(0,[z0,z2,z79,z3,z4,z5,z459])],[(0,[z144,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z104,z4,z5,z163,z6]),(0,[z0,z2,z3,z4,z5,z6,z631]),(0,[z0,z2,z632,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z633]),(0,[z0,z2,z231,z3,z4,z5,z6]),(0,[z0,z2,z95,z3,z4,z5,z407]),(0,[z0,z634,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z479])]],
   [[(0,[z0,z635,z2,z3,z4,z5,z6])],[(0,[z0,z2,z636,z3,z4,z5,z6]),(0,[z0,z637,z2,z3,z4,z5,z6]),(0,[z30,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z638]),(0,[z0,z2,z461,z3,z4,z5,z13])],[(0,[z0,z2,z3,z639,z4,z5,z6]),(0,[z0,z2,z3,z640,z4,z5,z6]),(0,[z0,z2,z3,z641,z4,z5,z6])],[(0,[z0,z2,z3,z4,z642,z5,z6]),(0,[z0,z2,z3,z31,z5,z6,z58]),(1,[z49,z0,z2,z3,z5,z58])],[(0,[z168,z0,z2,z3,z4,z5,z93]),(1,[z0,z2,z91,z5,z126,z6]),(0,[z0,z2,z3,z4,z5,z24,z9])],[(0,[z0,z2,z3,z4,z5,z643,z6]),(1,[z0,z226,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z644,z5,z6])],[(0,[z28,z0,z2,z8,z4,z5,z6]),(0,[z331,z0,z2,z3,z4,z5,z6]),(0,[z0,z361,z2,z3,z4,z5,z24])],[(0,[z645,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z87,z5]),(0,[z40,z0,z2,z3,z4,z5,z61]),(0,[z49,z0,z2,z3,z4,z5,z9])]],
   [[(0,[z0,z2,z3,z4,z646,z5,z6]),(0,[z0,z2,z79,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z647,z6])],[(0,[z0,z2,z648,z3,z4,z5,z6]),(0,[z649,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z650,z3,z4,z5,z6]),(0,[z651,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z339,z6]),(0,[z0,z2,z83,z77,z4,z5,z6]),(0,[z0,z2,z83,z3,z4,z5,z13])],[(0,[z0,z2,z3,z4,z5,z652,z6]),(0,[z168,z0,z2,z3,z4,z5,z425])],[(1,[z0,z2,z3,z4,z5,z560]),(0,[z0,z2,z3,z4,z46,z163,z6])],[(0,[z102,z0,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z6,z653]),(0,[z168,z0,z3,z4,z66,z5,z6]),(0,[z0,z2,z3,z654,z4,z5,z6]),(0,[z655,z0,z2,z3,z4,z5,z6]),(0,[z97,z0,z2,z4,z5,z6,z17]),(0,[z656,z0,z2,z3,z4,z5,z6])],[(0,[z0,z110,z3,z4,z5,z6,z61]),(0,[z0,z2,z3,z4,z5,z657,z6]),(0,[z0,z2,z3,z4,z89,z5,z6]),(0,[z0,z2,z3,z107,z4,z5,z13]),(0,[z0,z2,z658,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z659,z6]),(0,[z0,z2,z3,z4,z660,z5,z6]),(0,[z0,z2,z3,z4,z205,z5,z426])],[(0,[z661,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z41,z6,z166]),(0,[z0,z2,z3,z4,z66,z5,z24]),(0,[z0,z2,z662,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z663,z6]),(0,[z0,z2,z3,z4,z5,z6,z664]),(0,[z0,z2,z48,z3,z132,z5,z6]),(0,[z364,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z665,z3,z4,z5,z6]),(0,[z0,z2,z3,z666,z4,z5,z6]),(0,[z667,z0,z2,z3,z4,z5,z6]),(0,[z40,z2,z3,z4,z5,z41,z6]),(1,[z0,z2,z3,z4,z243,z6]),(0,[z668,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z444])],[(0,[z669,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z48,z3,z66,z5,z6]),(0,[z0,z2,z48,z3,z107,z5,z6]),(0,[z242,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z243,z10,z6]),(0,[z0,z2,z48,z79,z3,z5,z6]),(0,[z389,z0,z2,z3,z4,z5,z24])],[(0,[z147,z0,z2,z3,z31,z5,z6]),(1,[z0,z2,z3,z4,z161,z13]),(0,[z0,z2,z3,z4,z38,z6,z13]),(0,[z175,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z170,z6]),(0,[z670,z0,z2,z3,z4,z5,z6]),(0,[z394,z0,z2,z3,z4,z5,z24])],[(1,[z175,z2,z3,z4,z5,z6])],[(0,[z0,z2,z91,z3,z5,z47,z6])],[(0,[z0,z2,z3,z671,z4,z5,z6]),(0,[z0,z2,z672,z3,z4,z5,z6]),(0,[z0,z2,z3,z673,z4,z5,z6]),(0,[z97,z0,z2,z3,z4,z5,z6])],[(0,[z674,z0,z2,z3,z4,z5,z6]),(0,[z40,z0,z2,z3,z4,z5,z13]),(0,[z0,z2,z7,z3,z4,z5,z13]),(0,[z0,z2,z83,z3,z77,z4,z6]),(0,[z0,z2,z3,z4,z5,z17,z13])],[(0,[z81,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z24,z10]),(0,[z675,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z77,z4,z13]),(0,[z0,z2,z3,z4,z676,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z13,z582]),(0,[z0,z2,z3,z4,z5,z5,z13])],[(1,[z0,z2,z7,z113,z5,z6])],[(0,[z0,z2,z3,z677,z4,z5,z6]),(0,[z0,z2,z83,z157,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z678])],[(0,[z679,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z83,z8,z4,z5,z6]),(1,[z0,z2,z275,z4,z5,z6]),(0,[z0,z361,z2,z3,z4,z5,z13]),(0,[z97,z0,z2,z158,z4,z5,z6]),(0,[z0,z680,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z681])],[(0,[z27,z0,z2,z3,z4,z5,z61]),(0,[z0,z2,z3,z4,z5,z682,z6]),(0,[z0,z2,z3,z77,z4,z5,z76])],[(0,[z102,z0,z2,z157,z4,z5,z6]),(0,[z0,z2,z3,z4,z163,z6,z13])],[(0,[z683,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z684,z4,z5,z6]),(0,[z0,z2,z3,z685,z4,z5,z6])],[(0,[z0,z2,z3,z104,z4,z5,z13]),(0,[z0,z2,z686,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z183]),(0,[z0,z2,z3,z113,z4,z5,z13]),(0,[z687,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z24,z13])]],
   [[(0,[z102,z2,z110,z3,z4,z5,z6]),(0,[z30,z2,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z271]),(0,[z71,z0,z2,z3,z4,z5,z24]),(0,[z688,z0,z2,z3,z4,z5,z6]),(0,[z147,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z161,z6])],[(0,[z0,z2,z689,z3,z4,z5,z6]),(0,[z0,z2,z690,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z691]),(0,[z0,z2,z3,z4,z5,z692,z6])],[(0,[z133,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z693,z3,z4,z5,z6]),(0,[z274,z0,z2,z3,z4,z5,z6]),(0,[z28,z0,z2,z3,z4,z5,z24])],[(0,[z694,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z157,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z166,z13]),(0,[z168,z0,z2,z3,z4,z5,z13]),(0,[z695,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z407]),(0,[z0,z2,z277,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z453,z6]),(0,[z0,z2,z3,z57,z4,z5,z13])],[(0,[z696,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z697,z4,z5,z6]),(0,[z0,z2,z3,z8,z4,z5,z6]),(0,[z0,z2,z3,z698,z4,z5,z6]),(0,[z0,z2,z92,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z366,z5,z6]),(0,[z0,z2,z3,z4,z66,z5,z13]),(0,[z699,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z61,z13])],[(0,[z0,z2,z3,z31,z5,z47,z6]),(1,[z0,z2,z3,z4,z6,z120]),(0,[z0,z2,z280,z3,z4,z5,z6])],[(0,[z0,z2,z3,z700,z4,z5,z6]),(0,[z0,z2,z701,z3,z4,z5,z6]),(0,[z121,z0,z2,z204,z4,z5,z6]),(0,[z27,z40,z2,z3,z4,z5,z6]),(0,[z27,z0,z469,z3,z4,z5,z6]),(0,[z702,z0,z2,z3,z4,z5,z6]),(1,[z0,z139,z3,z4,z205,z6]),(0,[z0,z2,z3,z703,z4,z5,z6]),(0,[z0,z2,z3,z77,z4,z6,z13]),(0,[z0,z2,z704,z3,z4,z5,z6])],[(0,[z0,z2,z3,z705,z4,z5,z6]),(0,[z144,z37,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z706,z6]),(0,[z0,z2,z3,z4,z205,z5,z13])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z2,z3,z4,z707,z6]),(0,[z0,z2,z708,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z152]),(0,[z237,z0,z139,z3,z4,z13]),(0,[z0,z2,z3,z4,z663,z13])],[(0,[z0,z2,z3,z709,z5,z6]),(0,[z81,z0,z275,z4,z23,z6])],[(0,[z203,z0,z2,z3,z4,z710]),(0,[z0,z2,z3,z4,z711,z13]),(0,[z169,z2,z3,z4,z372,z6]),(0,[z712,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z713]),(0,[z0,z2,z3,z4,z5,z714]),(0,[z49,z0,z2,z3,z5,z58])],[(0,[z49,z0,z2,z3,z5,z164]),(0,[z0,z715,z3,z4,z5,z6])],[(0,[z0,z469,z3,z4,z5,z13]),(0,[z0,z65,z131,z3,z5,z6]),(0,[z81,z0,z2,z3,z4,z716]),(0,[z717,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z718,z5,z6]),(0,[z0,z2,z3,z719,z5,z6]),(0,[z0,z361,z3,z4,z5,z468]),(0,[z0,z2,z3,z4,z330,z24])],[(0,[z37,z2,z3,z4,z119,z6]),(0,[z0,z2,z3,z4,z170,z720]),(0,[z0,z2,z3,z721,z5,z6]),(0,[z0,z2,z7,z135,z5,z6])],[(0,[z0,z2,z3,z89,z5,z61]),(0,[z0,z2,z3,z4,z5,z722])],[(0,[z0,z2,z3,z4,z5,z723]),(0,[z0,z2,z724,z4,z5,z6]),(0,[z54,z0,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z78,z13]),(0,[z0,z2,z3,z4,z56,z58]),(0,[z0,z2,z3,z4,z604,z13])],[(0,[z0,z2,z3,z4,z725,z6]),(0,[z0,z2,z726,z4,z5,z6]),(0,[z0,z2,z3,z4,z372,z727]),(0,[z0,z2,z728,z4,z5,z6]),(0,[z0,z139,z3,z4,z729,z6])],[(0,[z730,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z560]),(0,[z0,z245,z3,z4,z5,z10]),(0,[z0,z635,z2,z3,z4,z13])],[(0,[z731,z0,z2,z3,z4,z5]),(0,[z0,z2,z239,z3,z4,z13]),(0,[z0,z2,z3,z4,z5,z732]),(0,[z0,z2,z3,z4,z733,z6]),(0,[z0,z2,z343,z4,z205,z6])],[(0,[z0,z734,z3,z4,z5,z6]),(0,[z0,z2,z39,z4,z5,z13])],[(0,[z0,z2,z3,z4,z5,z735]),(0,[z0,z2,z3,z4,z5,z736])],[(0,[z0,z2,z142,z4,z5,z13]),(0,[z0,z3,z4,z5,z737,z61]),(0,[z738,z0,z2,z3,z4,z5])],[(0,[z0,z226,z3,z4,z5,z13])]],
   [[(0,[z0,z2,z3,z4,z170,z176]),(0,[z0,z2,z3,z4,z5,z739]),(0,[z0,z2,z95,z4,z163,z24]),(0,[z0,z2,z3,z4,z98,z339])],[(0,[z0,z2,z3,z4,z740,z6]),(0,[z0,z2,z3,z4,z741,z6]),(0,[z0,z2,z3,z4,z161,z13]),(0,[z175,z2,z3,z4,z5,z176]),(0,[z0,z2,z3,z4,z5,z742])],[],[],[(0,[z125,z2,z3,z4,z5,z16]),(0,[z0,z2,z3,z4,z743,z6]),(0,[z0,z2,z3,z4,z46,z76])],[(0,[z0,z2,z267,z21,z5,z6]),(0,[z242,z245,z3,z4,z5,z6]),(0,[z0,z2,z744,z4,z5,z6]),(0,[z0,z2,z3,z115,z5,z13])],[(0,[z144,z730,z3,z4,z5,z6]),(0,[z0,z26,z267,z4,z5,z6]),(0,[z0,z2,z3,z89,z5,z13]),(0,[z0,z2,z3,z4,z5,z745]),(0,[z0,z2,z48,z79,z343,z6])],[(0,[z505,z0,z2,z3,z89,z5]),(0,[z0,z2,z3,z4,z5,z746]),(0,[z0,z139,z3,z4,z205,z426]),(0,[z0,z2,z3,z4,z120,z13]),(0,[z747,z2,z3,z4,z5,z6]),(0,[z0,z546,z2,z3,z4,z13])],[(0,[z0,z139,z110,z3,z4,z13]),(0,[z0,z2,z3,z4,z5,z748]),(0,[z0,z65,z3,z107,z5,z6]),(0,[z0,z2,z91,z3,z372,z6]),(0,[z0,z2,z7,z113,z5,z6])],[(0,[z0,z2,z3,z4,z749,z6]),(0,[z0,z2,z3,z4,z5,z96]),(0,[z0,z2,z3,z4,z273,z13])],[(0,[z0,z2,z750,z4,z5,z6]),(1,[z2,z751,z4,z5,z6]),(0,[z0,z2,z3,z4,z646,z13]),(0,[z0,z26,z3,z134,z5,z6]),(0,[z0,z2,z275,z4,z5,z6]),(0,[z169,z2,z3,z4,z5,z24]),(0,[z0,z2,z752,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z753]),(0,[z0,z2,z3,z4,z243,z13]),(0,[z754,z2,z3,z4,z5,z6])],[(0,[z27,z2,z3,z4,z5,z508])],[(0,[z97,z0,z2,z39,z4,z5])],[(0,[z144,z245,z3,z4,z5,z6]),(0,[z505,z0,z2,z3,z5,z58]),(0,[z0,z2,z92,z4,z163,z13]),(0,[z0,z2,z3,z755,z5,z6]),(0,[z0,z2,z756,z4,z5,z24])],[(0,[z0,z2,z757,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z758]),(0,[z0,z2,z3,z4,z33,z13])],[]],
   [[(0,[z0,z2,z520,z4,z163,z6]),(0,[z0,z2,z113,z4,z163,z13])],[(0,[z0,z2,z3,z4,z5,z759]),(0,[z0,z2,z83,z77,z4,z6])],[(0,[z0,z2,z3,z4,z129,z61]),(1,[z0,z2,z3,z118,z13]),(0,[z0,z2,z343,z4,z46,z6])],[(0,[z364,z2,z3,z4,z5,z41]),(0,[z0,z2,z3,z405,z4,z13])],[(0,[z0,z2,z3,z4,z5,z760]),(0,[z761,z2,z3,z4,z5,z6]),(0,[z0,z2,z762,z4,z5,z6])],[(0,[z147,z2,z3,z87,z88,z5]),(0,[z27,z295,z2,z3,z4,z5]),(0,[z2,z763,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z764])],[],[(0,[z0,z2,z3,z4,z5,z765]),(0,[z130,z2,z3,z402,z5,z6])],[(0,[z0,z2,z29,z3,z5,z13]),(0,[z97,z0,z2,z4,z78,z17]),(0,[z0,z2,z159,z4,z5,z11])],[(0,[z0,z2,z3,z766,z4,z6]),(0,[z626,z0,z2,z3,z4,z13]),(0,[z0,z2,z422,z79,z3,z6]),(0,[z0,z2,z3,z309,z5,z58])],[(0,[z0,z2,z3,z4,z5,z122]),(0,[z0,z2,z3,z57,z89,z5]),(0,[z97,z0,z2,z3,z4,z129]),(0,[z0,z2,z767,z4,z5,z6])],[(0,[z768,z2,z3,z4,z5,z6]),(0,[z0,z2,z158,z4,z5,z52]),(0,[z0,z769,z3,z4,z5,z24])],[(0,[z0,z2,z3,z770,z5,z6]),(0,[z0,z261,z2,z3,z4,z13]),(0,[z0,z2,z3,z4,z6,z771]),(0,[z0,z2,z3,z4,z106,z13]),(0,[z0,z2,z3,z4,z5,z772])],[(0,[z0,z2,z773,z4,z5,z6]),(0,[z0,z2,z224,z3,z5,z444]),(0,[z0,z2,z3,z4,z453,z13])],[(0,[z0,z2,z7,z3,z372,z6])],[(0,[z0,z2,z774,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z775,z5,z6]),(0,[z30,z2,z3,z31,z5,z13]),(0,[z0,z2,z3,z776,z5,z6]),(0,[z28,z0,z8,z4,z170,z6]),(0,[z0,z2,z441,z3,z4,z13]),(0,[z0,z2,z149,z4,z5,z24]),(0,[z0,z2,z777,z4,z5,z6]),(0,[z0,z2,z3,z108,z5,z16]),(0,[z0,z139,z3,z4,z205,z13]),(0,[z276,z0,z2,z91,z5,z6])],[(0,[z102,z2,z157,z4,z5,z6]),(0,[z0,z2,z3,z4,z129,z13]),(0,[z2,z3,z4,z5,z6,z778])],[(0,[z505,z0,z2,z3,z4,z749]),(0,[z168,z0,z2,z75,z5,z6]),(1,[z0,z2,z275,z4,z13]),(0,[z0,z2,z3,z4,z136,z13])],[(0,[z40,z0,z2,z3,z4,z98]),(0,[z0,z2,z779,z4,z5,z6]),(0,[z0,z125,z2,z3,z4,z13])],[(0,[z0,z2,z3,z780,z4,z5]),(0,[z0,z2,z3,z781,z5,z6]),(0,[z0,z2,z3,z4,z5,z73]),(0,[z0,z2,z3,z4,z366,z93]),(0,[z0,z2,z83,z77,z118,z6])],[(0,[z0,z2,z3,z4,z642,z13]),(0,[z395,z2,z192,z4,z5,z6]),(0,[z2,z782,z3,z4,z5,z6])],[(0,[z179,z0,z2,z3,z4,z13]),(0,[z0,z2,z3,z4,z5,z783])],[(0,[z0,z145,z139,z3,z4,z13]),(0,[z2,z3,z4,z161,z36,z13]),(0,[z0,z469,z3,z4,z55,z6]),(0,[z784,z2,z3,z4,z5,z6])],[(0,[z37,z2,z3,z4,z38,z13]),(0,[z0,z2,z3,z4,z785,z6]),(0,[z0,z2,z142,z4,z5,z16]),(0,[z0,z2,z3,z4,z786,z6])],[(0,[z0,z2,z787,z4,z5,z6]),(0,[z125,z2,z3,z4,z46,z6])],[(0,[z0,z2,z3,z4,z366,z425]),(0,[z699,z0,z2,z3,z4,z13]),(0,[z0,z2,z788,z3,z4,z5]),(1,[z0,z2,z3,z5,z789]),(0,[z0,z2,z270,z3,z4,z13])],[(0,[z561,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z790,z5,z6]),(0,[z242,z145,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z791,z6])],[(0,[z0,z2,z3,z792,z5,z6]),(0,[z0,z2,z793,z4,z5,z6]),(0,[z0,z2,z91,z5,z126,z24])],[(0,[z0,z2,z3,z794,z5,z6])],[(0,[z130,z2,z3,z4,z5,z176]),(0,[z0,z2,z3,z108,z205,z6])],[(0,[z0,z2,z3,z4,z5,z795]),(0,[z0,z2,z39,z4,z55,z6]),(0,[z0,z2,z3,z115,z5,z16])]],
   [[(0,[z0,z2,z3,z4,z5,z796]),(0,[z0,z2,z3,z45,z5,z13]),(0,[z0,z2,z3,z4,z5,z797]),(0,[z0,z2,z3,z4,z5,z798])],[(0,[z0,z2,z3,z4,z5,z799]),(0,[z0,z2,z441,z4,z163,z6]),(0,[z0,z2,z3,z4,z187,z13])],[(0,[z2,z3,z4,z38,z161,z13]),(0,[z395,z2,z231,z4,z5,z6]),(0,[z0,z2,z3,z4,z98,z17])],[(0,[z144,z145,z3,z4,z5,z6]),(0,[z0,z2,z3,z103,z4,z5]),(0,[z147,z2,z3,z88,z5,z6]),(0,[z30,z2,z3,z792,z5,z6]),(0,[z0,z2,z83,z4,z483,z6])],[(0,[z0,z2,z800,z3,z4,z6]),(0,[z0,z2,z204,z134,z5,z6]),(0,[z0,z2,z801,z3,z4,z5])],[(0,[z0,z802,z3,z4,z5,z6]),(0,[z803,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z804]),(0,[z0,z90,z92,z4,z5,z6]),(0,[z0,z2,z48,z79,z3,z6])],[(0,[z0,z2,z805,z4,z5,z6]),(0,[z0,z2,z658,z3,z4,z13]),(0,[z0,z2,z48,z79,z3,z459]),(0,[z0,z806,z3,z4,z5,z6])],[(0,[z0,z807,z3,z4,z5,z6]),(0,[z0,z469,z128,z4,z5,z6]),(0,[z0,z2,z3,z4,z366,z6]),(0,[z361,z51,z3,z4,z5,z10]),(0,[z808,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z89,z55,z6]),(0,[z0,z2,z3,z4,z129,z41]),(0,[z130,z2,z3,z4,z293,z6])],[(0,[z2,z3,z751,z4,z5,z6]),(0,[z0,z2,z809,z3,z4,z5]),(0,[z0,z2,z3,z4,z170,z24])],[(0,[z175,z2,z3,z4,z5,z24])],[(0,[z0,z2,z3,z4,z810,z6]),(0,[z242,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z811,z13])],[(0,[z27,z469,z3,z4,z5,z166]),(0,[z0,z2,z3,z132,z47,z6]),(0,[z333,z2,z3,z4,z5,z582])],[(0,[z0,z2,z3,z4,z812,z6]),(1,[z0,z3,z813,z5,z6])]],
   [[(0,[z0,z2,z814,z4,z5,z6]),(0,[z0,z2,z3,z815,z5,z6])],[(0,[z816,z2,z3,z4,z5,z6]),(0,[z0,z715,z3,z4,z5,z13])],[(0,[z0,z2,z3,z4,z5,z817]),(0,[z168,z0,z192,z66,z5,z6]),(0,[z0,z2,z224,z3,z5,z76])],[(0,[z0,z2,z3,z4,z5,z818]),(0,[z200,z0,z3,z4,z5,z61])],[(0,[z0,z2,z3,z819,z5,z6]),(0,[z81,z0,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z820,z6]),(0,[z0,z2,z3,z47,z479,z13])],[(0,[z0,z2,z3,z821,z5,z6]),(0,[z0,z2,z3,z822,z5,z6]),(0,[z0,z2,z3,z108,z46,z6])],[(0,[z0,z823,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z824,z6]),(0,[z27,z2,z39,z4,z5,z166]),(0,[z0,z2,z3,z4,z5,z825]),(0,[z0,z2,z3,z4,z826,z6]),(0,[z0,z2,z3,z4,z163,z13])],[(0,[z0,z2,z79,z3,z4,z13]),(0,[z0,z2,z3,z4,z24,z811])],[(0,[z121,z2,z3,z4,z161,z6]),(0,[z121,z2,z3,z4,z161,z122]),(0,[z0,z2,z3,z4,z827,z6]),(0,[z0,z2,z280,z4,z163,z6])],[(0,[z0,z2,z3,z4,z5,z93])],[(0,[z0,z2,z828,z3,z5,z6]),(0,[z0,z2,z3,z4,z829,z6]),(0,[z0,z2,z830,z3,z5,z6]),(0,[z0,z2,z3,z4,z446,z13])],[(0,[z0,z2,z3,z4,z5,z831]),(0,[z0,z2,z3,z66,z47,z13]),(0,[z0,z2,z3,z77,z4,z152])],[(0,[z0,z2,z3,z4,z6,z832])],[],[(0,[z203,z2,z110,z3,z4,z5]),(0,[z244,z2,z3,z88,z5,z6]),(0,[z168,z0,z75,z66,z5,z6]),(0,[z168,z0,z382,z3,z5,z6])],[(0,[z0,z2,z3,z4,z266,z13]),(0,[z0,z2,z3,z4,z38,z711]),(0,[z168,z395,z3,z66,z5,z6]),(0,[z0,z2,z3,z4,z5,z425]),(0,[z168,z0,z231,z66,z5,z6]),(0,[z0,z2,z91,z4,z163,z13])]],
   [[(0,[z0,z2,z3,z60,z4,z13]),(0,[z27,z2,z3,z89,z5,z166]),(0,[z0,z2,z3,z833,z5,z6]),(0,[z242,z361,z3,z4,z5,z10]),(0,[z0,z2,z343,z4,z5,z11]),(0,[z0,z2,z3,z834,z5,z6])],[(0,[z0,z2,z835,z3,z4,z6])],[(0,[z203,z144,z2,z3,z4,z5]),(0,[z0,z2,z836,z4,z5,z6]),(0,[z0,z2,z3,z21,z5,z24]),(0,[z0,z2,z29,z83,z5,z6])],[(0,[z0,z2,z837,z4,z5,z6]),(0,[z0,z26,z3,z4,z5,z24]),(0,[z0,z361,z3,z4,z10,z120])],[(0,[z0,z139,z2,z3,z4,z13])],[(0,[z0,z2,z158,z39,z4,z5]),(0,[z838,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z284,z13]),(0,[z0,z2,z3,z241,z47,z6]),(0,[z747,z2,z3,z4,z5,z13])],[(0,[z130,z2,z3,z391,z5,z6]),(0,[z0,z65,z3,z107,z5,z13]),(0,[z0,z2,z7,z113,z5,z13])],[(0,[z0,z2,z3,z4,z5,z839])],[(0,[z0,z2,z3,z4,z5,z840]),(0,[z2,z751,z104,z4,z5,z6]),(0,[z0,z2,z275,z4,z5,z13])],[(0,[z0,z2,z841,z4,z5,z6]),(0,[z0,z2,z3,z4,z842,z6]),(0,[z2,z51,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z843,z13])],[(0,[z0,z2,z3,z4,z55,z34]),(0,[z0,z2,z3,z4,z55,z24]),(0,[z0,z2,z3,z4,z56,z24])],[(0,[z0,z2,z3,z4,z5,z844]),(0,[z312,z0,z2,z3,z4,z13]),(0,[z0,z2,z32,z4,z5,z339])],[],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z311,z13]),(0,[z0,z2,z3,z4,z660,z13])],[(0,[z0,z2,z845,z4,z5,z6]),(0,[z0,z846,z3,z4,z5,z6]),(0,[z0,z2,z280,z4,z5,z17]),(0,[z0,z2,z3,z4,z5,z459])],[(0,[z0,z2,z83,z77,z4,z13])]],
   [[(0,[z0,z2,z847,z4,z5,z6]),(0,[z0,z2,z3,z848,z5,z6])],[(0,[z0,z245,z39,z4,z5,z6]),(1,[z0,z849,z4,z5,z6]),(0,[z0,z2,z192,z4,z372,z6]),(0,[z0,z2,z606,z3,z4,z13])],[(0,[z0,z2,z3,z850,z5,z6]),(0,[z263,z2,z3,z4,z5,z82])],[(0,[z0,z2,z3,z45,z55,z6]),(0,[z0,z2,z158,z3,z4,z129]),(0,[z395,z2,z3,z4,z372,z6]),(1,[z0,z3,z4,z5,z737])],[(0,[z102,z2,z430,z4,z5,z6]),(0,[z0,z2,z192,z107,z5,z6]),(0,[z0,z2,z4,z5,z6,z851]),(0,[z852,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z77,z4,z96]),(0,[z0,z2,z3,z118,z5,z24])],[(0,[z0,z2,z83,z640,z4,z6])],[(0,[z0,z2,z3,z4,z5,z853]),(0,[z0,z2,z3,z4,z293,z176]),(0,[z263,z2,z3,z108,z5,z6])],[(0,[z30,z2,z3,z705,z5,z6]),(0,[z0,z854,z3,z4,z5,z6])],[(0,[z144,z2,z39,z4,z5,z6]),(0,[z130,z2,z3,z4,z5,z24]),(0,[z855,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z856]),(0,[z0,z857,z3,z4,z5,z6])],[(0,[z2,z3,z31,z792,z5,z6]),(0,[z0,z2,z3,z4,z858,z6]),(0,[z0,z2,z3,z4,z47,z13])],[(0,[z0,z245,z3,z89,z5,z6]),(0,[z0,z2,z128,z4,z5,z24]),(0,[z27,z2,z3,z4,z129,z166]),(0,[z0,z2,z3,z4,z5,z859]),(0,[z28,z0,z382,z4,z5,z6]),(0,[z0,z2,z83,z224,z5,z6])],[(0,[z0,z2,z860,z4,z5,z6]),(0,[z0,z2,z3,z4,z360,z13]),(0,[z0,z259,z2,z3,z4,z13])],[(0,[z0,z226,z3,z21,z5,z6]),(0,[z0,z2,z3,z4,z861,z6])],[(0,[z0,z862,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z863]),(0,[z0,z2,z231,z4,z372,z6]),(0,[z0,z2,z864,z4,z5,z6]),(0,[z263,z2,z142,z4,z5,z6]),(0,[z0,z2,z3,z4,z534,z13])],[(0,[z0,z145,z2,z3,z4,z771]),(0,[z102,z2,z157,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z865])]],
   [[],[(0,[z0,z2,z866,z4,z5,z6]),(0,[z27,z0,z2,z3,z4,z56]),(0,[z867,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z78,z76])],[(0,[z144,z2,z3,z89,z5,z6]),(0,[z0,z2,z3,z343,z4,z13]),(0,[z0,z2,z868,z4,z5,z6])],[(1,[z0,z2,z3,z4,z771]),(0,[z0,z2,z3,z57,z5,z494]),(0,[z0,z2,z3,z21,z5,z560]),(0,[z0,z2,z3,z4,z869,z5]),(0,[z0,z2,z95,z4,z163,z96]),(0,[z49,z0,z2,z3,z56,z58]),(0,[z2,z782,z3,z4,z5,z13])],[(0,[z214,z0,z2,z3,z4,z13]),(0,[z0,z2,z128,z45,z5,z6]),(0,[z0,z2,z3,z138,z47,z6]),(0,[z0,z2,z870,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z871]),(0,[z0,z3,z4,z813,z5,z6]),(0,[z263,z2,z3,z115,z5,z6])],[(0,[z872,z2,z3,z4,z5,z6]),(0,[z0,z2,z159,z4,z5,z24])],[(0,[z71,z2,z104,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z873]),(0,[z0,z2,z75,z402,z5,z6]),(0,[z0,z2,z3,z874,z47,z6])],[(0,[z28,z0,z148,z8,z5,z6]),(0,[z200,z0,z3,z4,z5,z318]),(0,[z0,z2,z4,z5,z52,z875])],[(0,[z27,z2,z3,z4,z5,z294]),(0,[z0,z2,z192,z4,z5,z24])],[(0,[z0,z2,z3,z4,z5,z876]),(0,[z620,z2,z3,z88,z5,z6]),(0,[z27,z2,z3,z45,z5,z166]),(0,[z0,z2,z3,z541,z4,z13])],[(0,[z505,z0,z2,z3,z4,z877]),(0,[z0,z2,z3,z4,z5,z878]),(0,[z125,z139,z3,z4,z5,z6])],[(0,[z0,z2,z267,z134,z5,z6])],[(0,[z0,z2,z204,z4,z5,z24]),(0,[z0,z2,z3,z4,z568,z13]),(0,[z0,z2,z3,z774,z4,z6]),(0,[z879,z2,z3,z4,z5,z6])],[],[(0,[z203,z0,z2,z39,z4,z5]),(0,[z0,z2,z3,z4,z372,z880]),(0,[z0,z2,z3,z4,z5,z881])]],
   [[(0,[z0,z2,z882,z4,z5,z6]),(0,[z168,z0,z3,z66,z372,z6])],[(0,[z144,z145,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z883]),(0,[z147,z2,z3,z88,z5,z13]),(0,[z0,z2,z91,z527,z5,z6]),(0,[z0,z2,z3,z4,z98,z6])],[(0,[z0,z2,z3,z884,z5,z6]),(0,[z0,z3,z107,z813,z5,z6]),(0,[z0,z2,z275,z4,z5,z16]),(0,[z0,z317,z3,z4,z205,z6])],[(0,[z0,z2,z3,z391,z5,z176]),(0,[z168,z0,z3,z813,z5,z6])],[(0,[z0,z2,z8,z4,z293,z6]),(0,[z0,z2,z3,z4,z46,z82]),(0,[z0,z2,z95,z4,z163,z6]),(0,[z0,z2,z48,z79,z3,z13])],[(0,[z885,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z170,z73]),(0,[z0,z2,z75,z4,z5,z24]),(0,[z0,z2,z3,z4,z362,z13]),(0,[z0,z806,z3,z4,z5,z13])],[(0,[z0,z2,z3,z4,z5,z886]),(0,[z0,z245,z3,z4,z129,z6]),(0,[z175,z2,z3,z4,z5,z73]),(0,[z28,z0,z8,z4,z293,z6]),(0,[z0,z2,z231,z4,z5,z24]),(0,[z0,z2,z3,z4,z366,z13])],[(0,[z27,z0,z2,z3,z4,z98]),(0,[z0,z2,z3,z402,z5,z176])],[(0,[z0,z2,z3,z4,z5,z887]),(0,[z276,z0,z3,z66,z5,z6]),(0,[z535,z0,z2,z3,z4,z13])],[(0,[z0,z2,z3,z4,z5,z888]),(0,[z0,z2,z3,z4,z889,z6])],[(0,[z0,z2,z3,z4,z5,z890]),(0,[z0,z2,z3,z4,z5,z891]),(0,[z2,z892,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z439,z13]),(0,[z242,z2,z3,z4,z5,z24]),(0,[z0,z296,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z824,z6]),(0,[z0,z245,z3,z4,z5,z24]),(0,[z0,z2,z158,z325,z4,z5]),(0,[z0,z2,z3,z132,z47,z13])],[(0,[z144,z2,z3,z4,z129,z6]),(0,[z0,z2,z3,z4,z5,z893]),(0,[z0,z2,z3,z4,z34,z13]),(0,[z0,z2,z128,z89,z5,z6])],[(0,[z0,z2,z3,z4,z894,z6]),(0,[z0,z2,z3,z4,z5,z895]),(0,[z0,z2,z3,z391,z293,z6])],[(0,[z0,z2,z3,z4,z525,z13]),(0,[z0,z2,z3,z4,z5,z896])]],
   [[(0,[z0,z2,z3,z249,z4,z13]),(0,[z125,z2,z3,z4,z5,z82]),(0,[z0,z2,z275,z4,z205,z6])],[],[(0,[z0,z2,z3,z402,z293,z6]),(0,[z0,z2,z3,z4,z5,z426]),(0,[z81,z0,z3,z4,z23,z13])],[(0,[z0,z2,z3,z4,z5,z897]),(0,[z0,z2,z3,z4,z898,z6]),(0,[z0,z2,z7,z586,z5,z6])],[(0,[z0,z245,z3,z4,z5,z468]),(0,[z27,z0,z2,z3,z4,z120]),(0,[z0,z2,z3,z4,z5,z899]),(0,[z125,z2,z3,z108,z5,z6]),(0,[z0,z2,z77,z4,z163,z13])],[(0,[z0,z245,z3,z45,z5,z6]),(0,[z40,z2,z3,z641,z4,z5]),(0,[z0,z2,z75,z113,z5,z6]),(1,[z0,z2,z774,z4,z6])],[(0,[z121,z2,z3,z4,z161,z13]),(0,[z0,z2,z3,z4,z900,z6]),(0,[z0,z2,z3,z4,z901,z6]),(0,[z902,z2,z3,z4,z5,z6]),(0,[z0,z2,z5,z903,z126,z6]),(0,[z0,z2,z280,z4,z163,z13])],[(0,[z263,z2,z3,z4,z5,z24]),(0,[z0,z100,z3,z4,z5,z10]),(0,[z0,z2,z3,z5,z9,z789])],[(0,[z2,z730,z3,z4,z5,z6]),(0,[z0,z226,z204,z4,z5,z6]),(0,[z0,z2,z39,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z771]),(0,[z0,z2,z3,z904,z5,z24])],[(0,[z0,z2,z3,z4,z905,z6]),(0,[z0,z2,z3,z57,z5,z9])],[(0,[z144,z2,z3,z4,z5,z468]),(0,[z367,z0,z3,z4,z5,z61]),(0,[z0,z2,z3,z363,z4,z13])],[(0,[z906,z2,z3,z4,z5,z6]),(0,[z125,z2,z142,z4,z5,z6]),(0,[z0,z2,z3,z907,z5,z6])],[(0,[z535,z0,z8,z4,z5,z6]),(0,[z0,z2,z3,z908,z5,z6])],[(0,[z0,z2,z204,z4,z5,z560]),(0,[z0,z2,z3,z834,z5,z13])],[(0,[z0,z769,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z293,z24])],[(0,[z101,z0,z3,z4,z23,z6])],[(0,[z0,z2,z3,z89,z5,z10]),(0,[z0,z2,z3,z107,z372,z6]),(0,[z0,z2,z159,z48,z5,z6])],[(0,[z0,z2,z3,z4,z909,z6]),(0,[z0,z2,z910,z4,z5,z6]),(0,[z28,z0,z8,z391,z5,z6]),(0,[z125,z2,z3,z115,z5,z6])],[(0,[z0,z2,z149,z4,z5,z6])],[(0,[z0,z2,z157,z4,z163,z13]),(0,[z0,z2,z8,z402,z5,z6])],[(0,[z0,z2,z3,z4,z5,z911]),(0,[z0,z2,z3,z4,z5,z912]),(0,[z0,z2,z3,z4,z913,z6])],[(0,[z399,z2,z3,z88,z5,z6]),(0,[z0,z914,z3,z4,z5,z6]),(0,[z28,z0,z8,z402,z5,z6]),(1,[z125,z2,z3,z4,z13])],[(0,[z0,z2,z3,z4,z915,z6]),(0,[z0,z2,z128,z4,z129,z6]),(0,[z0,z2,z3,z4,z6,z916])],[(0,[z81,z125,z3,z4,z23,z6]),(0,[z0,z2,z3,z917,z5,z6])],[(0,[z918,z0,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z13]),(1,[z0,z2,z3,z4,z749]),(0,[z0,z2,z514,z79,z3,z6]),(0,[z0,z2,z48,z3,z874,z6])],[(0,[z0,z2,z3,z4,z919,z5]),(0,[z0,z90,z153,z4,z5,z6]),(0,[z169,z2,z3,z4,z366,z6]),(0,[z0,z2,z3,z108,z5,z82]),(0,[z0,z2,z3,z4,z920,z6])],[(0,[z921,z2,z3,z4,z5,z6]),(0,[z922,z2,z3,z4,z5,z6]),(0,[z81,z0,z2,z3,z4,z152])],[(0,[z0,z2,z3,z4,z5,z923]),(0,[z0,z2,z3,z4,z924,z6]),(0,[z0,z178,z3,z4,z205,z6]),(0,[z0,z2,z343,z4,z5,z24])],[(0,[z133,z110,z3,z4,z5,z6]),(0,[z28,z130,z8,z4,z5,z6]),(0,[z200,z0,z2,z3,z4,z120])]],
   [[(1,[z2,z3,z792,z5,z6]),(0,[z0,z2,z3,z4,z5,z925]),(0,[z0,z2,z91,z5,z126,z6])],[(0,[z505,z144,z2,z3,z4,z5]),(0,[z0,z2,z3,z926,z5,z6]),(0,[z0,z2,z75,z48,z5,z6]),(0,[z0,z2,z3,z4,z24,z120])],[],[(0,[z0,z2,z3,z4,z927,z6]),(0,[z0,z2,z3,z928,z4,z5]),(0,[z0,z2,z929,z4,z5,z6]),(0,[z2,z3,z4,z5,z41,z859]),(0,[z0,z2,z83,z77,z4,z444]),(0,[z0,z2,z3,z4,z5,z930])],[(0,[z27,z2,z3,z4,z5,z388]),(0,[z0,z2,z48,z3,z483,z6])],[(0,[z0,z2,z931,z3,z5,z6]),(0,[z0,z2,z3,z4,z56,z9]),(0,[z0,z100,z2,z3,z4,z13])],[(0,[z27,z2,z3,z4,z5,z465]),(0,[z932,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z56,z446])],[(0,[z0,z2,z3,z671,z47,z6]),(0,[z0,z26,z3,z4,z5,z560]),(0,[z0,z2,z3,z4,z372,z24])],[(0,[z203,z0,z2,z3,z4,z933]),(0,[z0,z2,z3,z4,z547,z13]),(0,[z0,z2,z142,z108,z5,z6]),(0,[z0,z2,z3,z4,z5,z934]),(0,[z0,z2,z3,z874,z5,z6])],[(0,[z0,z2,z3,z4,z46,z34]),(0,[z0,z2,z3,z4,z5,z935]),(0,[z0,z2,z3,z118,z6,z13]),(0,[z0,z2,z3,z4,z46,z24])],[],[(0,[z0,z2,z3,z936,z5,z6]),(0,[z144,z2,z3,z4,z161,z13]),(0,[z0,z2,z937,z4,z5,z6]),(0,[z0,z92,z849,z4,z5,z6]),(0,[z0,z2,z3,z4,z108,z13]),(0,[z0,z2,z3,z115,z5,z82])],[(0,[z0,z2,z3,z938,z4,z5]),(0,[z0,z2,z396,z3,z4,z13]),(0,[z81,z263,z2,z3,z4,z13]),(0,[z0,z2,z3,z4,z5,z444])],[(0,[z0,z2,z3,z4,z5,z939]),(0,[z2,z3,z4,z38,z824,z6]),(0,[z667,z0,z2,z3,z4,z13]),(0,[z0,z2,z3,z4,z129,z10]),(0,[z0,z2,z3,z391,z5,z24]),(0,[z169,z2,z3,z4,z5,z93]),(0,[z940,z2,z3,z4,z5,z6]),(0,[z81,z0,z2,z3,z108,z13]),(0,[z0,z2,z158,z4,z5,z433]),(0,[z0,z2,z280,z4,z5,z229])],[(0,[z0,z2,z3,z4,z562,z13]),(0,[z0,z2,z3,z4,z941,z6]),(0,[z0,z469,z3,z89,z5,z6]),(0,[z0,z2,z3,z4,z170,z6]),(0,[z28,z0,z8,z4,z5,z176]),(0,[z395,z2,z3,z4,z5,z24]),(0,[z0,z2,z569,z3,z4,z13]),(0,[z0,z2,z257,z77,z4,z6]),(0,[z0,z2,z3,z4,z5,z942]),(0,[z0,z2,z3,z309,z47,z6])],[(0,[z175,z2,z3,z4,z5,z6]),(0,[z0,z943,z3,z4,z5,z6]),(0,[z695,z0,z2,z3,z4,z13])]],
   [[(0,[z0,z2,z3,z4,z933,z6]),(0,[z0,z2,z3,z944,z5,z6])],[(0,[z28,z175,z8,z4,z5,z6]),(0,[z0,z2,z3,z402,z5,z24]),(0,[z0,z3,z813,z66,z5,z6]),(0,[z0,z2,z945,z4,z5,z6])],[(0,[z0,z190,z3,z4,z5,z61]),(0,[z0,z2,z3,z946,z5,z6]),(0,[z0,z2,z3,z4,z9,z120])],[(0,[z0,z2,z3,z947,z5,z6]),(0,[z169,z2,z3,z4,z5,z425]),(0,[z0,z2,z91,z5,z663,z6]),(0,[z0,z2,z159,z79,z4,z13])],[(0,[z0,z2,z948,z3,z4,z5])],[(0,[z0,z2,z3,z4,z6,z949]),(0,[z0,z2,z267,z4,z5,z24]),(0,[z125,z2,z3,z4,z5,z24])],[(0,[z0,z2,z3,z4,z5,z875])],[(0,[z950,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z366,z951])],[(0,[z28,z0,z29,z8,z5,z6]),(0,[z263,z2,z275,z4,z5,z6]),(0,[z0,z2,z3,z478,z4,z13])],[(0,[z258,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z952]),(0,[z505,z0,z2,z3,z57,z5]),(0,[z0,z2,z3,z134,z5,z24]),(0,[z0,z2,z3,z4,z5,z953]),(0,[z0,z2,z3,z4,z5,z954]),(0,[z0,z2,z3,z405,z47,z6])],[(0,[z0,z2,z3,z4,z5,z955])],[(0,[z0,z2,z3,z4,z5,z956]),(0,[z0,z2,z3,z4,z877,z6]),(0,[z0,z2,z3,z957,z5,z6]),(0,[z0,z2,z3,z4,z5,z958]),(0,[z0,z2,z3,z4,z5,z959]),(0,[z0,z2,z77,z774,z4,z6]),(0,[z97,z0,z2,z4,z5,z17]),(0,[z0,z2,z960,z4,z5,z6])],[(0,[z0,z2,z3,z118,z23,z6]),(0,[z0,z100,z3,z4,z5,z199])],[(0,[z2,z110,z39,z4,z5,z6]),(0,[z961,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z265,z4,z13]),(0,[z0,z2,z3,z4,z5,z962]),(1,[z0,z2,z343,z4,z13]),(0,[z687,z0,z2,z3,z4,z13])],[(0,[z2,z3,z4,z792,z5,z6]),(0,[z0,z963,z3,z4,z5,z6]),(0,[z37,z2,z3,z4,z38,z240])],[(0,[z0,z2,z3,z4,z5,z964]),(0,[z0,z2,z3,z4,z98,z13])]],
   [[(0,[z0,z2,z3,z4,z965,z6]),(0,[z0,z2,z3,z4,z5,z966]),(0,[z0,z2,z3,z4,z5,z967])],[(0,[z169,z2,z3,z4,z5,z6]),(0,[z968,z0,z2,z3,z4,z5]),(0,[z0,z969,z3,z4,z5,z6]),(0,[z237,z0,z3,z4,z5,z183])],[(0,[z0,z2,z3,z4,z5,z970]),(0,[z0,z2,z95,z4,z163,z13]),(0,[z0,z2,z79,z343,z4,z13])],[(0,[z0,z2,z3,z4,z38,z560])],[(0,[z0,z2,z756,z4,z5,z6]),(0,[z0,z2,z3,z4,z170,z797]),(0,[z0,z2,z3,z429,z5,z9])],[(0,[z0,z2,z3,z4,z5,z16])],[(0,[z0,z2,z3,z4,z971,z6]),(0,[z0,z2,z3,z21,z5,z6]),(0,[z0,z2,z3,z21,z5,z122]),(0,[z0,z2,z3,z77,z118,z13])],[(0,[z2,z110,z3,z89,z5,z6]),(0,[z0,z26,z3,z4,z5,z122]),(0,[z972,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z973]),(0,[z0,z2,z3,z4,z5,z974]),(0,[z0,z2,z3,z4,z5,z727]),(0,[z0,z2,z3,z4,z611,z13]),(0,[z0,z2,z83,z77,z4,z76])],[(0,[z0,z2,z3,z4,z5,z975]),(0,[z0,z2,z976,z4,z5,z6]),(0,[z54,z0,z2,z3,z4,z13])],[(1,[z0,z2,z3,z4,z710])],[(0,[z168,z0,z3,z66,z5,z24])],[(0,[z0,z2,z48,z396,z3,z6]),(0,[z0,z2,z977,z4,z5,z6])],[(0,[z0,z2,z497,z113,z5,z6])],[(0,[z0,z2,z3,z4,z55,z6]),(0,[z0,z2,z3,z4,z5,z978]),(0,[z0,z2,z3,z4,z56,z6])],[(0,[z144,z408,z3,z4,z5,z6]),(0,[z0,z2,z3,z979,z5,z6]),(0,[z0,z469,z3,z4,z5,z24]),(0,[z980,z2,z3,z4,z5,z6])]],
   [[(0,[z674,z110,z3,z4,z5,z6]),(0,[z0,z226,z267,z4,z5,z6])],[(0,[z256,z2,z3,z4,z38,z6]),(0,[z0,z2,z3,z4,z5,z981]),(0,[z0,z2,z7,z698,z5,z6]),(0,[z0,z2,z3,z108,z5,z24])],[(0,[z0,z2,z3,z4,z5,z982]),(0,[z242,z110,z3,z4,z5,z6]),(0,[z983,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z984])],[],[(0,[z0,z226,z3,z134,z5,z6]),(0,[z0,z42,z3,z107,z5,z6])],[(0,[z0,z2,z3,z4,z985,z6]),(0,[z0,z2,z3,z4,z483,z13])],[(0,[z0,z2,z267,z4,z5,z560]),(0,[z0,z322,z92,z4,z5,z6])],[(0,[z207,z2,z3,z31,z5,z6])],[(0,[z0,z469,z3,z45,z5,z6]),(0,[z0,z2,z3,z118,z5,z6])],[],[(0,[z0,z2,z3,z986,z5,z6]),(0,[z0,z2,z3,z134,z5,z560]),(0,[z0,z2,z91,z192,z5,z6]),(0,[z0,z2,z275,z4,z46,z6]),(0,[z0,z2,z3,z4,z339,z13])],[(0,[z0,z2,z3,z4,z652,z13]),(0,[z0,z2,z3,z908,z5,z13])],[(0,[z0,z3,z849,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z951]),(0,[z0,z2,z3,z4,z564,z24])],[],[(0,[z0,z987,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z540,z13]),(0,[z206,z0,z2,z3,z4,z13])],[(1,[z2,z3,z4,z5,z859]),(0,[z97,z0,z2,z4,z98,z17]),(0,[z0,z2,z3,z254,z4,z13])]],
   [[(0,[z505,z2,z110,z3,z4,z5]),(0,[z2,z324,z3,z4,z5,z41]),(0,[z0,z2,z3,z115,z5,z24])],[(0,[z0,z2,z3,z89,z5,z24]),(0,[z40,z2,z3,z4,z85,z5])],[(0,[z2,z110,z3,z4,z129,z6]),(0,[z0,z2,z3,z4,z5,z988]),(0,[z0,z2,z149,z4,z5,z13]),(0,[z0,z2,z989,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z990]),(0,[z0,z2,z3,z4,z5,z991])],[(0,[z0,z2,z91,z3,z47,z13]),(0,[z0,z2,z3,z309,z5,z338])],[(0,[z27,z2,z3,z4,z5,z166])],[(0,[z0,z2,z992,z4,z5,z6]),(0,[z130,z2,z3,z4,z5,z73]),(0,[z0,z2,z148,z3,z5,z24]),(0,[z0,z2,z993,z3,z5,z6]),(0,[z125,z2,z275,z4,z5,z6]),(0,[z0,z2,z382,z5,z126,z6]),(0,[z0,z994,z3,z4,z5,z24])],[(0,[z995,z0,z2,z3,z4,z5]),(0,[z0,z469,z39,z4,z5,z6]),(0,[z40,z2,z3,z4,z5,z859]),(0,[z996,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z997]),(0,[z0,z2,z142,z4,z5,z82]),(0,[z0,z2,z3,z4,z5,z998]),(0,[z0,z2,z224,z3,z5,z24])],[(0,[z333,z2,z3,z4,z161,z6]),(0,[z28,z0,z8,z4,z5,z24])],[(0,[z999,z2,z3,z4,z5,z6])],[],[(0,[z71,z2,z104,z4,z5,z6])],[(0,[z1000,z2,z3,z4,z5,z6]),(0,[z109,z0,z2,z3,z5,z164])],[(0,[z133,z110,z3,z4,z5,z13]),(0,[z0,z361,z3,z4,z243,z10]),(0,[z0,z2,z4,z5,z903,z6])],[(0,[z0,z2,z91,z5,z126,z13]),(0,[z0,z2,z3,z5,z789,z58])],[(0,[z0,z1001,z3,z4,z5,z6]),(0,[z0,z1002,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1003]),(0,[z81,z0,z3,z4,z23,z16])]],
   [[(0,[z2,z110,z3,z4,z5,z468]),(0,[z0,z2,z3,z4,z5,z1004]),(0,[z0,z2,z3,z4,z5,z1005]),(0,[z0,z2,z3,z4,z5,z1006]),(0,[z0,z460,z2,z3,z4,z13])],[(0,[z0,z2,z1007,z3,z5,z6]),(0,[z0,z2,z204,z4,z5,z122]),(0,[z0,z2,z3,z4,z293,z722])],[],[(0,[z0,z2,z48,z239,z3,z6]),(0,[z0,z2,z3,z4,z196,z13]),(0,[z0,z2,z3,z5,z6,z1008]),(0,[z0,z2,z3,z4,z1009,z6]),(0,[z0,z2,z3,z4,z243,z82]),(0,[z0,z2,z1010,z4,z5,z6]),(0,[z0,z2,z343,z4,z6,z13])],[(0,[z121,z2,z3,z21,z161,z6]),(0,[z1011,z2,z3,z4,z5,z6]),(0,[z0,z317,z2,z3,z4,z13]),(0,[z0,z2,z3,z4,z359,z24])],[(0,[z121,z26,z3,z4,z161,z6]),(0,[z0,z2,z3,z1012,z5,z6]),(0,[z81,z0,z2,z275,z4,z13])],[(0,[z144,z145,z3,z4,z5,z271]),(0,[z0,z2,z3,z4,z5,z1013]),(0,[z0,z2,z3,z77,z4,z13])],[(0,[z1014,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1015,z6]),(0,[z0,z2,z3,z4,z46,z811])],[(0,[z0,z2,z1016,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1017])],[(0,[z0,z730,z3,z4,z5,z6]),(0,[z0,z2,z39,z89,z5,z6]),(0,[z1018,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1019]),(0,[z0,z1020,z3,z4,z5,z6]),(0,[z0,z2,z95,z774,z4,z6])],[(0,[z0,z2,z142,z115,z5,z6]),(0,[z0,z2,z3,z4,z729,z6]),(0,[z0,z2,z3,z4,z5,z1021]),(0,[z0,z2,z7,z3,z47,z13]),(0,[z0,z2,z4,z163,z433,z13])],[(0,[z0,z2,z3,z4,z5,z1022]),(0,[z0,z2,z1023,z4,z5,z6]),(0,[z30,z2,z3,z31,z5,z24])],[(0,[z40,z2,z3,z4,z5,z41]),(0,[z0,z2,z3,z4,z129,z24]),(0,[z0,z2,z3,z4,z170,z13]),(0,[z0,z2,z3,z309,z47,z13])],[(0,[z0,z2,z1024,z3,z5,z6]),(0,[z0,z2,z3,z1025,z5,z6]),(0,[z175,z2,z3,z4,z5,z13]),(0,[z81,z0,z3,z4,z729,z6])],[(0,[z0,z2,z3,z88,z47,z13]),(0,[z0,z2,z3,z4,z5,z240]),(0,[z81,z0,z139,z3,z4,z13]),(0,[z0,z2,z275,z4,z5,z82]),(0,[z0,z2,z3,z4,z24,z13])],[(0,[z242,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z903,z6]),(0,[z383,z0,z2,z4,z5,z431])]],
   [[(0,[z0,z245,z3,z4,z5,z6]),(0,[z0,z2,z104,z4,z163,z13]),(0,[z0,z1026,z3,z4,z5,z6]),(1,[z2,z3,z4,z824,z6]),(0,[z0,z210,z3,z107,z5,z6])],[(0,[z0,z2,z3,z4,z1027,z6]),(0,[z1028,z2,z3,z4,z5,z6]),(0,[z0,z2,z1029,z3,z4,z5]),(0,[z0,z2,z48,z79,z3,z11])],[(0,[z0,z2,z275,z108,z5,z6]),(0,[z0,z2,z3,z4,z5,z407]),(0,[z0,z2,z224,z3,z77,z13]),(0,[z2,z3,z4,z5,z13,z1030])],[],[(0,[z0,z2,z3,z4,z5,z1031]),(0,[z0,z2,z3,z4,z5,z749]),(0,[z49,z0,z2,z3,z4,z129])],[],[(0,[z0,z2,z3,z4,z1032,z468]),(0,[z0,z2,z3,z4,z5,z1033]),(0,[z0,z2,z3,z1034,z5,z6]),(0,[z0,z191,z2,z3,z4,z13]),(0,[z0,z2,z3,z4,z5,z1035])],[(0,[z1036,z2,z3,z4,z5,z6]),(0,[z0,z2,z1037,z3,z5,z6]),(0,[z0,z2,z3,z640,z4,z13]),(0,[z0,z2,z3,z4,z549,z24]),(0,[z0,z2,z551,z3,z4,z13])],[(0,[z0,z2,z533,z113,z5,z6]),(0,[z0,z2,z91,z5,z903,z6]),(0,[z0,z2,z1038,z4,z5,z24])],[(0,[z0,z2,z3,z4,z5,z1039]),(0,[z0,z2,z960,z4,z5,z13])],[(0,[z0,z26,z3,z4,z5,z6]),(0,[z125,z2,z3,z4,z6,z13])],[(0,[z263,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1040,z5,z6]),(0,[z0,z2,z3,z45,z5,z24]),(0,[z0,z2,z192,z4,z366,z6]),(0,[z0,z2,z1041,z4,z5,z6])],[(0,[z27,z110,z3,z4,z5,z61]),(0,[z147,z505,z2,z3,z88,z5]),(0,[z0,z469,z3,z4,z129,z6]),(0,[z0,z2,z113,z5,z903,z6])],[(0,[z2,z157,z751,z4,z5,z6]),(0,[z0,z2,z3,z904,z5,z6]),(0,[z0,z2,z1042,z4,z5,z6])],[(0,[z0,z2,z497,z3,z4,z13])],[(0,[z169,z2,z3,z4,z5,z13])]],
   [[(0,[z2,z110,z3,z4,z161,z13]),(0,[z2,z51,z3,z4,z5,z6]),(0,[z0,z1043,z3,z4,z5,z6]),(0,[z0,z2,z113,z442,z5,z6])],[(0,[z0,z2,z3,z4,z1044,z6]),(0,[z0,z849,z8,z4,z5,z6]),(0,[z0,z2,z192,z66,z5,z6]),(0,[z0,z2,z275,z115,z5,z6]),(1,[z0,z2,z4,z5,z875])],[(0,[z306,z2,z157,z4,z5,z6])],[(0,[z655,z0,z2,z4,z5,z17])],[(0,[z0,z2,z3,z1045,z5,z6]),(0,[z0,z2,z3,z21,z5,z13]),(0,[z0,z2,z39,z4,z129,z6]),(0,[z0,z2,z3,z4,z5,z76])],[],[(0,[z0,z2,z3,z1046,z5,z6]),(0,[z0,z2,z3,z4,z78,z24]),(0,[z0,z2,z1047,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1048])],[(0,[z0,z2,z3,z1049,z5,z6]),(0,[z0,z2,z231,z4,z366,z6]),(0,[z0,z2,z3,z4,z5,z1050]),(0,[z0,z2,z3,z1051,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1052]),(0,[z0,z2,z3,z4,z644,z24]),(0,[z0,z2,z3,z4,z5,z1053])],[(0,[z0,z2,z3,z4,z5,z1054]),(0,[z0,z2,z39,z4,z5,z24])],[(0,[z0,z2,z3,z4,z5,z1055]),(0,[z357,z2,z3,z31,z5,z6]),(0,[z0,z2,z3,z77,z4,z967])],[(0,[z0,z2,z3,z4,z55,z13]),(0,[z0,z2,z192,z4,z5,z93]),(0,[z0,z2,z142,z4,z5,z24]),(0,[z0,z2,z3,z4,z56,z13])],[(0,[z0,z226,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z1056]),(0,[z200,z0,z3,z4,z5,z737]),(0,[z0,z2,z614,z4,z163,z6])],[(0,[z102,z2,z751,z4,z5,z6]),(0,[z0,z2,z3,z89,z129,z6]),(0,[z0,z2,z92,z4,z293,z6]),(0,[z0,z2,z3,z4,z1057,z6]),(0,[z0,z2,z3,z4,z293,z73]),(0,[z0,z2,z7,z5,z903,z6])],[(0,[z130,z2,z3,z4,z5,z6]),(0,[z121,z2,z204,z4,z161,z6]),(0,[z0,z2,z3,z4,z5,z1058]),(0,[z0,z2,z1059,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z271]),(0,[z37,z2,z3,z4,z824,z6]),(0,[z1060,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1061]),(0,[z0,z178,z2,z3,z4,z13])],[(0,[z144,z610,z3,z4,z5,z6]),(0,[z0,z2,z113,z4,z293,z6]),(0,[z0,z2,z1062,z4,z5,z6]),(0,[z0,z361,z3,z4,z5,z519]),(0,[z627,z0,z2,z3,z4,z13])],[(0,[z0,z2,z128,z4,z5,z6]),(0,[z0,z2,z192,z4,z5,z425]),(0,[z0,z2,z343,z4,z5,z6])],[(0,[z0,z2,z39,z45,z5,z6]),(0,[z0,z2,z1063,z3,z5,z6])],[(0,[z0,z3,z4,z5,z6,z737])],[(0,[z0,z2,z3,z4,z5,z1064]),(0,[z0,z1065,z3,z4,z5,z6]),(0,[z1066,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z729,z6]),(0,[z1067,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1068,z6])],[(0,[z203,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1069]),(0,[z0,z2,z516,z3,z4,z13]),(0,[z0,z2,z3,z108,z6,z13]),(0,[z0,z2,z3,z118,z5,z13]),(0,[z0,z2,z3,z4,z118,z13])],[(0,[z443,z2,z157,z4,z5,z6]),(0,[z1070,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1071]),(0,[z0,z2,z3,z4,z5,z716]),(0,[z0,z2,z3,z4,z1072,z6])],[(0,[z0,z2,z3,z4,z243,z24]),(0,[z0,z2,z3,z4,z5,z11])],[(0,[z0,z2,z231,z4,z5,z93]),(0,[z0,z2,z95,z4,z163,z407]),(0,[z0,z2,z3,z4,z98,z52])],[(0,[z0,z2,z3,z4,z5,z1073]),(0,[z168,z0,z3,z66,z366,z6]),(0,[z0,z2,z3,z4,z5,z1074])],[(0,[z0,z2,z662,z4,z5,z52]),(0,[z0,z2,z3,z4,z5,z1075]),(0,[z0,z2,z4,z5,z875,z17])],[(0,[z0,z2,z3,z4,z5,z1076]),(0,[z0,z2,z3,z1077,z5,z6]),(0,[z0,z2,z3,z4,z223,z13]),(0,[z0,z3,z4,z5,z1078,z6]),(0,[z0,z2,z3,z4,z431,z13])],[(0,[z0,z1079,z3,z4,z5,z6]),(0,[z0,z2,z1080,z4,z5,z6]),(0,[z0,z2,z3,z4,z52,z120]),(0,[z0,z2,z159,z4,z5,z6])],[(0,[z72,z110,z3,z4,z5,z6]),(0,[z203,z0,z2,z4,z5,z17]),(0,[z0,z290,z92,z4,z5,z6]),(0,[z237,z0,z3,z4,z5,z61]),(0,[z0,z2,z159,z4,z5,z459]),(0,[z0,z2,z3,z4,z46,z459])],[(0,[z0,z2,z3,z1081,z4,z6]),(0,[z0,z2,z231,z4,z5,z425])]],
   [[(0,[z0,z1082,z3,z4,z5,z6]),(0,[z0,z2,z192,z4,z5,z6]),(0,[z12,z0,z2,z3,z4,z811])],[(0,[z577,z2,z104,z4,z5,z6]),(0,[z0,z2,z7,z113,z5,z24]),(0,[z542,z0,z2,z3,z4,z13])],[(0,[z395,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1083,z5,z6]),(0,[z0,z2,z3,z57,z4,z129])],[(0,[z144,z281,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z710]),(0,[z0,z2,z7,z192,z5,z6]),(0,[z0,z2,z1084,z4,z5,z6]),(0,[z0,z2,z275,z4,z5,z24]),(0,[z81,z0,z2,z3,z115,z13])],[(0,[z0,z2,z204,z4,z5,z6]),(0,[z0,z2,z3,z700,z4,z13]),(0,[z0,z2,z3,z4,z5,z1085]),(0,[z0,z3,z4,z205,z729,z6])],[(0,[z0,z2,z1086,z4,z5,z6]),(0,[z0,z2,z3,z4,z1087,z5]),(0,[z0,z2,z3,z4,z5,z1088]),(0,[z331,z0,z3,z4,z5,z318])],[(0,[z2,z3,z792,z88,z5,z6]),(0,[z333,z2,z3,z4,z161,z13]),(0,[z0,z2,z29,z3,z5,z24]),(0,[z0,z2,z3,z249,z47,z6]),(0,[z0,z2,z3,z292,z4,z13]),(0,[z0,z2,z3,z4,z5,z1089])],[(0,[z0,z2,z3,z4,z366,z1052]),(0,[z0,z2,z3,z118,z5,z444])],[(0,[z2,z1090,z3,z4,z5,z6])],[(0,[z125,z2,z3,z4,z5,z6]),(0,[z71,z2,z104,z4,z5,z13]),(0,[z0,z2,z267,z4,z5,z6]),(0,[z0,z2,z267,z4,z5,z122]),(0,[z0,z2,z3,z4,z5,z1091]),(0,[z0,z2,z3,z4,z253,z13])],[],[(0,[z0,z2,z3,z4,z1092,z6]),(0,[z0,z2,z3,z391,z5,z73]),(0,[z168,z0,z3,z66,z5,z93]),(0,[z0,z2,z79,z3,z47,z13]),(0,[z0,z2,z3,z4,z453,z24])],[(0,[z27,z680,z2,z3,z4,z5]),(0,[z0,z2,z75,z4,z5,z6]),(0,[z0,z2,z3,z4,z47,z316])],[(0,[z0,z2,z3,z4,z5,z1093]),(0,[z0,z2,z3,z134,z5,z122]),(0,[z0,z2,z231,z4,z5,z6])],[(0,[z0,z226,z3,z4,z5,z560]),(0,[z0,z2,z91,z402,z5,z6]),(0,[z0,z139,z3,z4,z205,z24]),(0,[z242,z2,z3,z4,z5,z61]),(0,[z0,z2,z3,z4,z5,z789])],[(0,[z0,z1094,z3,z4,z5,z6]),(0,[z0,z2,z204,z4,z5,z13]),(0,[z0,z245,z3,z4,z5,z61]),(0,[z0,z2,z92,z402,z5,z6]),(0,[z0,z2,z3,z402,z5,z73]),(0,[z0,z2,z4,z5,z6,z875])]],
   [[(0,[z0,z2,z1095,z3,z4,z6]),(0,[z0,z2,z3,z4,z272,z13]),(0,[z0,z2,z3,z4,z161,z560]),(0,[z1096,z0,z2,z3,z4,z5]),(0,[z2,z3,z4,z5,z13,z778])],[(0,[z168,z0,z3,z66,z5,z425])],[(0,[z145,z730,z3,z4,z5,z6]),(0,[z0,z2,z113,z402,z5,z6]),(0,[z0,z2,z3,z4,z5,z720]),(0,[z0,z2,z3,z1097,z5,z6]),(0,[z1011,z2,z3,z4,z5,z13])],[],[(0,[z0,z2,z3,z4,z1098,z6]),(0,[z0,z2,z3,z1099,z5,z6]),(0,[z0,z2,z1100,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1101]),(0,[z0,z2,z3,z4,z24,z416])],[(0,[z0,z2,z3,z654,z47,z6])],[(0,[z37,z2,z3,z4,z38,z24]),(0,[z0,z2,z29,z7,z5,z6])],[(0,[z1102,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1103]),(0,[z81,z0,z2,z142,z4,z13]),(0,[z0,z2,z159,z48,z79,z6])],[(0,[z0,z2,z1104,z4,z5,z6]),(0,[z0,z2,z3,z45,z129,z6]),(0,[z0,z2,z3,z4,z5,z1105])],[(0,[z0,z2,z3,z4,z1106,z6]),(0,[z0,z2,z3,z1107,z5,z6]),(0,[z0,z2,z343,z4,z23,z6])],[(0,[z0,z2,z3,z1108,z5,z6]),(0,[z71,z2,z751,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1109])],[(0,[z27,z2,z3,z4,z5,z859])],[(0,[z0,z2,z3,z4,z299,z13]),(0,[z0,z1110,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z176]),(0,[z1111,z2,z3,z4,z5,z6]),(0,[z0,z374,z3,z4,z5,z519])],[(0,[z0,z2,z1112,z3,z4,z5]),(0,[z1113,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1114]),(0,[z242,z2,z3,z4,z5,z13]),(0,[z1115,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z781,z5,z24])],[(0,[z71,z203,z2,z104,z4,z5]),(0,[z147,z2,z3,z792,z5,z6]),(0,[z0,z245,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z880]),(0,[z0,z2,z91,z412,z5,z6])],[(0,[z168,z0,z3,z66,z5,z6]),(0,[z0,z2,z3,z66,z372,z6]),(0,[z0,z3,z4,z5,z10,z737]),(0,[z0,z361,z2,z3,z4,z120]),(0,[z0,z2,z1116,z3,z5,z6])]],
   [[(0,[z395,z2,z3,z4,z366,z6])],[(0,[z0,z2,z3,z4,z1117,z6])],[(0,[z0,z2,z3,z813,z5,z6])],[(0,[z175,z2,z3,z4,z170,z6]),(0,[z0,z2,z8,z4,z163,z13]),(0,[z0,z2,z1118,z3,z5,z6])],[(0,[z121,z2,z3,z4,z824,z6]),(0,[z535,z0,z3,z4,z23,z6]),(0,[z49,z0,z2,z3,z453,z58])],[(0,[z71,z2,z103,z104,z4,z5]),(0,[z0,z2,z3,z1119,z4,z5]),(0,[z0,z2,z3,z108,z5,z6])],[],[(0,[z0,z2,z3,z4,z293,z6]),(0,[z0,z2,z3,z4,z6,z811])],[(0,[z0,z26,z3,z4,z5,z13]),(0,[z0,z2,z3,z5,z6,z1120]),(0,[z81,z0,z2,z3,z4,z13]),(0,[z471,z0,z2,z3,z4,z13]),(0,[z274,z2,z3,z4,z5,z36])],[(0,[z0,z2,z3,z4,z5,z1121]),(0,[z263,z2,z3,z4,z5,z13])],[(0,[z0,z2,z3,z4,z372,z93]),(1,[z0,z2,z5,z903,z6]),(0,[z0,z2,z224,z5,z163,z6]),(0,[z0,z2,z3,z4,z24,z612])],[(0,[z0,z2,z3,z57,z621,z5]),(0,[z0,z2,z3,z4,z5,z1122])],[(0,[z147,z2,z3,z88,z5,z24]),(0,[z556,z0,z2,z3,z4,z13]),(0,[z0,z2,z79,z3,z4,z316])],[(0,[z319,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1123]),(0,[z0,z2,z79,z3,z4,z843])],[(0,[z279,z2,z104,z4,z5,z6]),(0,[z0,z226,z3,z4,z5,z122]),(0,[z0,z2,z1124,z4,z5,z6]),(0,[z0,z2,z3,z118,z205,z6]),(0,[z2,z51,z3,z4,z5,z13]),(0,[z0,z2,z3,z132,z47,z316])],[(0,[z0,z2,z3,z4,z5,z1125])]],
   [[(0,[z0,z2,z91,z4,z293,z6]),(0,[z0,z2,z3,z4,z372,z425])],[(0,[z0,z2,z3,z1126,z5,z6]),(0,[z0,z2,z3,z1127,z4,z5]),(0,[z169,z2,z192,z4,z5,z6]),(0,[z395,z2,z3,z4,z5,z93]),(0,[z0,z2,z3,z4,z5,z1128])],[(0,[z0,z2,z1129,z4,z5,z6]),(0,[z0,z2,z3,z4,z1130,z6])],[(0,[z0,z2,z3,z4,z5,z1131]),(0,[z0,z2,z3,z4,z1132,z6]),(0,[z0,z2,z3,z4,z1133,z6]),(0,[z0,z2,z3,z874,z4,z6])],[(0,[z0,z2,z3,z4,z24,z638]),(0,[z0,z2,z3,z4,z1134,z6])],[(0,[z702,z145,z3,z4,z5,z6]),(0,[z0,z2,z3,z57,z5,z479])],[(0,[z0,z2,z3,z4,z5,z711]),(0,[z0,z2,z3,z132,z47,z490]),(0,[z0,z2,z343,z4,z5,z459])],[(0,[z101,z2,z3,z4,z161,z6]),(0,[z0,z2,z1135,z4,z5,z6]),(0,[z0,z2,z3,z4,z710,z6]),(0,[z121,z2,z267,z4,z161,z6]),(0,[z0,z22,z2,z91,z5,z6]),(0,[z395,z2,z3,z4,z5,z425]),(0,[z0,z2,z3,z132,z47,z24])],[(0,[z0,z2,z1136,z4,z5,z6])],[],[(0,[z0,z2,z1137,z4,z5,z6]),(0,[z0,z994,z3,z4,z5,z6]),(0,[z0,z2,z148,z3,z5,z6]),(0,[z1138,z2,z3,z4,z5,z6])],[(0,[z0,z1139,z3,z4,z5,z6]),(0,[z121,z2,z3,z134,z161,z6]),(0,[z0,z2,z3,z4,z129,z166]),(0,[z0,z2,z224,z3,z5,z6])],[(0,[z28,z0,z8,z4,z5,z6]),(0,[z0,z2,z3,z4,z1140,z6]),(0,[z0,z2,z3,z4,z411,z13])],[(0,[z0,z2,z1141,z3,z4,z6]),(0,[z130,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z586,z4,z13])],[(0,[z169,z2,z231,z4,z5,z6]),(0,[z0,z2,z3,z4,z372,z6])],[(0,[z0,z2,z3,z4,z5,z1142]),(0,[z0,z2,z3,z4,z5,z1143]),(0,[z2,z1144,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z128,z4,z5,z13]),(0,[z0,z2,z343,z4,z5,z13])],[(0,[z1145,z0,z2,z3,z4,z5])],[(0,[z101,z0,z2,z3,z4,z13]),(0,[z0,z1146,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1147]),(0,[z0,z2,z1148,z4,z5,z6]),(0,[z97,z0,z2,z4,z5,z875])],[(0,[z245,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z38,z13]),(0,[z0,z2,z3,z391,z5,z6]),(0,[z0,z2,z849,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1149]),(0,[z0,z65,z3,z107,z5,z24]),(0,[z0,z2,z3,z4,z5,z1150]),(0,[z0,z2,z3,z4,z5,z1151])],[(0,[z0,z2,z3,z4,z5,z1152])],[(0,[z0,z2,z751,z4,z5,z6]),(0,[z28,z0,z8,z4,z5,z73]),(0,[z28,z0,z849,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1153]),(0,[z0,z2,z1154,z4,z5,z6]),(0,[z1155,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z737]),(0,[z49,z0,z2,z3,z5,z789])],[(0,[z26,z3,z4,z5,z161,z6]),(0,[z0,z2,z3,z1156,z5,z6])],[(0,[z133,z730,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1157,z6]),(0,[z0,z2,z3,z402,z5,z6]),(0,[z0,z65,z2,z75,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1158])],[(0,[z0,z3,z4,z729,z23,z6]),(0,[z0,z2,z598,z77,z4,z6])],[(0,[z0,z2,z1159,z4,z5,z6]),(0,[z0,z2,z3,z104,z4,z710]),(0,[z0,z2,z3,z4,z1160,z6]),(0,[z81,z0,z3,z4,z23,z82]),(0,[z0,z2,z3,z4,z163,z152]),(0,[z0,z2,z350,z3,z4,z13]),(0,[z0,z2,z159,z4,z5,z13])],[(0,[z0,z2,z1161,z3,z5,z6]),(0,[z0,z2,z3,z108,z23,z6]),(0,[z0,z2,z79,z3,z4,z152])],[(1,[z730,z3,z4,z5,z6]),(0,[z333,z2,z3,z4,z5,z166]),(0,[z601,z0,z2,z3,z4,z13]),(0,[z0,z2,z83,z77,z4,z24]),(0,[z0,z2,z3,z4,z5,z316])],[(0,[z0,z2,z3,z1162,z5,z6]),(0,[z0,z2,z192,z4,z5,z13]),(0,[z0,z2,z3,z107,z47,z13])],[(0,[z81,z0,z3,z108,z23,z6]),(0,[z0,z139,z3,z4,z6,z519]),(0,[z0,z2,z3,z4,z17,z120]),(0,[z0,z2,z277,z4,z5,z433]),(0,[z364,z2,z3,z4,z5,z62])]],
   [[(0,[z0,z2,z3,z4,z5,z1163]),(0,[z0,z2,z3,z134,z5,z6]),(0,[z130,z2,z3,z4,z170,z6]),(0,[z395,z2,z3,z4,z5,z13])],[(0,[z0,z2,z3,z4,z5,z1164]),(0,[z2,z3,z4,z824,z161,z6]),(0,[z0,z245,z3,z4,z55,z6]),(0,[z0,z2,z3,z4,z452,z13])],[(0,[z0,z2,z3,z4,z1165,z5]),(0,[z0,z2,z3,z4,z1032,z6]),(0,[z0,z2,z3,z4,z5,z1166]),(0,[z507,z0,z2,z3,z5,z58]),(0,[z97,z0,z2,z4,z5,z431])],[(0,[z0,z26,z3,z21,z5,z6]),(0,[z0,z2,z29,z5,z126,z6])],[(0,[z0,z2,z3,z1167,z5,z6]),(0,[z0,z2,z32,z4,z5,z52])],[(0,[z0,z2,z3,z4,z462,z13]),(0,[z0,z2,z3,z31,z47,z13]),(0,[z0,z2,z3,z4,z5,z490])],[(0,[z0,z2,z3,z4,z1168,z6]),(0,[z0,z90,z849,z4,z5,z6]),(0,[z0,z2,z75,z5,z126,z6])],[(0,[z0,z2,z267,z4,z5,z13]),(0,[z125,z2,z3,z4,z5,z13]),(0,[z81,z0,z142,z4,z23,z6]),(1,[z0,z2,z3,z108,z13]),(0,[z1169,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z164,z13])],[(0,[z0,z2,z3,z4,z62,z13])],[(0,[z37,z2,z3,z4,z38,z34])],[(0,[z0,z2,z75,z4,z5,z13])],[(0,[z556,z110,z3,z4,z5,z6]),(0,[z0,z2,z231,z4,z5,z13]),(0,[z125,z3,z4,z5,z23,z6])],[(0,[z0,z2,z350,z4,z163,z6]),(0,[z0,z2,z3,z4,z459,z13])],[(0,[z102,z2,z157,z4,z5,z24])],[(0,[z0,z2,z3,z4,z293,z899]),(0,[z81,z0,z3,z115,z23,z6]),(0,[z0,z361,z3,z4,z5,z10])],[(0,[z0,z2,z1170,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z119,z13]),(0,[z0,z2,z74,z5,z126,z6]),(0,[z0,z2,z4,z5,z6,z1171]),(0,[z0,z2,z3,z4,z1172,z6])],[],[(0,[z501,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1173])],[],[(0,[z0,z2,z3,z4,z5,z82]),(0,[z0,z2,z3,z4,z163,z96])],[(0,[z0,z2,z3,z4,z499,z13]),(0,[z0,z2,z1174,z4,z5,z6])],[(0,[z0,z469,z3,z4,z5,z6]),(0,[z168,z0,z149,z66,z5,z6]),(0,[z0,z2,z3,z5,z6,z789]),(0,[z0,z2,z3,z4,z647,z13])],[(0,[z0,z2,z3,z4,z1175,z6])],[(0,[z2,z3,z4,z5,z6,z859]),(0,[z0,z139,z3,z4,z205,z152])],[(0,[z1176,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z78,z6])],[(0,[z110,z3,z4,z5,z562,z6])],[(0,[z0,z2,z3,z1177,z5,z6])],[(0,[z168,z0,z3,z66,z5,z13]),(1,[z0,z2,z3,z874,z6]),(0,[z394,z2,z3,z4,z5,z388])],[(0,[z0,z2,z39,z4,z5,z6]),(0,[z0,z2,z3,z4,z1178,z6])],[(0,[z144,z145,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z1179]),(0,[z0,z2,z3,z4,z82,z13]),(0,[z0,z2,z3,z4,z47,z152]),(0,[z0,z2,z3,z118,z5,z76])]],
   [[(0,[z0,z2,z3,z4,z5,z1180]),(0,[z0,z2,z3,z4,z5,z1181]),(0,[z0,z2,z142,z4,z5,z6]),(0,[z0,z2,z3,z4,z1182,z6]),(0,[z0,z2,z3,z4,z524,z13])],[(0,[z0,z226,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1183]),(0,[z0,z2,z1184,z4,z5,z6])],[(0,[z54,z0,z3,z66,z5,z6]),(0,[z0,z2,z79,z3,z874,z6]),(0,[z0,z2,z48,z79,z3,z24])],[(0,[z0,z2,z347,z4,z163,z6]),(0,[z0,z2,z3,z4,z87,z5]),(0,[z0,z2,z111,z3,z4,z13]),(0,[z0,z2,z128,z4,z55,z6]),(0,[z0,z2,z3,z4,z6,z1185]),(0,[z0,z2,z3,z108,z5,z13])],[(0,[z0,z3,z4,z5,z468,z61]),(0,[z0,z2,z3,z4,z366,z24]),(0,[z0,z2,z83,z224,z77,z6]),(0,[z0,z2,z3,z874,z132,z6]),(0,[z0,z2,z3,z57,z5,z789]),(0,[z0,z2,z3,z70,z5,z9]),(0,[z808,z2,z3,z4,z5,z24])],[(0,[z0,z2,z3,z4,z129,z62]),(0,[z0,z2,z3,z4,z293,z13]),(0,[z0,z2,z3,z1186,z5,z6]),(0,[z0,z424,z3,z4,z5,z10]),(0,[z0,z2,z3,z70,z5,z446])],[(0,[z0,z2,z3,z4,z5,z1187]),(0,[z0,z2,z3,z4,z5,z1188]),(0,[z0,z2,z3,z4,z5,z1189]),(0,[z0,z2,z3,z4,z6,z1190])],[(0,[z144,z145,z3,z4,z5,z468]),(0,[z0,z2,z3,z1191,z5,z6]),(0,[z0,z2,z3,z115,z5,z6])],[(0,[z0,z2,z3,z89,z5,z6])],[(0,[z27,z2,z3,z4,z55,z166]),(0,[z0,z2,z29,z5,z163,z6]),(0,[z0,z2,z1192,z3,z5,z6])],[(0,[z0,z2,z3,z1193,z5,z6]),(0,[z0,z2,z1194,z4,z5,z6]),(0,[z0,z2,z189,z3,z4,z13]),(0,[z0,z2,z3,z4,z1195,z6]),(0,[z0,z2,z774,z4,z163,z6]),(0,[z0,z2,z3,z4,z98,z24])],[],[(0,[z0,z2,z3,z4,z243,z6]),(0,[z1196,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1197]),(0,[z0,z2,z204,z21,z5,z6]),(0,[z40,z2,z3,z4,z5,z36])],[(0,[z0,z2,z1198,z4,z5,z6]),(0,[z37,z26,z3,z4,z5,z6]),(0,[z0,z26,z204,z4,z5,z6]),(1,[z0,z2,z3,z4,z811])],[(0,[z184,z0,z3,z4,z5,z61]),(0,[z1199,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1200]),(0,[z0,z139,z3,z4,z519,z13]),(0,[z331,z0,z2,z3,z4,z120])]],
   [[(0,[z1201,z2,z3,z4,z5,z6]),(0,[z81,z0,z3,z4,z23,z24])],[(0,[z0,z2,z3,z4,z5,z1202]),(0,[z0,z2,z3,z4,z88,z749]),(0,[z0,z2,z3,z4,z76,z13])],[(0,[z0,z2,z3,z4,z5,z1203])],[(0,[z0,z2,z158,z4,z5,z162]),(0,[z0,z2,z3,z4,z5,z1204]),(0,[z0,z2,z3,z4,z1205,z6]),(0,[z2,z892,z3,z4,z5,z24])],[(0,[z121,z2,z3,z4,z161,z24]),(0,[z276,z0,z8,z4,z5,z6]),(0,[z12,z0,z2,z3,z4,z13])],[(0,[z0,z2,z3,z4,z1206,z6]),(0,[z0,z2,z3,z1207,z5,z6]),(0,[z0,z2,z3,z4,z967,z13])],[(0,[z0,z2,z1136,z4,z5,z13])],[(0,[z0,z2,z3,z4,z1208,z6]),(0,[z0,z2,z3,z4,z5,z1209]),(0,[z0,z2,z3,z275,z4,z13])],[(0,[z0,z2,z3,z4,z1210,z6]),(0,[z0,z2,z148,z3,z5,z13]),(0,[z168,z169,z3,z66,z5,z6]),(0,[z0,z2,z3,z118,z46,z6]),(0,[z1138,z2,z3,z4,z5,z13])],[(0,[z0,z2,z3,z4,z468,z771]),(0,[z175,z2,z3,z4,z293,z6]),(0,[z0,z2,z224,z3,z5,z13])],[(0,[z0,z2,z3,z4,z5,z1211]),(0,[z27,z2,z128,z4,z5,z166]),(0,[z40,z0,z2,z3,z4,z56]),(0,[z28,z0,z8,z4,z5,z13]),(0,[z0,z2,z29,z3,z5,z6])],[(0,[z0,z2,z1212,z4,z5,z6]),(0,[z0,z1213,z3,z4,z5,z6]),(0,[z1214,z2,z3,z4,z5,z6])],[(0,[z27,z2,z3,z4,z5,z521]),(0,[z0,z2,z3,z4,z372,z13]),(0,[z0,z2,z3,z4,z58,z120]),(0,[z0,z2,z158,z4,z5,z875])],[(0,[z618,z2,z104,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1215]),(0,[z0,z2,z29,z192,z5,z6]),(0,[z81,z125,z2,z3,z4,z13])],[(0,[z0,z2,z3,z1216,z5,z6]),(0,[z0,z1217,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1218]),(0,[z0,z2,z3,z4,z5,z1219])],[(0,[z0,z2,z1220,z4,z5,z6]),(0,[z0,z2,z3,z4,z453,z6])]],
   [[(0,[z0,z2,z3,z4,z453,z459])],[(0,[z0,z2,z3,z4,z6,z120]),(0,[z0,z2,z3,z4,z5,z843]),(0,[z0,z2,z159,z5,z47,z6])],[(0,[z30,z2,z3,z31,z5,z6]),(0,[z0,z2,z3,z4,z625,z13]),(0,[z0,z2,z3,z391,z5,z13]),(0,[z0,z139,z3,z4,z205,z6]),(0,[z0,z2,z3,z4,z388,z13])],[(0,[z0,z2,z3,z4,z129,z6]),(0,[z0,z2,z3,z4,z1221,z6]),(0,[z0,z1222,z3,z4,z5,z6])],[(0,[z1223,z0,z2,z3,z4,z5])],[(0,[z0,z2,z1224,z4,z5,z6]),(0,[z2,z3,z4,z5,z859,z166])],[(0,[z0,z2,z3,z402,z5,z13]),(0,[z263,z2,z3,z4,z5,z16]),(0,[z0,z2,z83,z774,z4,z6])],[(0,[z0,z2,z3,z4,z5,z1225]),(0,[z0,z2,z406,z4,z163,z6])],[(0,[z0,z2,z83,z265,z4,z6]),(0,[z505,z0,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z34]),(0,[z0,z2,z1226,z4,z5,z6]),(0,[z331,z0,z2,z3,z4,z13])],[(0,[z37,z2,z3,z4,z38,z6])],[(0,[z0,z2,z1227,z4,z5,z6]),(0,[z28,z0,z2,z29,z5,z6]),(0,[z81,z263,z3,z4,z23,z6]),(0,[z0,z2,z275,z4,z6,z13])],[(0,[z0,z2,z3,z1228,z5,z6]),(0,[z0,z2,z1229,z4,z5,z6]),(0,[z0,z139,z2,z3,z4,z152])],[(0,[z0,z2,z3,z4,z5,z1230]),(0,[z0,z361,z3,z4,z5,z737])],[(0,[z0,z2,z3,z134,z5,z13]),(0,[z1231,z0,z2,z3,z4,z5]),(0,[z0,z2,z1232,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1233]),(0,[z0,z2,z3,z4,z5,z1234]),(0,[z121,z226,z3,z4,z161,z6]),(0,[z0,z2,z1038,z4,z5,z6]),(0,[z40,z2,z3,z4,z5,z342]),(0,[z1235,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z182,z13])]],
   [[(0,[z0,z2,z75,z5,z47,z6])],[(0,[z0,z2,z3,z4,z5,z468])],[(0,[z0,z2,z3,z45,z5,z6]),(0,[z0,z2,z3,z4,z1236,z6]),(0,[z0,z2,z3,z4,z5,z1237])],[(0,[z203,z0,z2,z158,z4,z5]),(0,[z0,z2,z1238,z4,z5,z6]),(0,[z0,z2,z3,z4,z716,z13]),(0,[z587,z0,z3,z4,z5,z61]),(0,[z2,z3,z4,z5,z6,z1030])],[(0,[z0,z2,z3,z4,z5,z811])],[(0,[z0,z2,z3,z4,z5,z1239]),(0,[z121,z2,z3,z4,z161,z560]),(0,[z0,z245,z128,z4,z5,z6]),(0,[z0,z2,z3,z391,z170,z6])],[(0,[z175,z2,z3,z391,z5,z6]),(0,[z81,z0,z3,z4,z188,z6]),(0,[z0,z2,z91,z94,z5,z6])],[(1,[z0,z3,z4,z729,z6])],[(0,[z133,z110,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z1240,z6]),(0,[z2,z1241,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1242,z5,z6]),(0,[z0,z2,z3,z402,z170,z6]),(0,[z0,z65,z3,z813,z5,z6])],[(0,[z175,z2,z3,z402,z5,z6])],[(0,[z27,z245,z3,z4,z5,z166]),(0,[z0,z90,z2,z29,z5,z6])],[(0,[z49,z0,z2,z3,z89,z5]),(0,[z0,z2,z3,z1243,z5,z6])],[(0,[z0,z2,z39,z4,z5,z61]),(0,[z40,z0,z2,z3,z4,z120])],[(0,[z0,z2,z3,z4,z657,z13]),(0,[z0,z139,z3,z4,z543,z6]),(0,[z1244,z0,z2,z3,z4,z5]),(0,[z0,z2,z275,z4,z23,z6])],[(0,[z0,z2,z427,z3,z4,z13]),(0,[z0,z2,z461,z3,z5,z479])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 512).take 507) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1019).take 265) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1284)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [512, 507, 265] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 148).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 148).take 141).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 289).take 145).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 434).take 78).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [148, 141, 145, 78] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_38037

theorem PEqualNP.Outside.L_meta_38037 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277071040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277071040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38037.solve