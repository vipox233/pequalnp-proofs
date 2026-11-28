import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36306

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
  Nat.testBit (4277075688 * 2 ^ 32 + 4277074656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x20800408b0110b10#64 ++ 0x020800408b0110b1#64 ++ 0xdf414c19f0b31f3f#64 ++ 0xbdf414c19f0b31f3#64 : BitVec 256),
   (0x4500106251149941#64 ++ 0x0450010625114994#64 ++ 0xbef2b0e6735c99c7#64 ++ 0x7bef2b0e6735c99c#64 : BitVec 256),
   (0x0a04c105046020a2#64 ++ 0x20a04c105046020a#64 ++ 0x75ccc3078c60e1fe#64 ++ 0xf75ccc3078c60e1f#64 : BitVec 256),
   (0x840b02b00b80d408#64 ++ 0x4840b02b00b80d40#64 ++ 0xf3ef03f80f80fe0d#64 ++ 0xef3ef03f80f80fe0#64 : BitVec 256),
   (0x080fe8000eea000c#64 ++ 0x7080fe8000eea000#64 ++ 0x0fdffc000fff0003#64 ++ 0xe0fdffc000fff000#64 : BitVec 256),
   (0xf02fffdfe0000000#64 ++ 0x7f02fffdfe000000#64 ++ 0xffeffffff0000000#64 ++ 0x1ffeffffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [9, 3]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [12, 10]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75ccc3078c60e1fe 0xf75ccc3078c60e1f

def z1 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x7fdfff078fffe1ff 0xf7fdfff078fffe1f

def z2 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf414c19f0b31f3f 0xbdf414c19f0b31f3

def z3 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2b0e6735c99c7 0x7bef2b0e6735c99c

def z4 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03f80f80fe0d 0xef3ef03f80f80fe0

def z5 : W := mkw 0x8e0fc3b50fe0f4aa 0x68e0fc3b50fe0f4a 0xf7efc3ff8fe0ffff 0xff7efc3ff8fe0fff

def z6 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0000000 0x1ffeffffff000000

def z7 : W := mkw 0x0080000010110b10 0x00080000010110b1 0x0000000000b31f3f 0xa0000000000b31f3

def z8 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc000fff0003 0xe0fdffc000fff000

def z9 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc60e1fe 0xfffeffffffc60e1f

def z10 : W := mkw 0x0400002001009000 0x0040000200100900 0xb2e200e003009805 0x6b2e200e00300980

def z11 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x8a233cf870000000 0x08a233cf87000000

def z12 : W := mkw 0x24800428bb91df18 0x024800428bb91df1 0xdf414c19ffb3ff3f 0xfdf414c19ffb3ff3

def z13 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0a133c00039f0001 0x00a133c00039f000

def z14 : W := mkw 0x040000200b80d408 0x0040000200b80d40 0x000000000f80fe0d 0xe000000000f80fe0

def z15 : W := mkw 0xf8afffdffefb0b1c 0x7f8afffdffefb0b1 0xffffffffffff1f3f 0xfffffffffffff1f3

def z16 : W := mkw 0x4500106241049041 0x0450010624104904 0x003230e0030c0000 0x0003230e0030c000

def z17 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x410c43018c206038 0x8410c43018c20603

def z18 : W := mkw 0x20000408a0000000 0x020000408a000000 0xdf414c19f0000000 0x1df414c19f000000

def z19 : W := mkw 0x4500106251149941 0x0450010625114994 0x8a3230e0731c1801 0x08a3230e0731c180

def z20 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf02003fff0000000 0x1f02003fff000000

def z21 : W := mkw 0xf22017dfe00020a2 0x0f22017dfe00020a 0xf02003fff000e1fc 0x1f02003fff000e1f

def z22 : W := mkw 0x000fe90500000000 0x7000fe9050000000 0x7fcfff0780000000 0x17fcfff078000000

def z23 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x010d4c000ca30000 0x8010d4c000ca3000

def z24 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffeffffffca30000 0x9ffeffffffca3000

def z25 : W := mkw 0x8e0b02b00fe0f4aa 0x48e0b02b00fe0f4a 0xf3ef03f80fe0ffff 0xef3ef03f80fe0fff

def z26 : W := mkw 0x0000000010100900 0x0000000001010090 0x0000000000101907 0x2000000000010190

def z27 : W := mkw 0x0580002011159b51 0x00580002011159b5 0x0010000003ff9fff 0xe0010000003ff9ff

def z28 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0xfff3fcfff3ff9fff 0xffff3fcfff3ff9ff

def z29 : W := mkw 0x050000201b94dd49 0x0050000201b94dd4 0x001000000fdcffcf 0xe001000000fdcffc

def z30 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x0400c007806001f2 0x10400c007806001f

def z31 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffffff0003 0xfffffffffffff000

def z32 : W := mkw 0x080fe9050eea000c 0x7080fe9050eea000 0x7fdfff078fff0003 0xf7fdfff078fff000

def z33 : W := mkw 0xf024d7dfe0000000 0x2f024d7dfe000000 0xf5ecc3fff0000000 0x1f5ecc3fff000000

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0x0f414c0000b30003 0xa0f414c0000b3000

def z35 : W := mkw 0x4500106251149941 0x0450010625114994 0xbff3fce673ff99c7 0xfbff3fce673ff99c

def z36 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000035c99c7 0x600100000035c99c

def z37 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x20ae03e00f00e000 0x420ae03e00f00e00

def z38 : W := mkw 0x7024fd4fe0000000 0x37024fd4fe000000 0xbee2fce7f0000000 0x1bee2fce7f000000

def z39 : W := mkw 0x000b00000a800008 0x4000b00000a80000 0x03cf00000f800001 0xe03cf00000f80000

def z40 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x009eb0000f4c0000 0x4009eb0000f4c000

def z41 : W := mkw 0x080000000eea000c 0x0080000000eea000 0x000000000ca30000 0x8000000000ca3000

def z42 : W := mkw 0x2a84c50db4712bb2 0x22a84c50db4712bb 0xffcdcf1ffcf3ffff 0xfffcdcf1ffcf3fff

def z43 : W := mkw 0x0000000000000000 0x0000000000000000 0x71cc03000c00e00c 0xe71cc03000c00e00

def z44 : W := mkw 0x4500106251149941 0x0450010625114994 0xb02000e6700099c4 0x1b02000e6700099c

def z45 : W := mkw 0xf42fffffe1009000 0x7f42fffffe100900 0xffeffffff3009805 0x7ffeffffff300980

def z46 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x410d03180f80fe0d 0xe410d03180f80fe0

def z47 : W := mkw 0xf42fffffeb80d408 0x7f42fffffeb80d40 0xffefffffff80fe0d 0xfffefffffff80fe0

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x8201001800801e01 0x08201001800801e0

def z49 : W := mkw 0x4500106251149941 0x0450010625114994 0x2cb2b0e6735c81c2 0x52cb2b0e6735c81c

def z50 : W := mkw 0x4000104240000000 0x0400010424000000 0xbef2b0e6735c0003 0x7bef2b0e6735c000

def z51 : W := mkw 0x0804e800046a0004 0x30804e800046a000 0x0c10fc00007f0002 0x00c10fc00007f000

def z52 : W := mkw 0x840002b00100d400 0x0840002b00100d40 0xf02003f80000fe0c 0x0f02003f80000fe0

def z53 : W := mkw 0xf42fffffeb80d408 0x7f42fffffeb80d40 0xffeffffff3801e01 0x1ffeffffff3801e0

def z54 : W := mkw 0x288fec08befb0b1c 0x7288fec08befb0b1 0xdfdffc19ffff1f3f 0xfdfdffc19ffff1f3

def z55 : W := mkw 0x4000104240000000 0x0400010424000000 0xbee2b0e670000000 0x1bee2b0e67000000

def z56 : W := mkw 0x080000000eea000c 0x0080000000eea000 0x001000000fff0003 0xe001000000fff000

def z57 : W := mkw 0xf0afffdff0110b10 0x7f0afffdff0110b1 0xffeffffff0330132 0x1ffeffffff033013

def z58 : W := mkw 0xa00b0698a0000000 0x4a00b0698a000000 0xffef4ff9f0000000 0x1ffef4ff9f000000

def z59 : W := mkw 0x4b04d147547429e3 0x24b04d147547429e 0x7ddcf307fc7ce1fe 0xf7ddcf307fc7ce1f

def z60 : W := mkw 0x0000000000000000 0x0000000000000000 0x34c08006004081c6 0x734c08006004081c

def z61 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x3fdffc060fff81c7 0xf3fdffc060fff81c

def z62 : W := mkw 0x0004c10500000000 0x20004c1050000000 0x75ccc30780000000 0x175ccc3078000000

def z63 : W := mkw 0x02000105000020a2 0x002000105000020a 0x00000007800001f0 0x100000007800001f

def z64 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x208c83060c40e0c0 0x4208c83060c40e0c

def z65 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x8a010c1870931e01 0x08a010c1870931e0

def z66 : W := mkw 0x20800408a0010210 0x020800408a001021 0x00004c0180230030 0x000004c018023003

def z67 : W := mkw 0xf0ab3edaf0110b10 0x5f0ab3edaf0110b1 0x8a233cf870931e01 0x08a233cf870931e0

def z68 : W := mkw 0xf0afffdff0110b10 0x7f0afffdff0110b1 0xffeffffff0b31f3f 0xbffeffffff0b31f3

def z69 : W := mkw 0x040b00200b809008 0x4040b00200b80900 0xb3ef00e00f809805 0xeb3ef00e00f80980

def z70 : W := mkw 0x0e04c1250fe0f4aa 0x20e04c1250fe0f4a 0x75ccc3078fe0ffff 0xf75ccc3078fe0fff

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x0ed2b000035c0003 0x60ed2b000035c000

def z72 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xf12d4ffff0000000 0x1f12d4ffff000000

def z73 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x4fdfff018fff603b 0xe4fdfff018fff603

def z74 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0xf02000fff0009ffc 0x1f02000fff0009ff

def z75 : W := mkw 0x4100104250140941 0x0410010425014094 0x0c10b006705c01c2 0x10c10b006705c01c

def z76 : W := mkw 0x4d0ff8625ffe994d 0x74d0ff8625ffe994 0xbffffce67fff99c7 0xfbffffce67fff99c

def z77 : W := mkw 0x20000408a0000000 0x020000408a000000 0xdf414c19f0b30003 0xbdf414c19f0b3000

def z78 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0f537c0003bf0003 0xa0f537c0003bf000

def z79 : W := mkw 0x840002b00b80d408 0x0840002b00b80d40 0xf02003f80f80fe0d 0xef02003f80f80fe0

def z80 : W := mkw 0x20800408a0010210 0x020800408a001021 0xdf414c19f0a30638 0x9df414c19f0a3063

def z81 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x822300f803801e01 0x0822300f803801e0

def z82 : W := mkw 0xa48b06b8bb91df18 0x4a48b06b8bb91df1 0xffef4ff9ffb3ff3f 0xfffef4ff9ffb3ff3

def z83 : W := mkw 0x4500106241049041 0x0450010624104904 0x20b2b0e6034c80c0 0x420b2b0e6034c80c

def z84 : W := mkw 0x4500106251149941 0x0450010625114994 0xbe6000e6701099c7 0x3be6000e6701099c

def z85 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0a9fbc000fdf0001 0x40a9fbc000fdf000

def z86 : W := mkw 0x0000000010100900 0x0000000001010090 0x9e40000070101907 0x39e4000007010190

def z87 : W := mkw 0x0804c00004600000 0x20804c0000460000 0x010c40000c200000 0x8010c40000c20000

def z88 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x4d0dff1ff0000000 0x14d0dff1ff000000

def z89 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x2fdfff060fffe0c3 0xe2fdfff060fffe0c

def z90 : W := mkw 0xd02ffbd740000000 0x7d02ffbd74000000 0x20aeb3e600000000 0x020aeb3e60000000

def z91 : W := mkw 0x0a000000046020a2 0x00a000000046020a 0x000000000c40e0c0 0x4000000000c40e0c

def z92 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffff06001f2 0x1ffeffffff06001f

def z93 : W := mkw 0x0500002001049041 0x0050000200104904 0x00100000034c80c0 0x400100000034c80c

def z94 : W := mkw 0x208b2c08ba9b0b1c 0x5208b2c08ba9b0b1 0xdf537c19f3bf1f3f 0xbdf537c19f3bf1f3

def z95 : W := mkw 0x7024fd4fe0000000 0x37024fd4fe000000 0x0c00fc07f0000000 0x10c00fc07f000000

def z96 : W := mkw 0x02000105000020a2 0x002000105000020a 0x700003078000e1fc 0x1700003078000e1f

def z97 : W := mkw 0x8e0fc3b50fe0f4aa 0x68e0fc3b50fe0f4a 0xf3ef43f98fa0fe3d 0xef3ef43f98fa0fe3

def z98 : W := mkw 0x800b029000000000 0x4800b02900000000 0xf3ef03f800000000 0x0f3ef03f80000000

def z99 : W := mkw 0x8a0fc395046020a2 0x68a0fc395046020a 0xf7efc3ff8c60e1fe 0xff7efc3ff8c60e1f

def z100 : W := mkw 0x20000408a0000000 0x020000408a000000 0xd0000019f0000000 0x1d0000019f000000

def z101 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0xdfdffc180fff1e0f 0xedfdffc180fff1e0

def z102 : W := mkw 0x048000201b91df18 0x0048000201b91df1 0x000000000fb3ff3f 0xe000000000fb3ff3

def z103 : W := mkw 0x4500106241049041 0x0450010624104904 0xbef2b0e6734c80c0 0x5bef2b0e6734c80c

def z104 : W := mkw 0x8c0feab00fead40c 0x78c0feab00fead40 0xfffffff80ffffe0f 0xefffffff80ffffe0

def z105 : W := mkw 0x840002b00100d400 0x0840002b00100d40 0xf1ec03f80c00fe0c 0xef1ec03f80c00fe0

def z106 : W := mkw 0x7024fd4fe0000000 0x37024fd4fe000000 0x7dccff07f0000000 0x17dccff07f000000

def z107 : W := mkw 0xf42b3efaeb80d408 0x5f42b3efaeb80d40 0xfbef3ff87f80fe0d 0xefbef3ff87f80fe0

def z108 : W := mkw 0xc00b12d240000000 0x4c00b12d24000000 0xffefb3fe70000000 0x1ffefb3fe7000000

def z109 : W := mkw 0xb82fef9daeea000c 0x7b82fef9daeea000 0x4fdfff198fff0003 0xe4fdfff198fff000

def z110 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdfd3fc19f3ff1f3f 0xfdfd3fc19f3ff1f3

def z111 : W := mkw 0x000b00000a800008 0x4000b00000a80000 0x010d00000c800000 0x8010d00000c80000

def z112 : W := mkw 0x000fe80000000000 0x7000fe8000000000 0x0fcffc0000000000 0x00fcffc000000000

def z113 : W := mkw 0x20000408a0000000 0x020000408a000000 0xdf414c19f020013e 0xbdf414c19f020013

def z114 : W := mkw 0xb02fef9da0000000 0x7b02fef9da000000 0x410d4f1980000000 0x0410d4f198000000

def z115 : W := mkw 0x4500106251149941 0x0450010625114994 0xb4e080e6704099c6 0x7b4e080e6704099c

def z116 : W := mkw 0x0f04c1251574b9e3 0x20f04c1251574b9e 0x75dcc3078f7cf9ff 0xf75dcc3078f7cf9f

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0x554040018020013e 0xb554040018020013

def z118 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a010c0000930001 0x00a010c000093000

def z119 : W := mkw 0x02000105000020a2 0x002000105000020a 0x71cc03078c00e1fc 0xf71cc03078c00e1f

def z120 : W := mkw 0x20800408a0010210 0x020800408a001021 0x41014c1980a30638 0x841014c1980a3063

def z121 : W := mkw 0x4500106251149941 0x0450010625114994 0xfffeb3e67f5cf9cf 0xffffeb3e67f5cf9c

def z122 : W := mkw 0x4500106251149941 0x0450010625114994 0xba3230e6731c99c5 0x1ba3230e6731c99c

def z123 : W := mkw 0x0804c00004600000 0x20804c0000460000 0x05ccc0000c600002 0xe05ccc0000c60000

def z124 : W := mkw 0x800b029000000000 0x4800b02900000000 0x20ae03e000000000 0x020ae03e00000000

def z125 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x8f414c1870b31e03 0xa8f414c1870b31e0

def z126 : W := mkw 0xfa2fffdfeeea20ae 0x7fa2fffdfeeea20a 0xffffffffffffe1ff 0xfffffffffffffe1f

def z127 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x7fdfff000fffe00f 0xe7fdfff000fffe00

def z128 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x0c004c01f0330132 0x10c004c01f033013

def z129 : W := mkw 0x8c0fc2b00fe0d408 0x68c0fc2b00fe0d40 0xf7efc3f80fe0fe0f 0xef7efc3f80fe0fe0

def z130 : W := mkw 0xf02b17dfe0000000 0x4f02b17dfe000000 0xf3ef03fff0000000 0x1f3ef03fff000000

def z131 : W := mkw 0x4b04d147547429e3 0x24b04d147547429e 0x0c10f007f07c01f2 0x10c10f007f07c01f

def z132 : W := mkw 0xd02ffbd740000000 0x7d02ffbd74000000 0xbeeeb3e670000000 0x1beeeb3e67000000

def z133 : W := mkw 0x800b02900a804408 0x4800b02900a80440 0x410d03180c806608 0x8410d03180c80660

def z134 : W := mkw 0x840feab00b80d408 0x7840feab00b80d40 0xffeffff80f80fe0d 0xeffeffff80f80fe0

def z135 : W := mkw 0x470011675114b9e3 0x0470011675114b9e 0xf02003e7f000f9fc 0x1f02003e7f000f9f

def z136 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x618cc3078c60e0f8 0xc618cc3078c60e0f

def z137 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xffffb3f80fdcfe0f 0xeffffb3f80fdcfe0

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0xd341001800801e0d 0xad341001800801e0

def z139 : W := mkw 0x4a04d147446020a2 0x24a04d147446020a 0xffeef3e7fc60e1fe 0xfffeef3e7fc60e1f

def z140 : W := mkw 0x0000000010100900 0x0000000001010090 0x9f414c0070b31907 0xb9f414c0070b3190

def z141 : W := mkw 0x4d04d06255749941 0x24d04d0625574994 0xbffef0e67f7c99c7 0xfbffef0e67f7c99c

def z142 : W := mkw 0xfaafffdff4712bb2 0x7faafffdff4712bb 0xffeffffffcf3ffff 0xfffeffffffcf3fff

def z143 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x0000400180200030 0x0000040018020003

def z144 : W := mkw 0x4000104240000000 0x0400010424000000 0xbee2b0e6704081c6 0x7bee2b0e6704081c

def z145 : W := mkw 0xf02fffdfea800008 0x7f02fffdfea80000 0xffefffffff800001 0xfffefffffff80000

def z146 : W := mkw 0x4000104240000000 0x0400010424000000 0xb02000e670000000 0x1b02000e67000000

def z147 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x61afffff80000000 0x061afffff8000000

def z148 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xd5404019f0201f3e 0xbd5404019f0201f3

def z149 : W := mkw 0x4580106251159b51 0x04580106251159b5 0xbef2b0e673ff9fff 0xfbef2b0e673ff9ff

def z150 : W := mkw 0xf0afffdff0110b10 0x7f0afffdff0110b1 0xffeffffff0001f3c 0x1ffeffffff0001f3

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0x3ed2b006035c81c7 0x73ed2b006035c81c

def z152 : W := mkw 0x840002b00100d400 0x0840002b00100d40 0xf2e203f80300fe0d 0x6f2e203f80300fe0

def z153 : W := mkw 0xf024ffdfe0000000 0x3f024ffdfe000000 0xfc20fffff0000000 0x1fc20fffff000000

def z154 : W := mkw 0x450010625b94dd49 0x0450010625b94dd4 0xbef2b0e67fdcffcf 0xfbef2b0e67fdcffc

def z155 : W := mkw 0x0a84c10514712bb2 0x20a84c10514712bb 0x75ccc3078cf3ffff 0xf75ccc3078cf3fff

def z156 : W := mkw 0x0d0fe8201ffe994d 0x70d0fe8201ffe994 0x0fdffc000fff99c7 0xe0fdffc000fff99c

def z157 : W := mkw 0x0c0fe8200fead40c 0x70c0fe8200fead40 0x0fdffc000ffffe0f 0xe0fdffc000ffffe0

def z158 : W := mkw 0xd02013d740000000 0x0d02013d74000000 0x202003e600000000 0x0202003e60000000

def z159 : W := mkw 0x4004d14740000000 0x24004d1474000000 0xffeef3e7f0000000 0x1ffeef3e7f000000

def z160 : W := mkw 0x4d0ff8625ffe994d 0x74d0ff8625ffe994 0x8ffffce07fff1803 0xe8ffffce07fff180

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x75cc83060c40e1ce 0xf75cc83060c40e1c

def z162 : W := mkw 0x840b2ab00b8ad40c 0x5840b2ab00b8ad40 0xfbff3ff80f9ffe0d 0xefbff3ff80f9ffe0

def z163 : W := mkw 0x4500106251149941 0x0450010625114994 0xfff2f0e7f37c99ff 0xffff2f0e7f37c99f

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x30c0000000008004 0x630c000000000800

def z165 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xc32f03f80f807e09 0x8c32f03f80f807e0

def z166 : W := mkw 0x0000000010100900 0x0000000001010090 0xbec08006705099c7 0x7bec08006705099c

def z167 : W := mkw 0x0a0fe8000eea20ae 0x70a0fe8000eea20a 0x0fdffc000fffe1ff 0xe0fdffc000fffe1f

def z168 : W := mkw 0xf5affffff1159b51 0x7f5affffff1159b5 0xfffffffff3ff9fff 0xffffffffff3ff9ff

def z169 : W := mkw 0x0a000000046020a2 0x00a000000046020a 0x34c080060c60e1fe 0xf34c080060c60e1f

def z170 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75ccc307806001f2 0x175ccc307806001f

def z171 : W := mkw 0xa48006b8b111df10 0x0a48006b8b111df1 0xff614ff9f0b3ff3f 0xbff614ff9f0b3ff3

def z172 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x0f414c01f0b30133 0xb0f414c01f0b3013

def z173 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffff4c0000 0x5ffffffffff4c000

def z174 : W := mkw 0x4500106251149941 0x0450010625114994 0x8e32b0e6735c19c3 0x18e32b0e6735c19c

def z175 : W := mkw 0x880fea900eea440c 0x7880fea900eea440 0x4fdfff180fff660b 0xe4fdfff180fff660

def z176 : W := mkw 0x4f04d1675574b9e3 0x24f04d1675574b9e 0xfffef3e7ff7cf9ff 0xffffef3e7ff7cf9f

def z177 : W := mkw 0x4500106251149941 0x0450010625114994 0x8ef2b0e0735c1803 0x68ef2b0e0735c180

def z178 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xffef4ff80fb3fe0f 0xeffef4ff80fb3fe0

def z179 : W := mkw 0x4d0010625ffe994d 0x04d0010625ffe994 0xbef2b0e67fff99c7 0xfbef2b0e67fff99c

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x0fd3fc0003ff0003 0xe0fd3fc0003ff000

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x01cc00000c000000 0xe01cc00000c00000

def z182 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xd0000019f0001f3c 0x1d0000019f0001f3

def z183 : W := mkw 0x0a000000046020a2 0x00a000000046020a 0x00000000006001f2 0x000000000006001f

def z184 : W := mkw 0xf52017fff1149941 0x0f52017fff114994 0xfef2b3fff35c99c7 0x7fef2b3fff35c99c

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0x9e40000070000000 0x19e4000007000000

def z186 : W := mkw 0x000b00000a800008 0x4000b00000a80000 0x0203000003800001 0x0020300000380000

def z187 : W := mkw 0x0004c10500000000 0x20004c1050000000 0x75ccc3078c00e00c 0xf75ccc3078c00e00

def z188 : W := mkw 0xf0a017dff0110b10 0x0f0a017dff0110b1 0xff614ffff0b31f3f 0xbff614ffff0b31f3

def z189 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x9e404c01f0331937 0x39e404c01f033193

def z190 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x011d4c000fff0003 0xe011d4c000fff000

def z191 : W := mkw 0x4100104250140941 0x0410010425014094 0xbef2b0e6705c01c2 0x1bef2b0e6705c01c

def z192 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xbee3bcfe70000000 0x1bee3bcfe7000000

def z193 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x209eb3060f4ce0c0 0x4209eb3060f4ce0c

def z194 : W := mkw 0xf12fffdff0140941 0x7f12fffdff014094 0xfffffffff05c01c2 0x1fffffffff05c01c

def z195 : W := mkw 0x288fec08befb0b1c 0x7288fec08befb0b1 0xdf4d4c19fcb31f3f 0xbdf4d4c19fcb31f3

def z196 : W := mkw 0x0400002001009000 0x0040000200100900 0x0000000003009805 0x6000000000300980

def z197 : W := mkw 0x288fec08befb0b1c 0x7288fec08befb0b1 0x8fdffc187fff1e03 0xe8fdffc187fff1e0

def z198 : W := mkw 0x080b28000eea000c 0x5080b28000eea000 0x0a133c000fff0003 0xe0a133c000fff000

def z199 : W := mkw 0x000b00000a800008 0x4000b00000a80000 0x73cf03000f80e00d 0xe73cf03000f80e00

def z200 : W := mkw 0x800b02900a804408 0x4800b02900a80440 0x43cf03180f806609 0xe43cf03180f80660

def z201 : W := mkw 0xd02b3ad240000000 0x5d02b3ad24000000 0x002230e000000000 0x0002230e00000000

def z202 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x8e014c19f0b31f33 0x18e014c19f0b31f3

def z203 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x45ccc3018c60603a 0xe45ccc3018c60603

def z204 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x822300f80f80fe0d 0xe822300f80f80fe0

def z205 : W := mkw 0xfe2fffffefe0f4aa 0x7fe2fffffefe0f4a 0xffefffffffe0ffff 0xfffefffffffe0fff

def z206 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z207 : W := mkw 0x2084c50db0110b10 0x22084c50db0110b1 0xffcdcf1ff0b31f3f 0xbffcdcf1ff0b31f3

def z208 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2b0e6731c1801 0x1bef2b0e6731c180

def z209 : W := mkw 0x0a000000046020a2 0x00a000000046020a 0x554040018c60e1fe 0xf554040018c60e1f

def z210 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xfee2b3fff0000000 0x1fee2b3fff000000

def z211 : W := mkw 0x0000000000000000 0x0000000000000000 0xf3cd03180c80fe0d 0xef3cd03180c80fe0

def z212 : W := mkw 0x800fea9000000000 0x7800fea900000000 0xffeffff800000000 0x0ffeffff80000000

def z213 : W := mkw 0x4500106251149941 0x0450010625114994 0xfff3b0fe73dc9fcf 0xffff3b0fe73dc9fc

def z214 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xd1014c19f0a31f3c 0x9d1014c19f0a31f3

def z215 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xa2af03f80f80fe01 0x4a2af03f80f80fe0

def z216 : W := mkw 0x800fc39500000000 0x6800fc3950000000 0xf7efc3ff80000000 0x1f7efc3ff8000000

def z217 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf7ef43f98fa0ff3f 0xff7ef43f98fa0ff3

def z218 : W := mkw 0x7a24fd4fe46020a2 0x37a24fd4fe46020a 0x0c00fc07f06001f2 0x10c00fc07f06001f

def z219 : W := mkw 0x0400002001009000 0x0040000200100900 0xf3e300f803809e0d 0xef3e300f803809e0

def z220 : W := mkw 0x288fec08aeeb021c 0x7288fec08aeeb021 0x410d4c198ca30638 0x8410d4c198ca3063

def z221 : W := mkw 0x8e0fc3b50fe0f4aa 0x68e0fc3b50fe0f4a 0xf3ef83fe0fc0fecd 0xef3ef83fe0fc0fec

def z222 : W := mkw 0xf02016dae0000000 0x0f02016dae000000 0x802000f870000000 0x0802000f87000000

def z223 : W := mkw 0xf0ab3edaf0110b10 0x5f0ab3edaf0110b1 0xdf637cf9f0b31f3f 0xbdf637cf9f0b31f3

def z224 : W := mkw 0xc50b12f25b94dd49 0x4c50b12f25b94dd4 0xffffb3fe7fdcffcf 0xfffffb3fe7fdcffc

def z225 : W := mkw 0xae8fc7bdbff1ffba 0x6ae8fc7bdbff1ffb 0xffefcffffff3ffff 0xfffefcffffff3fff

def z226 : W := mkw 0x4500106251149941 0x0450010625114994 0x8a3230e0735c99c7 0x68a3230e0735c99c

def z227 : W := mkw 0x000fe8000a8a000c 0x7000fe8000a8a000 0x0fdffc00039f0001 0x00fdffc00039f000

def z228 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x61af03f80f80e608 0xc61af03f80f80e60

def z229 : W := mkw 0x4000104240000000 0x0400010424000000 0x8a2230e070000000 0x08a2230e07000000

def z230 : W := mkw 0x0a04e905046a20a6 0x30a04e905046a20a 0x7ddcff078c7fe1fe 0xf7ddcff078c7fe1f

def z231 : W := mkw 0x0080000010110b10 0x00080000010110b1 0x0000000000931e01 0x00000000000931e0

def z232 : W := mkw 0xf02ffedae0000000 0x7f02ffedae000000 0x8feffcf870000000 0x08feffcf87000000

def z233 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x248cc3078c60e1f2 0x5248cc3078c60e1f

def z234 : W := mkw 0x4d0ff8624fee904d 0x74d0ff8624fee904 0x20beb0e60f4c80c0 0x420beb0e60f4c80c

def z235 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xda010c19f0931f3d 0x1da010c19f0931f3

def z236 : W := mkw 0xb02fef9da0000000 0x7b02fef9da000000 0x4fcfff1980000000 0x04fcfff198000000

def z237 : W := mkw 0x6500146af1149941 0x06500146af114994 0xfff3fcfff35c99c7 0x7fff3fcfff35c99c

def z238 : W := mkw 0x0804c00004600000 0x20804c0000460000 0x0400c00000600002 0x00400c0000060000

def z239 : W := mkw 0x000b00000a800008 0x4000b00000a80000 0xd3cf00180f801e0d 0xed3cf00180f801e0

def z240 : W := mkw 0x0000000000000000 0x0000000000000000 0x02c2000003000001 0x602c200000300000

def z241 : W := mkw 0x02000105000020a2 0x002000105000020a 0x74c083078040e1fe 0x774c083078040e1f

def z242 : W := mkw 0x20800408a0010210 0x020800408a001021 0x55414c1980a3073e 0xb55414c1980a3073

def z243 : W := mkw 0x860003b50100f4a2 0x0860003b50100f4a 0xf02003ff8000fffc 0x1f02003ff8000fff

def z244 : W := mkw 0x0000000000000000 0x0000000000000000 0x4101001800800608 0x8410100180080060

def z245 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0xdf737cf9f3bf1f3f 0xbdf737cf9f3bf1f3

def z246 : W := mkw 0xf0afffdfe0010210 0x7f0afffdfe001021 0xffeffffff0a30638 0x9ffeffffff0a3063

def z247 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xd3410019f0801f3d 0xbd3410019f0801f3

def z248 : W := mkw 0x800b029000000000 0x4800b02900000000 0x822300f800000000 0x0822300f80000000

def z249 : W := mkw 0x450b38625b9e994d 0x5450b38625b9e994 0xbef3bce673df99c7 0x7bef3bce673df99c

def z250 : W := mkw 0x2884ec08b47b0b14 0x32884ec08b47b0b1 0xdf51fc19f0ff1f3f 0xbdf51fc19f0ff1f3

def z251 : W := mkw 0x0804e800046a0004 0x30804e800046a000 0x00004c0000230000 0x000004c000023000

def z252 : W := mkw 0xf02b3edaea8a000c 0x5f02b3edaea8a000 0x8a333cf8739f0001 0x08a333cf8739f000

def z253 : W := mkw 0x040000200100d400 0x0040000200100d40 0x000000000000fe0c 0x0000000000000fe0

def z254 : W := mkw 0x0804c0000eea000c 0x20804c0000eea000 0x05dcc0000fff0003 0xe05dcc0000fff000

def z255 : W := mkw 0x080b00000eea000c 0x4080b00000eea000 0x03df00000fff0003 0xe03df00000fff000

def z256 : W := mkw 0x0000000010100900 0x0000000001010090 0x9000000070001904 0x1900000007000190

def z257 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf7ef83fe0fc0ffcf 0xff7ef83fe0fc0ffc

def z258 : W := mkw 0x800b029000000000 0x4800b02900000000 0xf3ef03f80c00e00c 0xef3ef03f80c00e00

def z259 : W := mkw 0x0000000010100900 0x0000000001010090 0xdf404001f030193f 0xbdf404001f030193

def z260 : W := mkw 0x4500106241049041 0x0450010624104904 0x2ef2b0e6035c80c3 0x62ef2b0e6035c80c

def z261 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc40e0c0 0x5ffeffffffc40e0c

def z262 : W := mkw 0xda2ffbd7446020a2 0x7da2ffbd7446020a 0x75eef3e78c60e1fe 0xf75eef3e78c60e1f

def z263 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x000c03000c006000 0x0000c03000c00600

def z264 : W := mkw 0x8e0fc3b50fe0f4aa 0x68e0fc3b50fe0f4a 0x20ae83e60f40e0c0 0x420ae83e60f40e0c

def z265 : W := mkw 0x0804e8000eea000c 0x30804e8000eea000 0x0c10fc000fff0003 0xe0c10fc000fff000

def z266 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x00010c0000830000 0x000010c000083000

def z267 : W := mkw 0x0000000000000000 0x0000000000000000 0x208c03000c00e000 0x4208c03000c00e00

def z268 : W := mkw 0xd52ffbf751149941 0x7d52ffbf75114994 0xbefeb3e6735c99c7 0x7befeb3e6735c99c

def z269 : W := mkw 0x0000000000000000 0x0000000000000000 0xb2e200e000000000 0x0b2e200e00000000

def z270 : W := mkw 0x840002b00100d400 0x0840002b00100d40 0x202003e00000e000 0x0202003e00000e00

def z271 : W := mkw 0x70203c4ae0000000 0x170203c4ae000000 0x08003c0070000000 0x008003c007000000

def z272 : W := mkw 0x0400002001009000 0x0040000200100900 0x20a200e003008000 0x420a200e00300800

def z273 : W := mkw 0x0a04c000046020a2 0x20a04c000046020a 0x05ccc0000c60e1fe 0xe05ccc0000c60e1f

def z274 : W := mkw 0x880fea900eea000c 0x7880fea900eea000 0xfffffff80fff0003 0xefffffff80fff000

def z275 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x8000001870001e00 0x08000001870001e0

def z276 : W := mkw 0x0804e800046a0004 0x30804e800046a000 0x0ed2fc00037f0003 0x60ed2fc00037f000

def z277 : W := mkw 0x7a24fd4fe46020a2 0x37a24fd4fe46020a 0x7dccff07fc60e1fe 0xf7dccff07fc60e1f

def z278 : W := mkw 0x080fe80004600000 0x7080fe8000460000 0x0fcffc000c600002 0xe0fcffc000c60000

def z279 : W := mkw 0x840b2ab00b8ad40c 0x5840b2ab00b8ad40 0x8a333cf8039f1e01 0x08a333cf8039f1e0

def z280 : W := mkw 0xf52017fff1149941 0x0f52017fff114994 0xf02003fff00099c4 0x1f02003fff00099c

def z281 : W := mkw 0xf52fffffe1049041 0x7f52fffffe104904 0xfffffffff34c80c0 0x5fffffffff34c80c

def z282 : W := mkw 0x6080144af0110b10 0x06080144af0110b1 0xffe3fcfff0b31f3f 0xbffe3fcfff0b31f3

def z283 : W := mkw 0xf22fffdfe00020a2 0x7f22fffdfe00020a 0xffeffffff000e1fc 0x1ffeffffff000e1f

def z284 : W := mkw 0xba2fef9da46020a2 0x7ba2fef9da46020a 0x410d4f198c206038 0x8410d4f198c20603

def z285 : W := mkw 0xf02fffdfea8a000c 0x7f02fffdfea8a000 0xfffffffff39f0001 0x1fffffffff39f000

def z286 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0xfef2b0fff35c9fff 0x7fef2b0fff35c9ff

def z287 : W := mkw 0x0500002011149941 0x0050000201114994 0x34d08006035c99c7 0x734d08006035c99c

def z288 : W := mkw 0xb020079da0000000 0x0b020079da000000 0x4000031980000000 0x0400003198000000

def z289 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x8e23fcfff0000000 0x18e23fcfff000000

def z290 : W := mkw 0xa48b06b8ab81d618 0x4a48b06b8ab81d61 0xf3ef4ff98fa3fe3d 0xef3ef4ff98fa3fe3

def z291 : W := mkw 0x6d8ffc6affff9b5d 0x76d8ffc6affff9b5 0xfffffcffffff9fff 0xffffffcffffff9ff

def z292 : W := mkw 0x4504d16751149941 0x24504d1675114994 0xfffef3e7f35c99c7 0x7fffef3e7f35c99c

def z293 : W := mkw 0x000b280000000000 0x5000b28000000000 0x0a033c0000000000 0x00a033c000000000

def z294 : W := mkw 0xa48b06b8bb91df18 0x4a48b06b8bb91df1 0xf3ef03f9ff80ff3d 0xff3ef03f9ff80ff3

def z295 : W := mkw 0x4500106251149941 0x0450010625114994 0x0c10b006735c99c7 0x70c10b006735c99c

def z296 : W := mkw 0x000b00000a800008 0x4000b00000a80000 0x008e00000f000000 0x4008e00000f00000

def z297 : W := mkw 0x000fe80000000000 0x7000fe8000000000 0x010d4c0000000000 0x0010d4c000000000

def z298 : W := mkw 0xfd2ffffffffe994d 0x7fd2ffffffffe994 0xffffffffffff99c7 0xfffffffffffff99c

def z299 : W := mkw 0x040000200b80d408 0x0040000200b80d40 0x0000000003801e01 0x00000000003801e0

def z300 : W := mkw 0x4000104240000000 0x0400010424000000 0x0c00b00670000000 0x10c00b0067000000

def z301 : W := mkw 0x6000144ae0000000 0x06000144ae000000 0xffe3fcfff0000000 0x1ffe3fcfff000000

def z302 : W := mkw 0x000b00000a800008 0x4000b00000a80000 0x0fcf4c000fb30003 0xe0fcf4c000fb3000

def z303 : W := mkw 0x20000408a0000000 0x020000408a000000 0x8a010c1870000000 0x08a010c187000000

def z304 : W := mkw 0xd82ffbd74eea000c 0x7d82ffbd74eea000 0x20beb3e60f4c0000 0x420beb3e60f4c000

def z305 : W := mkw 0xb02b2e98a0000000 0x5b02b2e98a000000 0x00010c1800000000 0x000010c180000000

def z306 : W := mkw 0x0000000000000000 0x0000000000000000 0x04c0800000400002 0x604c080000040000

def z307 : W := mkw 0x450b38625b9e994d 0x5450b38625b9e994 0x8a333ce0739f1801 0x08a333ce0739f180

def z308 : W := mkw 0x0080000010110b10 0x00080000010110b1 0x0f414c0000b31f3f 0xa0f414c0000b31f3

def z309 : W := mkw 0x4100104240040041 0x0410010424004004 0x0010b006004c00c0 0x00010b006004c00c

def z310 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x75cdcf078ce3e1fe 0xf75cdcf078ce3e1f

def z311 : W := mkw 0xd52ffbf741049041 0x7d52ffbf74104904 0x20beb3e6034c80c0 0x420beb3e6034c80c

def z312 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x0c004c01f0b31f3f 0xb0c004c01f0b31f3

def z313 : W := mkw 0xb02fef9daa804408 0x7b02fef9daa80440 0x410d4f198c806608 0x8410d4f198c80660

def z314 : W := mkw 0x800b02900a804408 0x4800b02900a80440 0xd34d03180c807e0d 0xad34d03180c807e0

def z315 : W := mkw 0xf4affffffb91df18 0x7f4affffffb91df1 0xffefffffffb3ff3f 0xfffefffffffb3ff3

def z316 : W := mkw 0xf52ffffff1149941 0x7f52ffffff114994 0xfffffffff35c99c7 0x7fffffffff35c99c

def z317 : W := mkw 0x208fec08b0110b10 0x7208fec08b0110b1 0xdfcffc19f0b31f3f 0xbdfcffc19f0b31f3

def z318 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0c9efc000f7f0002 0x40c9efc000f7f000

def z319 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000031c1801 0x000100000031c180

def z320 : W := mkw 0xfa24d7dfe46020a2 0x2fa24d7dfe46020a 0xf5ecc3fffc60e1fe 0xff5ecc3fffc60e1f

def z321 : W := mkw 0x480ff8424eea000c 0x7480ff8424eea000 0xbffffce67fff0003 0xfbffffce67fff000

def z322 : W := mkw 0x6180144af0150b51 0x06180144af0150b5 0xdf51fc1ff0ff1fff 0xbdf51fc1ff0ff1ff

def z323 : W := mkw 0xa48b06b8bb91df18 0x4a48b06b8bb91df1 0xdf634cf9f3b31f3f 0xbdf634cf9f3b31f3

def z324 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03f80f00e000 0x4f3ef03f80f00e00

def z325 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0b1f7c000fbf0001 0x80b1f7c000fbf000

def z326 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xfbef3ff870000000 0x0fbef3ff87000000

def z327 : W := mkw 0x0a000000046020a2 0x00a000000046020a 0x000000000c60e1fe 0xe000000000c60e1f

def z328 : W := mkw 0x0a0000000eea20ae 0x00a0000000eea20a 0x001000000fffe1ff 0xe001000000fffe1f

def z329 : W := mkw 0x0804e800046a0004 0x30804e800046a000 0x0010b000004c0000 0x00010b000004c000

def z330 : W := mkw 0x2004c50da0000000 0x22004c50da000000 0xffcdcf1ff0000000 0x1ffcdcf1ff000000

def z331 : W := mkw 0x702ffd4fe0000000 0x7702ffd4fe000000 0x0fcffc07f0000000 0x10fcffc07f000000

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x75c0c007806081fe 0xf75c0c007806081f

def z333 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x41014c1980b31f3f 0xa41014c1980b31f3

def z334 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf12d03f80c80fe0c 0x8f12d03f80c80fe0

def z335 : W := mkw 0x0a04c1050eea20ae 0x20a04c1050eea20a 0x75dcc3078fffe1ff 0xf75dcc3078fffe1f

def z336 : W := mkw 0x0804e800046a0004 0x30804e800046a000 0x0f51fc0000ff0003 0xa0f51fc0000ff000

def z337 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x20ae03e00f80fe0d 0xe20ae03e00f80fe0

def z338 : W := mkw 0x080000000eea000c 0x0080000000eea000 0x0ed2b0000fff0003 0xe0ed2b0000fff000

def z339 : W := mkw 0xf42b3efaeb80d408 0x5f42b3efaeb80d40 0x8a233cf873801e01 0x08a233cf873801e0

def z340 : W := mkw 0xf02b3fdfe0000000 0x5f02b3fdfe000000 0xfa233ffff0000000 0x1fa233ffff000000

def z341 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf414c19f0001f3c 0x1df414c19f0001f3

def z342 : W := mkw 0x4f04d1674564b0e3 0x24f04d1674564b0e 0x20beb3e60f4ce0c0 0x420beb3e60f4ce0c

def z343 : W := mkw 0x0500002011149941 0x0050000201114994 0x00000000000099c4 0x000000000000099c

def z344 : W := mkw 0x800b02900a800008 0x4800b02900a80000 0xf3ef03f80f800001 0xef3ef03f80f80000

def z345 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x7fcdcf078cf3e1ff 0xf7fcdcf078cf3e1f

def z346 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x0fdffc078fff01f3 0xf0fdffc078fff01f

def z347 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x5d404c01f033013e 0xb5d404c01f033013

def z348 : W := mkw 0xc50b12f24b84d449 0x4c50b12f24b84d44 0xf3ffb3fe0fccfecd 0xef3ffb3fe0fccfec

def z349 : W := mkw 0xb02fef9da0000000 0x7b02fef9da000000 0xdf4d4f19f0000000 0x1df4d4f19f000000

def z350 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x410c43018c60e1fe 0xe410c43018c60e1f

def z351 : W := mkw 0x70a4fd4ff0110b10 0x370a4fd4ff0110b1 0xdf41fc1ff0b31f3f 0xbdf41fc1ff0b31f3

def z352 : W := mkw 0xe58b16fafb95df59 0x4e58b16fafb95df5 0xffffffffffffffff 0xffffffffffffffff

def z353 : W := mkw 0xc50b12f25b94dd49 0x4c50b12f25b94dd4 0xbefeb3e67f5cf9c7 0x7befeb3e67f5cf9c

def z354 : W := mkw 0x288fec08aeeb021c 0x7288fec08aeeb021 0x4fdffc198fff063b 0xe4fdffc198fff063

def z355 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x34c0c007806081f6 0x734c0c007806081f

def z356 : W := mkw 0x000000000a8a000c 0x0000000000a8a000 0x00100000039f0001 0x000100000039f000

def z357 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xffc1cc1ff0f39fff 0xfffc1cc1ff0f39ff

def z358 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75ccc3078c206038 0x975ccc3078c20603

def z359 : W := mkw 0x25800428b1159b51 0x025800428b1159b5 0xdf514c19f3ff9fff 0xfdf514c19f3ff9ff

def z360 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xff614ffff0000000 0x1ff614ffff000000

def z361 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x554c43018c20613e 0xb554c43018c20613

def z362 : W := mkw 0xd02ffbd740000000 0x7d02ffbd74000000 0xf3efb3fe00000000 0x0f3efb3fe0000000

def z363 : W := mkw 0x0804c00004600000 0x20804c0000460000 0x75ccc3000c60e00e 0xe75ccc3000c60e00

def z364 : W := mkw 0x8c0b02b00fead40c 0x48c0b02b00fead40 0xf3ff03f80ffffe0f 0xef3ff03f80ffffe0

def z365 : W := mkw 0x0804c00004600000 0x20804c0000460000 0x0fdef0000f7c0003 0xe0fdef0000f7c000

def z366 : W := mkw 0x000b000000000000 0x4000b00000000000 0x03cf000000000000 0x003cf00000000000

def z367 : W := mkw 0x4500106251149941 0x0450010625114994 0xaab2b0e6735c98c1 0x4aab2b0e6735c98c

def z368 : W := mkw 0x4d0ff8624fee904d 0x74d0ff8624fee904 0x2ffffce60fff80c3 0xe2ffffce60fff80c

def z369 : W := mkw 0x4500106251149941 0x0450010625114994 0xbaf230e0731c9805 0x6baf230e0731c980

def z370 : W := mkw 0x0c0fe8200fea900c 0x70c0fe8200fea900 0xbffffce00fff9807 0xebffffce00fff980

def z371 : W := mkw 0xba2fef9da46020a2 0x7ba2fef9da46020a 0x75cdcf1f8c60e1fe 0xf75cdcf1f8c60e1f

def z372 : W := mkw 0x840b02b001009000 0x4840b02b00100900 0xf3ef03f803009805 0x6f3ef03f80300980

def z373 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x2caeffe7f0000000 0x12caeffe7f000000

def z374 : W := mkw 0x0004e80000000000 0x30004e8000000000 0x0c00fc0000000000 0x00c00fc000000000

def z375 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a123000031c0001 0x00a123000031c000

def z376 : W := mkw 0x000b00000a800008 0x4000b00000a80000 0x0fdfb0000fdc0003 0xe0fdfb0000fdc000

def z377 : W := mkw 0x20000408b0100900 0x020000408b010090 0xdf414c19f0101907 0x3df414c19f010190

def z378 : W := mkw 0xc50012f25114dd41 0x0c50012f25114dd4 0xf02003fe7000ffcc 0x1f02003fe7000ffc

def z379 : W := mkw 0xb02fef9da0000000 0x7b02fef9da000000 0xf3ef4ff980000000 0x0f3ef4ff98000000

def z380 : W := mkw 0x0000000000000000 0x0000000000000000 0x1440000000000106 0x3144000000000010

def z381 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xdf637cf9f0000000 0x1df637cf9f000000

def z382 : W := mkw 0x5024f94740000000 0x35024f9474000000 0x0000b00600000000 0x00000b0060000000

def z383 : W := mkw 0x4000104240000000 0x0400010424000000 0x20a2b0e600000000 0x020a2b0e60000000

def z384 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdb410c1870931e0d 0xadb410c1870931e0

def z385 : W := mkw 0xc50b12f24b84d449 0x4c50b12f24b84d44 0x20beb3e60f4ce0c0 0x420beb3e60f4ce0c

def z386 : W := mkw 0x840b02b00100d400 0x4840b02b00100d40 0xf3ef03f80000fe0c 0x0f3ef03f80000fe0

def z387 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xf0aeb3fff0000000 0x1f0aeb3fff000000

def z388 : W := mkw 0x0004c10500000000 0x20004c1050000000 0x208c830600000000 0x0208c83060000000

def z389 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0bdf3c000f9f0001 0xe0bdf3c000f9f000

def z390 : W := mkw 0x0804c00004600000 0x20804c0000460000 0x55ccc0018c60013e 0xf55ccc0018c60013

def z391 : W := mkw 0x0000000010100900 0x0000000001010090 0x9ed2b000735c1907 0x79ed2b000735c190

def z392 : W := mkw 0x4100104250140941 0x0410010425014094 0x9e50b006705c19c7 0x39e50b006705c19c

def z393 : W := mkw 0x6f84d56ff575bbf3 0x26f84d56ff575bbf 0xffffffffffffffff 0xffffffffffffffff

def z394 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x8a010c1870b31f3f 0xa8a010c1870b31f3

def z395 : W := mkw 0x8c0feab00fead40c 0x78c0feab00fead40 0xf3ffb3f80fccfe0d 0xef3ffb3f80fccfe0

def z396 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x5fdffc018fff013f 0xf5fdffc018fff013

def z397 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc206038 0x9ffeffffffc20603

def z398 : W := mkw 0x20000408a0000000 0x020000408a000000 0x41014c1980000000 0x041014c198000000

def z399 : W := mkw 0xac8feeb8bffbdf1c 0x7ac8feeb8bffbdf1 0xfffffff9ffffff3f 0xffffffff9ffffff3

def z400 : W := mkw 0x2884c408b4710b10 0x22884c408b4710b1 0xdfcdcc19fcf31f3f 0xfdfcdcc19fcf31f3

def z401 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x710c43078c20e1fc 0x9710c43078c20e1f

def z402 : W := mkw 0x0800000004600000 0x0080000000460000 0x000000000c600002 0xe000000000c60000

def z403 : W := mkw 0x8000029000004400 0x0800002900000440 0x4000031800006608 0x0400003180000660

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0x00100000035c0003 0x600100000035c000

def z405 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0b30003 0xbffeffffff0b3000

def z406 : W := mkw 0xf52b3efaf1149941 0x5f52b3efaf114994 0xbef3bcfe735c99c7 0x7bef3bcfe735c99c

def z407 : W := mkw 0xf52ffffffb94dd49 0x7f52ffffffb94dd4 0xffffffffffdcffcf 0xfffffffffffdcffc

def z408 : W := mkw 0x040000200b80d408 0x0040000200b80d40 0xd34100180f80fe0d 0xed34100180f80fe0

def z409 : W := mkw 0xf02fffdfea804408 0x7f02fffdfea80440 0xffeffffffc806608 0x9ffeffffffc80660

def z410 : W := mkw 0x4d04f862557e9945 0x34d04f862557e994 0xbef2fce6737f99c7 0x7bef2fce6737f99c

def z411 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0ed3bc0003df0003 0x60ed3bc0003df000

def z412 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0801e0d 0xbffeffffff0801e0

def z413 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fcffc000ca30000 0x80fcffc000ca3000

def z414 : W := mkw 0x0a0fe905046020a2 0x70a0fe905046020a 0x7fcfff078c60e1fe 0xf7fcfff078c60e1f

def z415 : W := mkw 0x040000200b80d408 0x0040000200b80d40 0x71cc03000f80fe0d 0xe71cc03000f80fe0

def z416 : W := mkw 0x8000029000000000 0x0800002900000000 0xf02003f800000000 0x0f02003f80000000

def z417 : W := mkw 0x0080000010110b10 0x00080000010110b1 0x5540400180b31f3f 0xb5540400180b31f3

def z418 : W := mkw 0xf42fffffeb80d408 0x7f42fffffeb80d40 0xffefffffff00e000 0x5ffefffffff00e00

def z419 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x00000001f0000130 0x100000001f000013

def z420 : W := mkw 0x4f04d1674564b0e3 0x24f04d1674564b0e 0x75fef3e78f6ce1fe 0xf75fef3e78f6ce1f

def z421 : W := mkw 0x2a84c50db4712bb2 0x22a84c50db4712bb 0xdf41cc1ff0f31fff 0xbdf41cc1ff0f31ff

def z422 : W := mkw 0x0a04e905046a20a6 0x30a04e905046a20a 0x0c10fc07807f01f2 0x10c10fc07807f01f

def z423 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xb2ee03e00f00f805 0x6b2ee03e00f00f80

def z424 : W := mkw 0x0004c10500000000 0x20004c1050000000 0x410c430180000000 0x0410c43018000000

def z425 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x410d4f018ca36038 0x8410d4f018ca3603

def z426 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x7fdef3078f7ce1ff 0xf7fdef3078f7ce1f

def z427 : W := mkw 0x0000000000000000 0x0000000000000000 0x0ec2b00000000000 0x00ec2b0000000000

def z428 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x71ee03e00f00e00c 0xe71ee03e00f00e00

def z429 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0xbef2fce7f37f99f7 0x7bef2fce7f37f99f

def z430 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x9e410c1870931f07 0x39e410c1870931f0

def z431 : W := mkw 0x0804e800046a0004 0x30804e800046a000 0x0ddcfc000c7f0002 0xe0ddcfc000c7f000

def z432 : W := mkw 0xd02ffbd740000000 0x7d02ffbd74000000 0x75eef3e780000000 0x175eef3e78000000

def z433 : W := mkw 0x0400002001009000 0x0040000200100900 0x822200e003001801 0x0822200e00300180

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000004081c6 0x600000000004081c

def z435 : W := mkw 0x800b02900a804408 0x4800b02900a80440 0xf3ef03f80c806608 0x8f3ef03f80c80660

def z436 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0e13fc0003ff0003 0x00e13fc0003ff000

def z437 : W := mkw 0x02000105000020a2 0x002000105000020a 0x754043078020e1fe 0xb754043078020e1f

def z438 : W := mkw 0x8c0feab00fead40c 0x78c0feab00fead40 0x20beb3e00f4ce000 0x420beb3e00f4ce00

def z439 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xffcd4f19fcb3ff3f 0xfffcd4f19fcb3ff3

def z440 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x71cc83060c40e0cc 0xe71cc83060c40e0c

def z441 : W := mkw 0x0804c10504600000 0x20804c1050460000 0x75ccc3078c600002 0xf75ccc3078c60000

def z442 : W := mkw 0x0000000000000000 0x0000000000000000 0x34c0800600000000 0x134c080060000000

def z443 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xb2e300f803809e05 0x6b2e300f803809e0

def z444 : W := mkw 0x0000000000000000 0x0000000000000000 0x9240000000001805 0x2924000000000180

def z445 : W := mkw 0x00002800000a0004 0x100002800000a000 0x08103c00001f0000 0x008103c00001f000

def z446 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfffffffff35c0003 0x7fffffffff35c000

def z447 : W := mkw 0x2a04c50da46020a2 0x22a04c50da46020a 0xffcdcf1ffc60e1fe 0xfffcdcf1ffc60e1f

def z448 : W := mkw 0x20800408a0010210 0x020800408a001021 0x00010c1800830600 0x000010c180083060

def z449 : W := mkw 0x8c0feab00fead40c 0x78c0feab00fead40 0x2fffffe00fffe003 0xe2fffffe00fffe00

def z450 : W := mkw 0x040b00200b80d408 0x4040b00200b80d40 0x03cf00000f80fe0d 0xe03cf00000f80fe0

def z451 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0xf7cdc31f8ce0ffff 0xff7cdc31f8ce0fff

def z452 : W := mkw 0x4100104250140941 0x0410010425014094 0x00000006700001c0 0x100000006700001c

def z453 : W := mkw 0x040000200b80d408 0x0040000200b80d40 0x000000000f00e000 0x4000000000f00e00

def z454 : W := mkw 0x2280050db0112bb2 0x02280050db0112bb 0xff414f1ff0b3ffff 0xbff414f1ff0b3fff

def z455 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x7400c3078060e1fe 0x17400c3078060e1f

def z456 : W := mkw 0xb82fef9daeea000c 0x7b82fef9daeea000 0x410d4f198ca30000 0x8410d4f198ca3000

def z457 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x708c83078c40e1fc 0x5708c83078c40e1f

def z458 : W := mkw 0x880fea900eea440c 0x7880fea900eea440 0x410d4f180ca36608 0x8410d4f180ca3660

def z459 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0xbef3bcfe73df9fc7 0x7bef3bcfe73df9fc

def z460 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf22303f80380fe0d 0x0f22303f80380fe0

def z461 : W := mkw 0x860b03b50b80f4aa 0x4860b03b50b80f4a 0xf3ef03ff8f80fffd 0xff3ef03ff8f80fff

def z462 : W := mkw 0x450b10625b949949 0x4450b10625b94994 0xbfffb0e67fdc99c7 0xfbfffb0e67fdc99c

def z463 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x002200e003000000 0x0002200e00300000

def z464 : W := mkw 0xc50b12f251149941 0x4c50b12f25114994 0xffffb3fe735c99c7 0x7ffffb3fe735c99c

def z465 : W := mkw 0x0400002001009000 0x0040000200100900 0xb02000e000009804 0x0b02000e00000980

def z466 : W := mkw 0xc40b12f24b80d408 0x4c40b12f24b80d40 0xffefb3fe7f80fe0d 0xfffefb3fe7f80fe0

def z467 : W := mkw 0x20800408a0010210 0x020800408a001021 0x4f414c1980b3063b 0xa4f414c1980b3063

def z468 : W := mkw 0xf82fffdfe46a0004 0x7f82fffdfe46a000 0xfffffffff07f0002 0x1fffffffff07f000

def z469 : W := mkw 0xf52ffffff1149941 0x7f52ffffff114994 0xffeffffff00099c4 0x1ffeffffff00099c

def z470 : W := mkw 0x2a84c50db4712bb2 0x22a84c50db4712bb 0x7dcccf07fc73e1fe 0xf7dcccf07fc73e1f

def z471 : W := mkw 0x800b029000000000 0x4800b02900000000 0xf3ef03f800801e0d 0xaf3ef03f800801e0

def z472 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x05def0000f6c0002 0xe05def0000f6c000

def z473 : W := mkw 0xf82ffedaeeea000c 0x7f82ffedaeeea000 0x8ffffcf87fff0003 0xe8ffffcf87fff000

def z474 : W := mkw 0xf42b17ffeb80d408 0x4f42b17ffeb80d40 0xf3ef03ffff80fe0d 0xff3ef03ffff80fe0

def z475 : W := mkw 0x0400002011109900 0x0040000201110990 0xbee200e073109907 0x7bee200e07310990

def z476 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0d1dfc000cff0002 0x80d1dfc000cff000

def z477 : W := mkw 0x0000000000000000 0x0000000000000000 0x5540400180000000 0x1554040018000000

def z478 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x00123000030c0000 0x000123000030c000

def z479 : W := mkw 0xa40b06b8ab80d408 0x4a40b06b8ab80d40 0xffef4ff9ff80fe0d 0xfffef4ff9ff80fe0

def z480 : W := mkw 0x4500106251149941 0x0450010625114994 0xb0b2b0e6734c99c4 0x5b0b2b0e6734c99c

def z481 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff04081c6 0x7ffeffffff04081c

def z482 : W := mkw 0x0000000000000000 0x0000000000000000 0x0540400000200002 0xa054040000020000

def z483 : W := mkw 0xd82ffbd74eea000c 0x7d82ffbd74eea000 0x2fffffe60fff0003 0xe2fffffe60fff000

def z484 : W := mkw 0x0804c00004600000 0x20804c0000460000 0x35ccc0060c6081c6 0xf35ccc0060c6081c

def z485 : W := mkw 0x0a0fc1050ee020aa 0x60a0fc1050ee020a 0x77cfc3078fe0e1ff 0xf77cfc3078fe0e1f

def z486 : W := mkw 0x4100104250140941 0x0410010425014094 0x3cd0b006705c81c6 0x73cd0b006705c81c

def z487 : W := mkw 0x0080000010110b10 0x00080000010110b1 0x0000000000001f3c 0x00000000000001f3

def z488 : W := mkw 0x288fec08befb0b1c 0x7288fec08befb0b1 0x0fdffc01ffff0133 0xf0fdffc01ffff013

def z489 : W := mkw 0x24800428b1119b10 0x024800428b1119b1 0xffe34cf9f3b39f3f 0xfffe34cf9f3b39f3

def z490 : W := mkw 0x7524fd6ff1149941 0x37524fd6ff114994 0xbef2fce7f35c99c7 0x7bef2fce7f35c99c

def z491 : W := mkw 0x0500002011149941 0x0050000201114994 0x0ed2b000035c99c7 0x60ed2b000035c99c

def z492 : W := mkw 0x7020154fe0000000 0x07020154fe000000 0x00000007f0000000 0x100000007f000000

def z493 : W := mkw 0xd42ffbf74b80d408 0x7d42ffbf74b80d40 0x20aeb3e60f00e000 0x420aeb3e60f00e00

def z494 : W := mkw 0x840fc3b50b80d408 0x6840fc3b50b80d40 0xf7efc3ff8f80fe0d 0xff7efc3ff8f80fe0

def z495 : W := mkw 0x000fe80000000000 0x7000fe8000000000 0x0fdffc00035c0003 0x60fdffc00035c000

def z496 : W := mkw 0x2884ec08b47b0b14 0x32884ec08b47b0b1 0x0c10fc01f07f0132 0x10c10fc01f07f013

def z497 : W := mkw 0xb02fef9da0000000 0x7b02fef9da000000 0x75cdcf1f80000000 0x175cdcf1f8000000

def z498 : W := mkw 0x782ffd4feeea000c 0x7782ffd4feeea000 0x0fdffc07ffff0003 0xf0fdffc07ffff000

def z499 : W := mkw 0x200fec08a0000000 0x7200fec08a000000 0xdfcffc19f0000000 0x1dfcffc19f000000

def z500 : W := mkw 0x0000010500000000 0x0000001050000000 0x7000030780000000 0x1700003078000000

def z501 : W := mkw 0x490ff8425efe094d 0x7490ff8425efe094 0x0fdffc067fff01c3 0xf0fdffc067fff01c

def z502 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x08000c0070130000 0x008000c007013000

def z503 : W := mkw 0xc50b12f25b94dd49 0x4c50b12f25b94dd4 0xfbff33f87f9cfe0d 0xefbff33f87f9cfe0

def z504 : W := mkw 0x0100000010140941 0x0010000001014094 0x00100000005c01c2 0x000100000005c01c

def z505 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x000c00000c000000 0x0000c00000c00000

def z506 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x05ccc0078c6001f2 0xf05ccc0078c6001f

def z507 : W := mkw 0x0400002001009000 0x0040000200100900 0xf3ee03e00f00f80d 0xef3ee03e00f00f80

def z508 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xcb2f7ff9f0000000 0x0cb2f7ff9f000000

def z509 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x34cc83060c40e1c6 0x734cc83060c40e1c

def z510 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0f4d4c000cb30003 0xa0f4d4c000cb3000

def z511 : W := mkw 0x850b02b01b94dd49 0x4850b02b01b94dd4 0xf3ff03f80fdcffcf 0xef3ff03f80fdcffc

def z512 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x83ef00f80f801e01 0xe83ef00f80f801e0

def z513 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffffc00e00c 0xfffeffffffc00e00

def z514 : W := mkw 0x0000000010100900 0x0000000001010090 0xdf41001870901f0f 0xbdf41001870901f0

def z515 : W := mkw 0xf82fffdfe4600000 0x7f82fffdfe460000 0xffeffffffc600002 0xfffeffffffc60000

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0xd741401980a01f3f 0xbd741401980a01f3

def z517 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x00008006004000c0 0x000008006004000c

def z518 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x450cc3078c6061fa 0x9450cc3078c6061f

def z519 : W := mkw 0x8e0febb50feaf4ae 0x78e0febb50feaf4a 0xffffffff8fffffff 0xfffffffff8ffffff

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x700003000000e00c 0x0700003000000e00

def z521 : W := mkw 0xc50b12f25b94dd49 0x4c50b12f25b94dd4 0x8a3330f8739c1e01 0x08a3330f8739c1e0

def z522 : W := mkw 0x2a84c50da46122b2 0x22a84c50da46122b 0x75cdcf1f8ce3e7fe 0xf75cdcf1f8ce3e7f

def z523 : W := mkw 0x400ff84240000000 0x7400ff8424000000 0xbfeffce670000000 0x1bfeffce67000000

def z524 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xaaafbffe70000000 0x0aaafbffe7000000

def z525 : W := mkw 0xf52ffffff1149941 0x7f52ffffff114994 0xfffffffff31c1801 0x1fffffffff31c180

def z526 : W := mkw 0x080000000eea000c 0x0080000000eea000 0x0f514c000fff0003 0xe0f514c000fff000

def z527 : W := mkw 0x0080000000010210 0x0008000000001021 0x0000000000a30638 0x80000000000a3063

def z528 : W := mkw 0xd42ffbf74b80d408 0x7d42ffbf74b80d40 0xf3efb3fe0f80fe0d 0xef3efb3fe0f80fe0

def z529 : W := mkw 0x4100104250140941 0x0410010425014094 0x0ed2b006735c01c3 0x70ed2b006735c01c

def z530 : W := mkw 0x3024ed0da0000000 0x33024ed0da000000 0x00004c0180000000 0x000004c018000000

def z531 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xcb014c19f0b31e39 0x8cb014c19f0b31e3

def z532 : W := mkw 0x0500002011149941 0x0050000201114994 0x9e500000735c99c7 0x79e500000735c99c

def z533 : W := mkw 0x0000000000000000 0x0000000000000000 0x514000000000000c 0xa514000000000000

def z534 : W := mkw 0x848b02b01b91df18 0x4848b02b01b91df1 0xf3ef03f80fb3ff3f 0xef3ef03f80fb3ff3

def z535 : W := mkw 0x4f0ff9675ffeb9ef 0x74f0ff9675ffeb9e 0xffffffe7fffff9ff 0xfffffffe7fffff9f

def z536 : W := mkw 0xa08b0698b0110b10 0x4a08b0698b0110b1 0xffef4ff9f0b31f3f 0xbffef4ff9f0b31f3

def z537 : W := mkw 0x4f04d1675574b9e3 0x24f04d1675574b9e 0xbef2f0e7f37c99f7 0x7bef2f0e7f37c99f

def z538 : W := mkw 0xf42017ffe100d400 0x0f42017ffe100d40 0xf02003fff000fe0c 0x1f02003fff000fe0

def z539 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf0ae03f80f00fe0c 0x4f0ae03f80f00fe0

def z540 : W := mkw 0x0d0000201ffe994d 0x00d0000201ffe994 0x001000000fff99c7 0xe001000000fff99c

def z541 : W := mkw 0xc50b12f25b94dd49 0x4c50b12f25b94dd4 0xf3ef03fe7f80ffcd 0xff3ef03fe7f80ffc

def z542 : W := mkw 0xb42fefbdab80d408 0x7b42fefbdab80d40 0xf3ef4ff98f80fe0d 0xef3ef4ff98f80fe0

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0x5f414c0180b3013f 0xb5f414c0180b3013

def z544 : W := mkw 0x2a8fed0dbefb2bbe 0x72a8fed0dbefb2bb 0xffdfff1fffffffff 0xfffdfff1ffffffff

def z545 : W := mkw 0x088000001efb0b1c 0x0088000001efb0b1 0x001000000fff1f3f 0xe001000000fff1f3

def z546 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x019ffc000fef0000 0xc019ffc000fef000

def z547 : W := mkw 0x080fe800046a0004 0x7080fe800046a000 0x0fdffc00007f0002 0x00fdffc00007f000

def z548 : W := mkw 0xd02ffbd740000000 0x7d02ffbd74000000 0x2fefffe600000000 0x02fefffe60000000

def z549 : W := mkw 0x0804c00004600000 0x20804c0000460000 0x0fcdcc000cf30003 0xe0fcdcc000cf3000

def z550 : W := mkw 0x4f0010625574b9e3 0x04f0010625574b9e 0xbef2b0e67f7cf9ff 0xfbef2b0e67f7cf9f

def z551 : W := mkw 0x840002b00100d400 0x0840002b00100d40 0xf36103f80080fe0d 0xaf36103f80080fe0

def z552 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0xff614cfff0b39fff 0xbff614cfff0b39ff

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0xdf414c1800b31e0f 0xadf414c1800b31e0

def z554 : W := mkw 0x20000408a0000000 0x020000408a000000 0xdf414c19f0801e0d 0xbdf414c19f0801e0

def z555 : W := mkw 0xfc2fffffefead40c 0x7fc2fffffefead40 0xfffffffffffffe0f 0xffffffffffffffe0

def z556 : W := mkw 0x0000000010100900 0x0000000001010090 0x0c00000070100102 0x10c0000007010010

def z557 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400400180200132 0x1040040018020013

def z558 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000020013e 0xa000000000020013

def z559 : W := mkw 0x4f04d1675574b9e3 0x24f04d1675574b9e 0xbefeb3e67f5cf9c7 0x7befeb3e67f5cf9c

def z560 : W := mkw 0x2280050db0112bb2 0x02280050db0112bb 0xf000031ff000fffc 0x1f000031ff000fff

def z561 : W := mkw 0x8a0fc3950ee064aa 0x68a0fc3950ee064a 0x410d43198ca06638 0x8410d43198ca0663

def z562 : W := mkw 0x4d0ff8625ffe994d 0x74d0ff8625ffe994 0xbefeb0e67f5c99c7 0x7befeb0e67f5c99c

def z563 : W := mkw 0x08000000046a0004 0x008000000046a000 0x00100000007f0002 0x000100000007f000

def z564 : W := mkw 0x0000000000000000 0x0000000000000000 0x01014c0000a30000 0x801014c0000a3000

def z565 : W := mkw 0x0a000105046020a2 0x00a000105046020a 0x700003078c60e1fe 0xf700003078c60e1f

def z566 : W := mkw 0x4500106241049041 0x0450010624104904 0x34f2b0e6034c81c6 0x734f2b0e6034c81c

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x75cc43018c20e13e 0xf75cc43018c20e13

def z568 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff020013e 0xbffeffffff020013

def z569 : W := mkw 0x02000000000020a2 0x002000000000020a 0x000000000000e1fc 0x0000000000000e1f

def z570 : W := mkw 0x470011675114b9e3 0x0470011675114b9e 0xfef2b3e7f35cf9ff 0x7fef2b3e7f35cf9f

def z571 : W := mkw 0x0e0000200fe0f4aa 0x00e0000200fe0f4a 0x000000000fe0ffff 0xe000000000fe0fff

def z572 : W := mkw 0x7824fd4fe46a0004 0x37824fd4fe46a000 0x0c10fc07f07f0002 0x10c10fc07f07f000

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x20808006004080c0 0x420808006004080c

def z574 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x5540c007806001fe 0xb5540c007806001f

def z575 : W := mkw 0xf0a017dff0110b10 0x0f0a017dff0110b1 0xf02003fff0001f3c 0x1f02003fff0001f3

def z576 : W := mkw 0x2a800408b4712bb2 0x02a800408b4712bb 0xdf414c19fcf3ffff 0xfdf414c19fcf3fff

def z577 : W := mkw 0x8e0fc3b50fe0f4aa 0x68e0fc3b50fe0f4a 0x75eec3e78f60e1fe 0xf75eec3e78f60e1f

def z578 : W := mkw 0x8c0feab00fead40c 0x78c0feab00fead40 0xf3ef4ff80fa3fe0d 0xef3ef4ff80fa3fe0

def z579 : W := mkw 0x080fc0000ee00008 0x6080fc0000ee0000 0x07cfc0000fe00003 0xe07cfc0000fe0000

def z580 : W := mkw 0xda2ffbd7446020a2 0x7da2ffbd7446020a 0x20aeb3e60c40e0c0 0x420aeb3e60c40e0c

def z581 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc000f4c0000 0x40fdffc000f4c000

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c004c0000330002 0x00c004c000033000

def z583 : W := mkw 0xb0afef9db0110b10 0x7b0afef9db0110b1 0xdf4d4f19f0b31f3f 0xbdf4d4f19f0b31f3

def z584 : W := mkw 0xf0afffdff0110b10 0x7f0afffdff0110b1 0xffeffffff0931e01 0x1ffeffffff0931e0

def z585 : W := mkw 0x0500002011149941 0x0050000201114994 0xb2f200e0035c99c7 0x6b2f200e0035c99c

def z586 : W := mkw 0x040000200b80d408 0x0040000200b80d40 0xb2e200e00f80fe0d 0xeb2e200e00f80fe0

def z587 : W := mkw 0x0f0000201574b9e3 0x00f0000201574b9e 0x001000000f7cf9ff 0xe001000000f7cf9f

def z588 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x03cf4c000fa30001 0xe03cf4c000fa3000

def z589 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf414c19f0931e01 0x1df414c19f0931e0

def z590 : W := mkw 0x800b02900a804408 0x4800b02900a80440 0x0001001800800600 0x0000100180080060

def z591 : W := mkw 0x080000000eea000c 0x0080000000eea000 0x001000000f4c0000 0x4001000000f4c000

def z592 : W := mkw 0x28800408befb0b1c 0x028800408befb0b1 0xdf514c19ffff1f3f 0xfdf514c19ffff1f3

def z593 : W := mkw 0x0000000000000000 0x0000000000000000 0x410c03000c006008 0x8410c03000c00600

def z594 : W := mkw 0x4500106251149941 0x0450010625114994 0xbee2b0e6700099c4 0x1bee2b0e6700099c

def z595 : W := mkw 0x0a04c105147029a2 0x20a04c105147029a 0xffccc307fc70f9ff 0xfffccc307fc70f9f

def z596 : W := mkw 0x0000000000000000 0x0000000000000000 0x0f414c0000000000 0x00f414c000000000

def z597 : W := mkw 0x0000000010100900 0x0000000001010090 0x8a00000070101801 0x08a0000007010180

def z598 : W := mkw 0xff2ffffff574b9e3 0x7ff2ffffff574b9e 0xffffffffff7cf9ff 0xfffffffffff7cf9f

def z599 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000801e0d 0xa0000000000801e0

def z600 : W := mkw 0x4400106241009000 0x0440010624100900 0xbee2b0e673009805 0x7bee2b0e67300980

def z601 : W := mkw 0x4500106251149941 0x0450010625114994 0xbc30b0e6705c99c6 0x1bc30b0e6705c99c

def z602 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x208c83060c60e1fe 0xe208c83060c60e1f

def z603 : W := mkw 0x450ff86251149941 0x7450ff8625114994 0xbffffce6735c99c7 0x7bffffce6735c99c

def z604 : W := mkw 0xa48b06b8bb91df18 0x4a48b06b8bb91df1 0xfbef0ff87f93fe0d 0xefbef0ff87f93fe0

def z605 : W := mkw 0x800b029000000000 0x4800b02900000000 0x410d031800000000 0x0410d03180000000

def z606 : W := mkw 0x000000000a804408 0x0000000000a80440 0x000000000c806608 0x8000000000c80660

def z607 : W := mkw 0x8a0fc3950ee064aa 0x68a0fc3950ee064a 0x75cdc31f8ce0e7fe 0xf75cdc31f8ce0e7f

def z608 : W := mkw 0x2a84c50db4712bb2 0x22a84c50db4712bb 0x0c00cc07f07301f2 0x10c00cc07f07301f

def z609 : W := mkw 0x840b02b01b90dd08 0x4840b02b01b90dd0 0xffef03f87f90ff0f 0xfffef03f87f90ff0

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x500000018000013c 0x1500000018000013

def z611 : W := mkw 0xcd0ffaf25ffedd4d 0x7cd0ffaf25ffedd4 0xfffffffe7fffffcf 0xffffffffe7fffffc

def z612 : W := mkw 0x0a80000014712bb2 0x00a80000014712bb 0x000000000cf3ffff 0xe000000000cf3fff

def z613 : W := mkw 0xb0afef9da0010210 0x7b0afef9da001021 0x410d4f1980a30638 0x8410d4f1980a3063

def z614 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf414c19f0330132 0x1df414c19f033013

def z615 : W := mkw 0x0804c00004600000 0x20804c0000460000 0x008c80000c400000 0x4008c80000c40000

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0xd000001800001e0c 0x0d000001800001e0

def z617 : W := mkw 0x902feb9500000000 0x7902feb950000000 0x000c030000000000 0x0000c03000000000

def z618 : W := mkw 0x840002b00100d400 0x0840002b00100d40 0x802000f800001e00 0x0802000f800001e0

def z619 : W := mkw 0x20800408a0010210 0x020800408a001021 0x4000001980000638 0x0400000198000063

def z620 : W := mkw 0x0400002001009000 0x0040000200100900 0xbef2b0e0035c9807 0x6bef2b0e0035c980

def z621 : W := mkw 0x0080000010110b10 0x00080000010110b1 0xd341001800b31f3f 0xad341001800b31f3

def z622 : W := mkw 0xa48b06b8bb91df18 0x4a48b06b8bb91df1 0x8a230cf873931e01 0x08a230cf873931e0

def z623 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x71cc43018c20e03c 0xe71cc43018c20e03

def z624 : W := mkw 0x280fec08aeea000c 0x7280fec08aeea000 0xdfdffc19ffff0003 0xfdfdffc19ffff000

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x30000006000081c4 0x130000006000081c

def z626 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x009eb0000fff0003 0xe009eb0000fff000

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x4100400180200038 0x8410040018020003

def z628 : W := mkw 0x000fe80000000000 0x7000fe8000000000 0x0fcffc0000b30003 0xa0fcffc0000b3000

def z629 : W := mkw 0x20800408a0010210 0x020800408a001021 0xd3414c1980a31e3d 0xad3414c1980a31e3

def z630 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x05cdcc000ce30002 0xe05cdcc000ce3000

def z631 : W := mkw 0x800b02900a804408 0x4800b02900a80440 0x71cd03180c80e60c 0xe71cd03180c80e60

def z632 : W := mkw 0xa08b0698ba914f18 0x4a08b0698ba914f1 0xdf4d4f19fcb37f3f 0xbdf4d4f19fcb37f3

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c10b000005c0002 0x00c10b000005c000

def z634 : W := mkw 0x4904f842547e0945 0x34904f842547e094 0x0c10fc06707f01c2 0x10c10fc06707f01c

def z635 : W := mkw 0x02000105000020a2 0x002000105000020a 0x4000030180006038 0x0400003018000603

def z636 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000c00e00c 0xe000000000c00e00

def z637 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x03dfb0000fcc0001 0xe03dfb0000fcc000

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000b30003 0xa0000000000b3000

def z639 : W := mkw 0x0004c10500000000 0x20004c1050000000 0x75ccc3078020013e 0xb75ccc3078020013

def z640 : W := mkw 0xc50012f25114dd41 0x0c50012f25114dd4 0xfef2b3fe735cffcf 0x7fef2b3fe735cffc

def z641 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xd0000019f0b31f3f 0xbd0000019f0b31f3

def z642 : W := mkw 0xc50b12f25b94dd49 0x4c50b12f25b94dd4 0xbef3b0fe73dc9fc7 0x7bef3b0fe73dc9fc

def z643 : W := mkw 0x800b02900a804408 0x4800b02900a80440 0x000c03000c006000 0x0000c03000c00600

def z644 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x25ccc3060c60e0c2 0xe25ccc3060c60e0c

def z645 : W := mkw 0x4100104250140941 0x0410010425014094 0x08103000701c0000 0x008103000701c000

def z646 : W := mkw 0x4500106251149941 0x0450010625114994 0x20b2b0e6035c99c7 0x620b2b0e6035c99c

def z647 : W := mkw 0x6180144af0150b51 0x06180144af0150b5 0x0c10fc07f07f01f2 0x10c10fc07f07f01f

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x0341000000800001 0xa034100000080000

def z649 : W := mkw 0x8e04c3b50560f4a2 0x28e04c3b50560f4a 0xf5ecc3ff8c60fffe 0xff5ecc3ff8c60fff

def z650 : W := mkw 0x080fe8001efa090c 0x7080fe8001efa090 0x9fdffc007fff1907 0xf9fdffc007fff190

def z651 : W := mkw 0x0e04c1250560b0a2 0x20e04c1250560b0a 0xf7eec3e78f60f9ff 0xff7eec3e78f60f9f

def z652 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x75def3078f6ce1fe 0xf75def3078f6ce1f

def z653 : W := mkw 0x2a84c50db4712bb2 0x22a84c50db4712bb 0xf5ccc31ffc60fffe 0xff5ccc31ffc60fff

def z654 : W := mkw 0x0080000010110b10 0x00080000010110b1 0x0000000000330132 0x0000000000033013

def z655 : W := mkw 0x088fe8001efb0b1c 0x7088fe8001efb0b1 0x0fdffc000fff1f3f 0xe0fdffc000fff1f3

def z656 : W := mkw 0x20000408a0000000 0x020000408a000000 0x0c004c01f0000000 0x10c004c01f000000

def z657 : W := mkw 0xa08b0698aa814618 0x4a08b0698aa81461 0x410d4f198ca36638 0x8410d4f198ca3663

def z658 : W := mkw 0x0a000000046020a2 0x00a000000046020a 0x000000000c206038 0x8000000000c20603

def z659 : W := mkw 0x70a4fd4ff0110b10 0x370a4fd4ff0110b1 0x0c00fc07f0330132 0x10c00fc07f033013

def z660 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0edeb0000f5c0003 0x60edeb0000f5c000

def z661 : W := mkw 0x000fe8000a800008 0x7000fe8000a80000 0x0fcffc000f800001 0xe0fcffc000f80000

def z662 : W := mkw 0x0000000000000000 0x0000000000000000 0xd341001800000000 0x0d34100180000000

def z663 : W := mkw 0x4500106241049041 0x0450010624104904 0xb2f2b0e6034c98c5 0x6b2f2b0e6034c98c

def z664 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xde400019f0101f3f 0x3de400019f0101f3

def z665 : W := mkw 0x2a84c50db4712bb2 0x22a84c50db4712bb 0xdf4d4f19fcb37f3f 0xbdf4d4f19fcb37f3

def z666 : W := mkw 0x0000000000000000 0x0000000000000000 0x71cc030000000000 0x071cc03000000000

def z667 : W := mkw 0xf02fffdff0100900 0x7f02fffdff010090 0xffeffffff0101907 0x3ffeffffff010190

def z668 : W := mkw 0x0080000010110b10 0x00080000010110b1 0x9e40000070b31f3f 0xb9e40000070b31f3

def z669 : W := mkw 0x7024fd4fe0000000 0x37024fd4fe000000 0xdf41fc1ff0000000 0x1df41fc1ff000000

def z670 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75ccc3078c40e0c0 0x575ccc3078c40e0c

def z671 : W := mkw 0x4500106251149941 0x0450010625114994 0x802000e070001800 0x0802000e07000180

def z672 : W := mkw 0xf42fffffe100d400 0x7f42fffffe100d40 0xffeffffff000fe0c 0x1ffeffffff000fe0

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e40000000100003 0x20e4000000010000

def z674 : W := mkw 0x000000000a800008 0x0000000000a80000 0x000000000f800001 0xe000000000f80000

def z675 : W := mkw 0x8c0feab00fead40c 0x78c0feab00fead40 0x8ffffcf80fff1e03 0xe8ffffcf80fff1e0

def z676 : W := mkw 0xf52b3efaf1149941 0x5f52b3efaf114994 0x8a333cf8731c1801 0x08a333cf8731c180

def z677 : W := mkw 0x4f04d1675574b9e3 0x24f04d1675574b9e 0xf5ecc3e7fc60f9fe 0xff5ecc3e7fc60f9f

def z678 : W := mkw 0x0004c00000000000 0x20004c0000000000 0x05ccc00000000000 0x005ccc0000000000

def z679 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xd36300f803801e0d 0xad36300f803801e0

def z680 : W := mkw 0x2a84c50da46122b2 0x22a84c50da46122b 0x410d4f198ca36638 0x8410d4f198ca3663

def z681 : W := mkw 0x0004c10500000000 0x20004c1050000000 0x75ccc307804081c6 0x775ccc307804081c

def z682 : W := mkw 0x4500106241049041 0x0450010624104904 0x202000e6000080c0 0x0202000e6000080c

def z683 : W := mkw 0x0400002001009000 0x0040000200100900 0xb6e280e6034099c7 0x7b6e280e6034099c

def z684 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03f803801e01 0x0f3ef03f803801e0

def z685 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x4d014c19f0b3073a 0x94d014c19f0b3073

def z686 : W := mkw 0x000fe80000000000 0x7000fe8000000000 0x008eb00000000000 0x0008eb0000000000

def z687 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdc004c19f0331f3e 0x1dc004c19f0331f3

def z688 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x0400c0078c60e1fe 0xf0400c0078c60e1f

def z689 : W := mkw 0x208b2c08ba9b0b1c 0x5208b2c08ba9b0b1 0x8a133c18739f1e01 0x08a133c18739f1e0

def z690 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0x8a333cf8739f1e01 0x08a333cf8739f1e0

def z691 : W := mkw 0x208b0408ba910b18 0x4208b0408ba910b1 0xdfcf4c19ffb31f3f 0xfdfcf4c19ffb31f3

def z692 : W := mkw 0x4500106251149941 0x0450010625114994 0xb2e200e6730099c5 0x7b2e200e6730099c

def z693 : W := mkw 0x4500106251149941 0x0450010625114994 0x9e7230e0731c1907 0x39e7230e0731c190

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x04008006004001c2 0x104008006004001c

def z695 : W := mkw 0x4000104250100900 0x0400010425010090 0xbee2b0e670101907 0x3bee2b0e67010190

def z696 : W := mkw 0x0204c105000020a2 0x20204c105000020a 0x75ccc3078000e1fc 0x175ccc3078000e1f

def z697 : W := mkw 0xa48006b8b111df10 0x0a48006b8b111df1 0xf02003f9f000ff3c 0x1f02003f9f000ff3

def z698 : W := mkw 0x0a000000046020a2 0x00a000000046020a 0x71cc03000c60e1fe 0xe71cc03000c60e1f

def z699 : W := mkw 0x4500106251149941 0x0450010625114994 0xb03000e6735c99c7 0x7b03000e6735c99c

def z700 : W := mkw 0x0c0000200fead40c 0x00c0000200fead40 0x001000000ffffe0f 0xe001000000ffffe0

def z701 : W := mkw 0x7124fd4ff0140941 0x37124fd4ff014094 0x0c10fc07f05c01c2 0x10c10fc07f05c01c

def z702 : W := mkw 0x0000000000000000 0x0000000000000000 0x0092b000034c0000 0x40092b000034c000

def z703 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x23ef03e00f80e001 0xe23ef03e00f80e00

def z704 : W := mkw 0xcf0fd3f75ff4fdeb 0x6cf0fd3f75ff4fde 0xfffff3fffffcffff 0xffffff3fffffcfff

def z705 : W := mkw 0x0004c10500000000 0x20004c1050000000 0x0400c00780000000 0x10400c0078000000

def z706 : W := mkw 0x02000105000020a2 0x002000105000020a 0x200003060000e0c0 0x0200003060000e0c

def z707 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffffff1e0f 0xfffffffffffff1e0

def z708 : W := mkw 0xfa2fffdfeee064aa 0x7fa2fffdfeee064a 0xffeffffffce0e7fe 0xfffeffffffce0e7f

def z709 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x8a23bcfe70000000 0x08a23bcfe7000000

def z710 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2b0e673ff99c7 0xfbef2b0e673ff99c

def z711 : W := mkw 0x7a24fd4fe46020a2 0x37a24fd4fe46020a 0xbee2fce7f06081f6 0x7bee2fce7f06081f

def z712 : W := mkw 0x800b029000000000 0x4800b02900000000 0xffef03f870000000 0x1ffef03f87000000

def z713 : W := mkw 0xd0affbd750110b10 0x7d0affbd750110b1 0x20aeb3e600b31f3f 0xa20aeb3e600b31f3

def z714 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x8e237cf9f0000000 0x18e237cf9f000000

def z715 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc000fff81c7 0xe0fdffc000fff81c

def z716 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffffff013f 0xfffffffffffff013

def z717 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03f80f80fe01 0x4f3ef03f80f80fe0

def z718 : W := mkw 0xf02b3fdfea8a000c 0x5f02b3fdfea8a000 0xfa333ffff39f0001 0x1fa333ffff39f000

def z719 : W := mkw 0xf02b17dfea800008 0x4f02b17dfea80000 0xf3ef03ffff800001 0xff3ef03ffff80000

def z720 : W := mkw 0xf82017dfeeea000c 0x0f82017dfeeea000 0xf03003ffffff0003 0xff03003ffffff000

def z721 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef3b0fe73dc9fc7 0x7bef3b0fe73dc9fc

def z722 : W := mkw 0x4500106251149941 0x0450010625114994 0xbff3fce6735c99c7 0x7bff3fce6735c99c

def z723 : W := mkw 0x4500106251149941 0x0450010625114994 0xaab2b0e6735c99c7 0x6aab2b0e6735c99c

def z724 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfffffffff31c0001 0x1fffffffff31c000

def z725 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff000013c 0x1ffeffffff000013

def z726 : W := mkw 0xba2fef9daeea20ae 0x7ba2fef9daeea20a 0x410d4f198ca36038 0x8410d4f198ca3603

def z727 : W := mkw 0x080fe9050eea000c 0x7080fe9050eea000 0x7fdfff078fff013f 0xf7fdfff078fff013

def z728 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf537c19f3bf1f3f 0xbdf537c19f3bf1f3

def z729 : W := mkw 0xf0afffdfe0010210 0x7f0afffdfe001021 0xffeffffff0b3063b 0xbffeffffff0b3063

def z730 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xf3ef4ffff0000000 0x1f3ef4ffff000000

def z731 : W := mkw 0xf02b3fdfe0000000 0x5f02b3fdfe000000 0xf0210ffff0000000 0x1f0210ffff000000

def z732 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0ad33c00039f0001 0x60ad33c00039f000

def z733 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xffef7ff9f0000000 0x1ffef7ff9f000000

def z734 : W := mkw 0x4000104240000000 0x0400010424000000 0xbe6000e670000000 0x1be6000e67000000

def z735 : W := mkw 0xf82fffdfe46a0004 0x7f82fffdfe46a000 0xfffffffff04c0000 0x1fffffffff04c000

def z736 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xffcd4f19f0b31f3f 0xbffcd4f19f0b31f3

def z737 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x9fdffc000fff1807 0xe9fdffc000fff180

def z738 : W := mkw 0xf22fffdfe00020a2 0x7f22fffdfe00020a 0xffeffffff020e1fe 0xbffeffffff020e1f

def z739 : W := mkw 0xf22017dfe00020a2 0x0f22017dfe00020a 0xf02003fff0006038 0x1f02003fff000603

def z740 : W := mkw 0xf82fffdfe4600000 0x7f82fffdfe460000 0xffeffffffcf30003 0xfffeffffffcf3000

def z741 : W := mkw 0x0a0fe8000eea20ae 0x70a0fe8000eea20a 0x0fdffc000fff603b 0xe0fdffc000fff603

def z742 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xffef03f87f80fe0d 0xfffef03f87f80fe0

def z743 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75cdcf078ce3e1fe 0xf75cdcf078ce3e1f

def z744 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xfef2b3fff35c0003 0x7fef2b3fff35c000

def z745 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0e9ffc000fff0003 0x40e9ffc000fff000

def z746 : W := mkw 0x4500106251149941 0x0450010625114994 0x0c32b0e6735c01c2 0x10c32b0e6735c01c

def z747 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x71cc43078c20e1fc 0xf71cc43078c20e1f

def z748 : W := mkw 0x080fe9050eea000c 0x7080fe9050eea000 0x2fdfff060fff0003 0xe2fdfff060fff000

def z749 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2b0e6737c99ff 0xfbef2b0e6737c99f

def z750 : W := mkw 0x7024fd4fe0000000 0x37024fd4fe000000 0x2ca2fce7f0000000 0x12ca2fce7f000000

def z751 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdfc3fc19f0b31f3f 0xbdfc3fc19f0b31f3

def z752 : W := mkw 0xf02b16dae0000000 0x4f02b16dae000000 0x822300f870000000 0x0822300f87000000

def z753 : W := mkw 0xf02b17dfe0000000 0x4f02b17dfe000000 0xffef4ffff0000000 0x1ffef4ffff000000

def z754 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc20613e 0xbffeffffffc20613

def z755 : W := mkw 0x880fea900eea000c 0x7880fea900eea000 0xfffffff80fffe00f 0xefffffff80fffe00

def z756 : W := mkw 0x0a04e9050eea20ae 0x30a04e9050eea20a 0x0c10fc078fffe1ff 0xf0c10fc078fffe1f

def z757 : W := mkw 0x8c04eab0056ad404 0x38c04eab0056ad40 0xfc30fff8007ffe0e 0x0fc30fff8007ffe0

def z758 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf4e083fff04081c6 0x7f4e083fff04081c

def z759 : W := mkw 0x400ff84240000000 0x7400ff8424000000 0xbeeeb0e670000000 0x1beeeb0e67000000

def z760 : W := mkw 0x4500106241049041 0x0450010624104904 0xaab2b0e6734c80c0 0x4aab2b0e6734c80c

def z761 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000031c9805 0x600100000031c980

def z762 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0b533c00039f0001 0xa0b533c00039f000

def z763 : W := mkw 0x400b38424a8a000c 0x5400b38424a8a000 0xbef3bce6739f0001 0x1bef3bce6739f000

def z764 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xf5eef3fff0000000 0x1f5eef3fff000000

def z765 : W := mkw 0x840b2ab00b80d408 0x5840b2ab00b80d40 0xfbef3ff80f80fe0d 0xefbef3ff80f80fe0

def z766 : W := mkw 0x0f04c0201574b9e3 0x20f04c0201574b9e 0x0fdef0000f7cf9ff 0xe0fdef0000f7cf9f

def z767 : W := mkw 0xf82ffedaeeea000c 0x7f82ffedaeeea000 0xfffffff87fff0003 0xefffffff87fff000

def z768 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0001805 0x3ffeffffff000180

def z769 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf12d03f80f80fe0d 0xef12d03f80f80fe0

def z770 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc60e0f8 0xdffeffffffc60e0f

def z771 : W := mkw 0x0a0fe8000eea20ae 0x70a0fe8000eea20a 0x3fdffc060fffe1ff 0xf3fdffc060fffe1f

def z772 : W := mkw 0x2a84c50db4712bb2 0x22a84c50db4712bb 0xaa8d8f1e7cd3fec1 0x4aa8d8f1e7cd3fec

def z773 : W := mkw 0xf02b16dae0000000 0x4f02b16dae000000 0xf3ef03f870000000 0x0f3ef03f87000000

def z774 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x708c83078c60e1fe 0xf708c83078c60e1f

def z775 : W := mkw 0x4500106251149941 0x0450010625114994 0x2ef2b0e6735c81c3 0x72ef2b0e6735c81c

def z776 : W := mkw 0xf22fffdfe00020a2 0x7f22fffdfe00020a 0xffeffffffc00e1fc 0xfffeffffffc00e1f

def z777 : W := mkw 0x4000104240000000 0x0400010424000000 0xffeeb3e670000000 0x1ffeeb3e67000000

def z778 : W := mkw 0x4580106251159b51 0x04580106251159b5 0xbff3fce673ff9fff 0xfbff3fce673ff9ff

def z779 : W := mkw 0xfa2fffdfe46a20a6 0x7fa2fffdfe46a20a 0xfffffffff07f01f2 0x1fffffffff07f01f

def z780 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0b31e0f 0xbffeffffff0b31e0

def z781 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x019ffc000fff0003 0xe019ffc000fff000

def z782 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x7fcef3078c60e1fe 0xf7fcef3078c60e1f

def z783 : W := mkw 0x800b02900a804408 0x4800b02900a80440 0xf3ef03f80c807e0d 0xaf3ef03f80c807e0

def z784 : W := mkw 0x400ff84240000000 0x7400ff8424000000 0x8feffce070000000 0x08feffce07000000

def z785 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03f80fc0ffcf 0xef3ef03f80fc0ffc

def z786 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf514c19f3ff1f3f 0xfdf514c19f3ff1f3

def z787 : W := mkw 0x0a0fe8000eea20ae 0x70a0fe8000eea20a 0x5fdffc018fffe1ff 0xf5fdffc018fffe1f

def z788 : W := mkw 0x0500002011149941 0x0050000201114994 0x0f514c0003ff99c7 0xe0f514c0003ff99c

def z789 : W := mkw 0xd02ffbd740000000 0x7d02ffbd74000000 0xffefb3fe70000000 0x1ffefb3fe7000000

def z790 : W := mkw 0x000fe8000a8a000c 0x7000fe8000a8a000 0x0a9fbc00039f0001 0x00a9fbc00039f000

def z791 : W := mkw 0x840b02b00b8ad40c 0x4840b02b00b8ad40 0xf3ff03f80f9ffe0d 0xef3ff03f80f9ffe0

def z792 : W := mkw 0x800b2a900a8a000c 0x5800b2a900a8a000 0xfbff3ff8039f0001 0x0fbff3ff8039f000

def z793 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf414c19f0a31f3c 0x9df414c19f0a31f3

def z794 : W := mkw 0x4000104240000000 0x0400010424000000 0xffe2f0e7f0000000 0x1ffe2f0e7f000000

def z795 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000035c81c2 0x400100000035c81c

def z796 : W := mkw 0x050b28201b9e994d 0x5050b28201b9e994 0x0a133c0003df99c7 0x60a133c0003df99c

def z797 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0b9ffc000fff0001 0xc0b9ffc000fff000

def z798 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf1ec03fff0000000 0x1f1ec03fff000000

def z799 : W := mkw 0x4500106251149941 0x0450010625114994 0xa0b2b0e6734c98c0 0x4a0b2b0e6734c98c

def z800 : W := mkw 0x4d0ff8625ffe994d 0x74d0ff8625ffe994 0xb12d4ce67ca399c4 0x9b12d4ce67ca399c

def z801 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xfe6003fff0000000 0x1fe6003fff000000

def z802 : W := mkw 0x0804e8000eea000c 0x30804e8000eea000 0x0ddcfc000fff0003 0xe0ddcfc000fff000

def z803 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0b3013f 0xbffeffffff0b3013

def z804 : W := mkw 0x4500106251149941 0x0450010625114994 0xfef2b3e6735cf9cf 0x7fef2b3e6735cf9c

def z805 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000037c99ff 0xe00100000037c99f

def z806 : W := mkw 0xc10b12d25a944d49 0x4c10b12d25a944d4 0x4d1db31e7cdc67ca 0x94d1db31e7cdc67c

def z807 : W := mkw 0x0a04e905046a20a6 0x30a04e905046a20a 0x3ed2fc07837f81f7 0x73ed2fc07837f81f

def z808 : W := mkw 0x0f8000201575bbf3 0x00f8000201575bbf 0x001000000fffffff 0xe001000000ffffff

def z809 : W := mkw 0x080b28000eea000c 0x5080b28000eea000 0x0a133c0003ff0003 0x00a133c0003ff000

def z810 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x8bef3cf870000000 0x08bef3cf87000000

def z811 : W := mkw 0x0804c00004600000 0x20804c0000460000 0x0fdffc000fff0003 0xe0fdffc000fff000

def z812 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0xf7ccc3078c60f9ff 0xff7ccc3078c60f9f

def z813 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfffffffff3ff0003 0xffffffffff3ff000

def z814 : W := mkw 0x4000104240000000 0x0400010424000000 0xffe3b0fe70000000 0x1ffe3b0fe7000000

def z815 : W := mkw 0x048000201b91df18 0x0048000201b91df1 0x75cc43018fb3ff3f 0xf75cc43018fb3ff3

def z816 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf414c19fcb3ff3f 0xfdf414c19fcb3ff3

def z817 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xffef03f80f90fe0f 0xeffef03f80f90fe0

def z818 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x77cec3078f60e1ff 0xf77cec3078f60e1f

def z819 : W := mkw 0x0500002011149941 0x0050000201114994 0x02d20000035c99c7 0x602d20000035c99c

def z820 : W := mkw 0x6580146ae1059251 0x06580146ae105925 0x61b3fcff83ef86f8 0xc61b3fcff83ef86f

def z821 : W := mkw 0xa0000698a0000000 0x0a0000698a000000 0xf02003f9f0000000 0x1f02003f9f000000

def z822 : W := mkw 0xf02016dae0000000 0x0f02016dae000000 0xd02000f9f0000000 0x1d02000f9f000000

def z823 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf0ae03f80f80fe0d 0xef0ae03f80f80fe0

def z824 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x208c83078c40e1f0 0x5208c83078c40e1f

def z825 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef3bce673df99c7 0x7bef3bce673df99c

def z826 : W := mkw 0x4000104240000000 0x0400010424000000 0x9e6230e070000000 0x19e6230e07000000

def z827 : W := mkw 0x840002b00100d400 0x0840002b00100d40 0xf0ac03f80c00fe0c 0x4f0ac03f80c00fe0

def z828 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xffc14c19f0b39f3f 0xfffc14c19f0b39f3

def z829 : W := mkw 0x0d00002015749941 0x00d0000201574994 0x001000000f7c99c7 0xe001000000f7c99c

def z830 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf7ef03f80f80ff0f 0xff7ef03f80f80ff0

def z831 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2b0e673dc9fcf 0xfbef2b0e673dc9fc

def z832 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffeffffffc000000 0x1ffeffffffc00000

def z833 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x7ddcf3078c7ce1fe 0xf7ddcf3078c7ce1f

def z834 : W := mkw 0x4000104240000000 0x0400010424000000 0xbef2b0e6735c81c7 0x7bef2b0e6735c81c

def z835 : W := mkw 0x840002b00b80d408 0x0840002b00b80d40 0xf1ec03f80f80fe0d 0xef1ec03f80f80fe0

def z836 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xf12d4ffffc20e1fc 0x9f12d4ffffc20e1f

def z837 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x822f03f80f807e01 0x0822f03f80f807e0

def z838 : W := mkw 0xfa2fffdfeeea20ae 0x7fa2fffdfeeea20a 0xffeffffffce3e1fe 0xfffeffffffce3e1f

def z839 : W := mkw 0xf0afffdfe0010210 0x7f0afffdfe001021 0xffeffffff0230030 0x1ffeffffff023003

def z840 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x7bdf3f000f9fe00d 0xe7bdf3f000f9fe00

def z841 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0x202003e7f0000000 0x1202003e7f000000

def z842 : W := mkw 0xf0afffdfe0010210 0x7f0afffdfe001021 0xffeffffff0a3073e 0xbffeffffff0a3073

def z843 : W := mkw 0x42001147400020a2 0x042001147400020a 0xf02003e7f000e1fc 0x1f02003e7f000e1f

def z844 : W := mkw 0x4500106251149941 0x0450010625114994 0xffffb3fe7fdcffcf 0xfffffb3fe7fdcffc

def z845 : W := mkw 0x4580106251159b51 0x04580106251159b5 0xbef2b0e6735c9fff 0x7bef2b0e6735c9ff

def z846 : W := mkw 0x4a04d147446020a2 0x24a04d147446020a 0xbeeeb3e67c40e0c0 0x5beeeb3e67c40e0c

def z847 : W := mkw 0x0a04e905046a20a6 0x30a04e905046a20a 0x7fdeff078f7fe1ff 0xf7fdeff078f7fe1f

def z848 : W := mkw 0x4500106251149941 0x0450010625114994 0xbaf2b0e6735c98c5 0x6baf2b0e6735c98c

def z849 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xcb014c19f0b31f3f 0xacb014c19f0b31f3

def z850 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xfa233ff870000000 0x0fa233ff87000000

def z851 : W := mkw 0x4f04d1675574b9e3 0x24f04d1675574b9e 0xcb3e73e1ff3c7839 0x8cb3e73e1ff3c783

def z852 : W := mkw 0xf02fffdfea800008 0x7f02fffdfea80000 0xffffffffffdc0003 0xfffffffffffdc000

def z853 : W := mkw 0x4500106251149941 0x0450010625114994 0x8ef2b0e6735c19c3 0x78ef2b0e6735c19c

def z854 : W := mkw 0x050000201b94dd49 0x0050000201b94dd4 0x0010000003dc9fc7 0x60010000003dc9fc

def z855 : W := mkw 0x000fe8000a8a000c 0x7000fe8000a8a000 0x0fdffc000f9f0001 0xe0fdffc000f9f000

def z856 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2b0e67f5cf9cf 0xfbef2b0e67f5cf9c

def z857 : W := mkw 0x070000201114b9e3 0x0070000201114b9e 0x00100000035cf9ff 0x600100000035cf9f

def z858 : W := mkw 0x0500002011149941 0x0050000201114994 0x30100006035c99c7 0x730100006035c99c

def z859 : W := mkw 0x0f0fe9251ffeb9ef 0x70f0fe9251ffeb9e 0x7fdfff078ffff9ff 0xf7fdfff078ffff9f

def z860 : W := mkw 0x0500002011149941 0x0050000201114994 0x0ed2b000035c1803 0x60ed2b000035c180

def z861 : W := mkw 0x7020154fe0000000 0x07020154fe000000 0xbee2b0e7f0000000 0x1bee2b0e7f000000

def z862 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xcb3f7ff9ffbf0001 0x8cb3f7ff9ffbf000

def z863 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x2fdfff060fffe1ff 0xe2fdfff060fffe1f

def z864 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdfc1cc19f0f31f3f 0xfdfc1cc19f0f31f3

def z865 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0e533c00039f0003 0x20e533c00039f000

def z866 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x750cc3078c60e1fe 0x9750cc3078c60e1f

def z867 : W := mkw 0xf02fffdfea804408 0x7f02fffdfea80440 0xffeffffffc80e60c 0xfffeffffffc80e60

def z868 : W := mkw 0xfa24d7dfe46020a2 0x2fa24d7dfe46020a 0xf420c3fff06001f2 0x1f420c3fff06001f

def z869 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf1ee03f80f00fe0c 0xef1ee03f80f00fe0

def z870 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03f80c80fe0c 0x8f3ef03f80c80fe0

def z871 : W := mkw 0x080b28000eea000c 0x5080b28000eea000 0x0a133c000fdf0001 0x40a133c000fdf000

def z872 : W := mkw 0x0d0fe8201ffe994d 0x70d0fe8201ffe994 0x011d4c000fff99c7 0xe011d4c000fff99c

def z873 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x7fdfff060fffe1cf 0xf7fdfff060fffe1c

def z874 : W := mkw 0xf02016dae0000000 0x0f02016dae000000 0xb02000fe70000000 0x1b02000fe7000000

def z875 : W := mkw 0x080b28000eea000c 0x5080b28000eea000 0x0f537c000fff0003 0xe0f537c000fff000

def z876 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0edefc000f7f0003 0x60edefc000f7f000

def z877 : W := mkw 0x4000104240000000 0x0400010424000000 0xbee2b0e670400002 0x7bee2b0e67040000

def z878 : W := mkw 0x4500106251149941 0x0450010625114994 0x0010b006035c99c7 0x60010b006035c99c

def z879 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0xf7eec3e78c60e1fe 0xff7eec3e78c60e1f

def z880 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xff6d4ffff0000000 0x1ff6d4ffff000000

def z881 : W := mkw 0xb52fefbdb1149941 0x7b52fefbdb114994 0x411d4f19835c99c7 0x6411d4f19835c99c

def z882 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x4fdfff018fffe1ff 0xe4fdfff018fffe1f

def z883 : W := mkw 0xf024d7dfe0000000 0x2f024d7dfe000000 0xffedcffff0000000 0x1ffedcffff000000

def z884 : W := mkw 0x4000104240000000 0x0400010424000000 0x2ca2b0e670000000 0x12ca2b0e67000000

def z885 : W := mkw 0x000b00000a800008 0x4000b00000a80000 0x0fdffc000fff0003 0xe0fdffc000fff000

def z886 : W := mkw 0x4000104240000000 0x0400010424000000 0x8ee2b0e070000000 0x08ee2b0e07000000

def z887 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0fdf7c000fbf0003 0xe0fdf7c000fbf000

def z888 : W := mkw 0xf02fffdfea8a000c 0x7f02fffdfea8a000 0xfffffffff3df0003 0x7fffffffff3df000

def z889 : W := mkw 0x0804e800046a0004 0x30804e800046a000 0x0e12fc00037f0003 0x00e12fc00037f000

def z890 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf1214ffff0000000 0x1f1214ffff000000

def z891 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x20aeb3e7f0000000 0x120aeb3e7f000000

def z892 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffff06001fe 0xbffeffffff06001f

def z893 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff00081c4 0x1ffeffffff00081c

def z894 : W := mkw 0xe00b16dae0000000 0x4e00b16dae000000 0xffeffffff0000000 0x1ffeffffff000000

def z895 : W := mkw 0x0500002011149941 0x0050000201114994 0x00000000030099c5 0x600000000030099c

def z896 : W := mkw 0xfa2b3edae46020a2 0x5fa2b3edae46020a 0x8a233cf87c60e1fe 0xe8a233cf87c60e1f

def z897 : W := mkw 0xf02ffedae0000000 0x7f02ffedae000000 0xdfeffcf9f0000000 0x1dfeffcf9f000000

def z898 : W := mkw 0xa48b06b8bb91df18 0x4a48b06b8bb91df1 0x2cae4fe1ff33e132 0x52cae4fe1ff33e13

def z899 : W := mkw 0x5024f94740000000 0x35024f9474000000 0xbee2b0e670000000 0x1bee2b0e67000000

def z900 : W := mkw 0x0500002011149941 0x0050000201114994 0x30d00000035c99c7 0x630d00000035c99c

def z901 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000034c99c4 0x400100000034c99c

def z902 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xdf637cf9f020013e 0xbdf637cf9f020013

def z903 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef43f98fa0fe3d 0xef3ef43f98fa0fe3

def z904 : W := mkw 0xf22017dfe00020a2 0x0f22017dfe00020a 0xf02003fff000e0c0 0x1f02003fff000e0c

def z905 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffeffffffcb30003 0xbffeffffffcb3000

def z906 : W := mkw 0xf02b17dfe0000000 0x4f02b17dfe000000 0xf12d03fff0000000 0x1f12d03fff000000

def z907 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x08123c00031f0000 0x008123c00031f000

def z908 : W := mkw 0x4500106251149941 0x0450010625114994 0xbcb2b0e6735c99c6 0x5bcb2b0e6735c99c

def z909 : W := mkw 0x0500002011149941 0x0050000201114994 0x20908006035c99c7 0x620908006035c99c

def z910 : W := mkw 0xf024ffdfe0000000 0x3f024ffdfe000000 0xfdecfffff0000000 0x1fdecfffff000000

def z911 : W := mkw 0x880fea900eea000c 0x7880fea900eea000 0x4fdfff180fff0003 0xe4fdfff180fff000

def z912 : W := mkw 0x0500002011149941 0x0050000201114994 0x55504001837c99ff 0xf55504001837c99f

def z913 : W := mkw 0x0804e800046a0004 0x30804e800046a000 0x0fd3fc0003ff0003 0xe0fd3fc0003ff000

def z914 : W := mkw 0xf12fffdfe0040041 0x7f12fffdfe004004 0xfffffffff04c00c0 0x1fffffffff04c00c

def z915 : W := mkw 0x0804e800046a0004 0x30804e800046a000 0x0c92fc00037f0002 0x40c92fc00037f000

def z916 : W := mkw 0xa80fee98aeea000c 0x7a80fee98aeea000 0xfffffff9ffff0003 0xffffffff9ffff000

def z917 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf4e083fff0000000 0x1f4e083fff000000

def z918 : W := mkw 0x4500106251149941 0x0450010625114994 0x8a32b0e6735c18c1 0x08a32b0e6735c18c

def z919 : W := mkw 0xa00b0698a0000000 0x4a00b0698a000000 0xf3ef03f9f0000000 0x1f3ef03f9f000000

def z920 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfffffffff34c0000 0x5fffffffff34c000

def z921 : W := mkw 0x450010625114dd41 0x0450010625114dd4 0xbef2b0e6735cffcf 0x7bef2b0e6735cffc

def z922 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x2fdfff000fffe003 0xe2fdfff000fffe00

def z923 : W := mkw 0xf22017dfe00020a2 0x0f22017dfe00020a 0xf02003fff00001f0 0x1f02003fff00001f

def z924 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xa02003fe70000000 0x0a02003fe7000000

def z925 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x700c03078c00e1fc 0x1700c03078c00e1f

def z926 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x4d014c19f0b31f3f 0xb4d014c19f0b31f3

def z927 : W := mkw 0xa00b0698aa800008 0x4a00b0698aa80000 0xffef4ff9ffb30003 0xfffef4ff9ffb3000

def z928 : W := mkw 0x400b10424a800008 0x4400b10424a80000 0xbfefb0e67f800001 0xfbfefb0e67f80000

def z929 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x710c43078c60e1fe 0xf710c43078c60e1f

def z930 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xdf6f7ff9f0000000 0x1df6f7ff9f000000

def z931 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc60e1f2 0x5ffeffffffc60e1f

def z932 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf414c19f0b31e39 0x9df414c19f0b31e3

def z933 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xf0beb3ffff4c0000 0x5f0beb3ffff4c000

def z934 : W := mkw 0x4100104250140941 0x0410010425014094 0xbef2b0e6735c01c3 0x7bef2b0e6735c01c

def z935 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x4fdffc180fff060b 0xe4fdffc180fff060

def z936 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x8a133c18039f1e01 0x08a133c18039f1e0

def z937 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03f98f80ff3d 0xff3ef03f98f80ff3

def z938 : W := mkw 0xf82fffdfe4600000 0x7f82fffdfe460000 0xffeffffffc200000 0x9ffeffffffc20000

def z939 : W := mkw 0x4000104240000000 0x0400010424000000 0x8ef2b0e0735c0003 0x68ef2b0e0735c000

def z940 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xf1affffff0000000 0x1f1affffff000000

def z941 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdb014c19f0b31f3d 0x9db014c19f0b31f3

def z942 : W := mkw 0x4100104240040041 0x0410010424004004 0xbef2b0e6704c00c0 0x1bef2b0e6704c00c

def z943 : W := mkw 0x6b84d54ff4752bf3 0x26b84d54ff4752bf 0x0c10fc07f07f01f2 0x10c10fc07f07f01f

def z944 : W := mkw 0x4a001042446020a2 0x04a001042446020a 0xbee2b0e67c60e1fe 0xfbee2b0e67c60e1f

def z945 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x7fdfff078fffe1ff 0xf7fdfff078fffe1f

def z946 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x802230f870000000 0x0802230f87000000

def z947 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0x2cbeffe7ff7f0002 0x52cbeffe7ff7f000

def z948 : W := mkw 0xfa24d7dfe46020a2 0x2fa24d7dfe46020a 0xf12c43fffc206038 0x9f12c43fffc20603

def z949 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf414c19f0b31f33 0x1df414c19f0b31f3

def z950 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0bdf3c00039f0001 0x00bdf3c00039f000

def z951 : W := mkw 0x4580106251159b51 0x04580106251159b5 0xbef2b0e673df9fc7 0x7bef2b0e673df9fc

def z952 : W := mkw 0x20800408a0010210 0x020800408a001021 0xdf414c19f0a31e3d 0xbdf414c19f0a31e3

def z953 : W := mkw 0xf02fd7dfe0000000 0x6f02fd7dfe000000 0xf7efc3fff0000000 0x1f7efc3fff000000

def z954 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xcfeffff9f0000000 0x0cfeffff9f000000

def z955 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0a137c0003bf0001 0x00a137c0003bf000

def z956 : W := mkw 0xf82fffdfe4600000 0x7f82fffdfe460000 0xffeffffffc60e00e 0xfffeffffffc60e00

def z957 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x0fdfff000fff6003 0xe0fdfff000fff600

def z958 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff06081fe 0xfffeffffff06081f

def z959 : W := mkw 0x24000428ab80d408 0x024000428ab80d40 0xdf414c19ff80fe0d 0xfdf414c19ff80fe0

def z960 : W := mkw 0xf0afffdfe0010210 0x7f0afffdfe001021 0xffeffffff0a31e3d 0xbffeffffff0a31e3

def z961 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x9e633cf870000000 0x19e633cf87000000

def z962 : W := mkw 0x480ff8424eea000c 0x7480ff8424eea000 0xbfeffce67ca30000 0x9bfeffce67ca3000

def z963 : W := mkw 0x4500106251149941 0x0450010625114994 0xfff3fce7f3ff99ff 0xffff3fce7f3ff99f

def z964 : W := mkw 0x850b02b00b84d449 0x4850b02b00b84d44 0xf3ff03f80fccfecd 0xef3ff03f80fccfec

def z965 : W := mkw 0x0d0fe8201ffe994d 0x70d0fe8201ffe994 0x3fdffc060fff99c7 0xf3fdffc060fff99c

def z966 : W := mkw 0xf82fffdfe4600000 0x7f82fffdfe460000 0xffeffffffc60013e 0xfffeffffffc60013

def z967 : W := mkw 0x288fec08befb0b1c 0x7288fec08befb0b1 0xd09eb019ff4c1f3c 0x5d09eb019ff4c1f3

def z968 : W := mkw 0x7aa4fd4ff4712bb2 0x37aa4fd4ff4712bb 0x0c00fc07f07301f2 0x10c00fc07f07301f

def z969 : W := mkw 0x7020154fe0000000 0x07020154fe000000 0xb02000e7f0000000 0x1b02000e7f000000

def z970 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xc1014c19f0a31e38 0x8c1014c19f0a31e3

def z971 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xa0aeb3fe70000000 0x0a0aeb3fe7000000

def z972 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x71cc83078c40e1fc 0xf71cc83078c40e1f

def z973 : W := mkw 0x7024fd4fe0000000 0x37024fd4fe000000 0x8e22fce7f0000000 0x18e22fce7f000000

def z974 : W := mkw 0x25800428b1159b51 0x025800428b1159b5 0x41114c1983ff9fff 0xe41114c1983ff9ff

def z975 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x34ccc3078c60e1f6 0x734ccc3078c60e1f

def z976 : W := mkw 0xf82fffdfe46a0004 0x7f82fffdfe46a000 0xffeffffff0230000 0x1ffeffffff023000

def z977 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x3fdfff060fffe1c7 0xf3fdfff060fffe1c

def z978 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffffdf0001 0x5ffffffffffdf000

def z979 : W := mkw 0xf22fffdfe00020a2 0x7f22fffdfe00020a 0xffeffffff0006038 0x1ffeffffff000603

def z980 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x8ee3bcf870000000 0x08ee3bcf87000000

def z981 : W := mkw 0x4000104240000000 0x0400010424000000 0xba2230e670000000 0x1ba2230e67000000

def z982 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x4b1f7f018fbf6039 0x84b1f7f018fbf603

def z983 : W := mkw 0xf024ffdfe0000000 0x3f024ffdfe000000 0xf020b3fff0000000 0x1f020b3fff000000

def z984 : W := mkw 0x21800408b0150b51 0x021800408b0150b5 0xdf514c19f0ff1fff 0xbdf514c19f0ff1ff

def z985 : W := mkw 0x0f04c1251574b9e3 0x20f04c1251574b9e 0x209c83060f5cf9c7 0x6209c83060f5cf9c

def z986 : W := mkw 0x4000104240000000 0x0400010424000000 0xb02000e6700081c4 0x1b02000e6700081c

def z987 : W := mkw 0x4000104240000000 0x0400010424000000 0xb0a2b0e670000000 0x1b0a2b0e67000000

def z988 : W := mkw 0xfa2fffdfeee020aa 0x7fa2fffdfeee020a 0xffefffffffe0e1ff 0xfffefffffffe0e1f

def z989 : W := mkw 0xf82fffdfeeea440c 0x7f82fffdfeeea440 0xffffffffffff660b 0xfffffffffffff660

def z990 : W := mkw 0xf5a017fff1159b51 0x0f5a017fff1159b5 0xf02003fff0009ffc 0x1f02003fff0009ff

def z991 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x618cc3078c60e1fe 0xe618cc3078c60e1f

def z992 : W := mkw 0xf024d7dfe0000000 0x2f024d7dfe000000 0xffeef3fff0000000 0x1ffeef3fff000000

def z993 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0xdfdffc180fff0003 0xedfdffc180fff000

def z994 : W := mkw 0x4500106251149941 0x0450010625114994 0xaeb2b0e6735c99c3 0x5aeb2b0e6735c99c

def z995 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0x61af03f80f80fe0d 0xe61af03f80f80fe0

def z996 : W := mkw 0xfa24ffdfe46020a2 0x3fa24ffdfe46020a 0xfc20fffff060e1fe 0x1fc20fffff060e1f

def z997 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf56043fff020013e 0xbf56043fff020013

def z998 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xfbef0ff80f93fe0d 0xefbef0ff80f93fe0

def z999 : W := mkw 0xa0000698a0000000 0x0a0000698a000000 0xff614ff9f0000000 0x1ff614ff9f000000

def z1000 : W := mkw 0xf024d7dfe0000000 0x2f024d7dfe000000 0xf420c3fff0000000 0x1f420c3fff000000

def z1001 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xfbff33f80f9cfe0d 0xefbff33f80f9cfe0

def z1002 : W := mkw 0x6a04d54fe46020a2 0x26a04d54fe46020a 0xffeffffffc60e1fe 0xfffeffffffc60e1f

def z1003 : W := mkw 0xf02fffdfea804408 0x7f02fffdfea80440 0xffeffffffc006000 0x1ffeffffffc00600

def z1004 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf2af03f80f80fe0d 0x4f2af03f80f80fe0

def z1005 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0edfbc000fdf0003 0x60edfbc000fdf000

def z1006 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xffe3fcfff0000000 0x1ffe3fcfff000000

def z1007 : W := mkw 0x4500106241049041 0x0450010624104904 0xbef2b0e6734c81c6 0x7bef2b0e6734c81c

def z1008 : W := mkw 0x4500106241049041 0x0450010624104904 0xbef2b0e6735c80c3 0x7bef2b0e6735c80c

def z1009 : W := mkw 0x0580002011159b51 0x00580002011159b5 0x00100000035c9fff 0x600100000035c9ff

def z1010 : W := mkw 0x840002b00100d400 0x0840002b00100d40 0xf3ee03f80f00fe0d 0xef3ee03f80f00fe0

def z1011 : W := mkw 0xfa2fffdfe46a20a6 0x7fa2fffdfe46a20a 0xfffffffffc7fe1fe 0xffffffffffc7fe1f

def z1012 : W := mkw 0xf8afffdfeeeb021c 0x7f8afffdfeeeb021 0xffeffffffca30638 0x9ffeffffffca3063

def z1013 : W := mkw 0x048b00201b91df18 0x4048b00201b91df1 0x0fcf4c000fb3ff3f 0xe0fcf4c000fb3ff3

def z1014 : W := mkw 0xf02016dae0000000 0x0f02016dae000000 0xbee2b0fe70000000 0x1bee2b0fe7000000

def z1015 : W := mkw 0x480ff84244600000 0x7480ff8424460000 0xbfeffce67c6081c6 0xfbfeffce67c6081c

def z1016 : W := mkw 0x840002b00100d400 0x0840002b00100d40 0xf12c03f80c00fe0c 0x8f12c03f80c00fe0

def z1017 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2b0e6735c19c3 0x1bef2b0e6735c19c

def z1018 : W := mkw 0x0000000000000000 0x0000000000000000 0xbee200e070000000 0x1bee200e07000000

def z1019 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xa3ef03f80f80fe01 0xea3ef03f80f80fe0

def z1020 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xffd3fc1ff3ff9fff 0xfffd3fc1ff3ff9ff

def z1021 : W := mkw 0x0f04c1251ffeb9ef 0x20f04c1251ffeb9e 0x75dcc3078ffff9ff 0xf75dcc3078ffff9f

def z1022 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff000000c 0xbffeffffff000000

def z1023 : W := mkw 0xc00012d240000000 0x0c00012d24000000 0xf02003fe70000000 0x1f02003fe7000000

def z1024 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x9e414c19f0b31f37 0x39e414c19f0b31f3

def z1025 : W := mkw 0x0d8fe8201fff9b5d 0x70d8fe8201fff9b5 0x0fdffc000fff9fff 0xe0fdffc000fff9ff

def z1026 : W := mkw 0x400b384240000000 0x5400b38424000000 0xbee3bce670000000 0x1bee3bce67000000

def z1027 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0xffccc307fc60e1fe 0xfffccc307fc60e1f

def z1028 : W := mkw 0x4000104240000000 0x0400010424000000 0xbfe3fce670000000 0x1bfe3fce67000000

def z1029 : W := mkw 0x4000104240000000 0x0400010424000000 0xaaa2b0e670000000 0x0aaa2b0e67000000

def z1030 : W := mkw 0x400b38424a8a000c 0x5400b38424a8a000 0x8a333ce0739f0001 0x08a333ce0739f000

def z1031 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xcb2f3ff870000000 0x0cb2f3ff87000000

def z1032 : W := mkw 0xa00b0698a0000000 0x4a00b0698a000000 0xdf634cf9f0000000 0x1df634cf9f000000

def z1033 : W := mkw 0xa08b0698aa814618 0x4a08b0698aa81461 0xffef4ff9fca36638 0x9ffef4ff9fca3663

def z1034 : W := mkw 0x0500002011149941 0x0050000201114994 0x00000000001099c7 0x200000000001099c

def z1035 : W := mkw 0x0d000020157e9945 0x00d000020157e994 0x00100000037f99c7 0x600100000037f99c

def z1036 : W := mkw 0xf024ffdfe0000000 0x3f024ffdfe000000 0x8c20fcfff0000000 0x18c20fcfff000000

def z1037 : W := mkw 0x050b00201b94dd49 0x4050b00201b94dd4 0x0fdfb0000fdcffcf 0xe0fdfb0000fdcffc

def z1038 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x3fdffc060fff0003 0xf3fdffc060fff000

def z1039 : W := mkw 0x0400002001009000 0x0040000200100900 0xf3ef03f80f80fe0d 0xef3ef03f80f80fe0

def z1040 : W := mkw 0xf02016dae0000000 0x0f02016dae000000 0x8a210cf870000000 0x08a210cf87000000

def z1041 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc000f7f0002 0x40fdffc000f7f000

def z1042 : W := mkw 0x0500002011149941 0x0050000201114994 0x0010000003ff99c7 0xe0010000003ff99c

def z1043 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x2fdffc060fff80c3 0xe2fdffc060fff80c

def z1044 : W := mkw 0x4500106251149941 0x0450010625114994 0xb0b2b0e6735c99c7 0x7b0b2b0e6735c99c

def z1045 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0bdfbc000fdf0001 0xe0bdfbc000fdf000

def z1046 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x089ebc000f5f0000 0x4089ebc000f5f000

def z1047 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x2fdfff078fffe1f3 0xf2fdfff078fffe1f

def z1048 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf2ee03f80f00fe0d 0x6f2ee03f80f00fe0

def z1049 : W := mkw 0x4a0ff9474eea20ae 0x74a0ff9474eea20a 0xffffffe7ffffe1ff 0xfffffffe7ffffe1f

def z1050 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xd1014c19f0b31f3f 0xbd1014c19f0b31f3

def z1051 : W := mkw 0x8a0feb950eea64ae 0x78a0feb950eea64a 0x7fdfff1f8fffe7ff 0xf7fdfff1f8fffe7f

def z1052 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0xf7cdc31f8c60e1fe 0xff7cdc31f8c60e1f

def z1053 : W := mkw 0x840b2ab00b8ad40c 0x5840b2ab00b8ad40 0xf3ef0ff80f83fe0d 0xef3ef0ff80f83fe0

def z1054 : W := mkw 0x6080144ae0010210 0x06080144ae001021 0xffe3fcfff0a30638 0x9ffe3fcfff0a3063

def z1055 : W := mkw 0x840b2ab00b8ad40c 0x5840b2ab00b8ad40 0xf3ff33f80f8cfe0d 0xef3ff33f80f8cfe0

def z1056 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfd2dfffff0000000 0x1fd2dfffff000000

def z1057 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0xf5e0c0fff0609ffe 0xff5e0c0fff0609ff

def z1058 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x2fefffe7f0000000 0x12fefffe7f000000

def z1059 : W := mkw 0x050000201b949949 0x0050000201b94994 0x001000000fdc99c7 0xe001000000fdc99c

def z1060 : W := mkw 0xca0fd3d7446020a2 0x6ca0fd3d7446020a 0xffeff3fffc60e1fe 0xfffeff3fffc60e1f

def z1061 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xf3efb3fff0000000 0x1f3efb3fff000000

def z1062 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xf0aeb3fffc40e1fc 0x5f0aeb3fffc40e1f

def z1063 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ff03f80fdcfe0f 0xef3ff03f80fdcfe0

def z1064 : W := mkw 0xf0a017dfe0010210 0x0f0a017dfe001021 0xf1214ffff0a30638 0x9f1214ffff0a3063

def z1065 : W := mkw 0xf02fffdfea8a000c 0x7f02fffdfea8a000 0xfffffffff30c0000 0x1fffffffff30c000

def z1066 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000035c98c1 0x400100000035c98c

def z1067 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x7fccc3078c70e1ff 0xf7fccc3078c70e1f

def z1068 : W := mkw 0xd02013d740000000 0x0d02013d74000000 0xbee2b3e670000000 0x1bee2b3e67000000

def z1069 : W := mkw 0xf02fffdfea800008 0x7f02fffdfea80000 0xffefffffffb30003 0xfffefffffffb3000

def z1070 : W := mkw 0x4000104240000000 0x0400010424000000 0xbef2b0e6731c0001 0x1bef2b0e6731c000

def z1071 : W := mkw 0xc00b12d240000000 0x4c00b12d24000000 0xbeeeb3e670000000 0x1beeeb3e67000000

def z1072 : W := mkw 0x0e8000201ff1ffba 0x00e8000201ff1ffb 0x000000000ff3ffff 0xe000000000ff3fff

def z1073 : W := mkw 0x4500106241049041 0x0450010624104904 0xb0b2b0e6734c80c0 0x5b0b2b0e6734c80c

def z1074 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000031c99c5 0x000100000031c99c

def z1075 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xffef4ff98fb3ff3f 0xfffef4ff98fb3ff3

def z1076 : W := mkw 0x480ff9474eea000c 0x7480ff9474eea000 0xffffffe7ffff0003 0xfffffffe7ffff000

def z1077 : W := mkw 0xf02b17dfe0000000 0x4f02b17dfe000000 0xffefb3fff0000000 0x1ffefb3fff000000

def z1078 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf7ef43f98f80fe0d 0xff7ef43f98f80fe0

def z1079 : W := mkw 0x080b28000eea000c 0x5080b28000eea000 0x0bdf3c000fff0003 0xe0bdf3c000fff000

def z1080 : W := mkw 0x6000144ae0000000 0x06000144ae000000 0xbee2fce7f0000000 0x1bee2fce7f000000

def z1081 : W := mkw 0x0500002011149941 0x0050000201114994 0x0000000000001800 0x0000000000000180

def z1082 : W := mkw 0xf02ffedae0000000 0x7f02ffedae000000 0x8aafbcf870000000 0x08aafbcf87000000

def z1083 : W := mkw 0xf02ffedae0000000 0x7f02ffedae000000 0xbfeffcfe70000000 0x1bfeffcfe7000000

def z1084 : W := mkw 0x050000201114dd41 0x0050000201114dd4 0x000000000000ffcc 0x0000000000000ffc

def z1085 : W := mkw 0x4000104240000000 0x0400010424000000 0xffe2f0e7f020013e 0xbffe2f0e7f020013

def z1086 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0400002 0x7ffeffffff040000

def z1087 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75ccc3078c60e1f2 0x575ccc3078c60e1f

def z1088 : W := mkw 0xf02fffdfea804408 0x7f02fffdfea80440 0xffeffffff0800600 0x1ffeffffff080060

def z1089 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x5fdffc000fff000f 0xe5fdffc000fff000

def z1090 : W := mkw 0xc00b12d240000000 0x4c00b12d24000000 0xffefb3fe7c40e1ce 0xfffefb3fe7c40e1c

def z1091 : W := mkw 0x080b28000eea000c 0x5080b28000eea000 0x0a133c000fbf0001 0x80a133c000fbf000

def z1092 : W := mkw 0x782ffd4feeea000c 0x7782ffd4feeea000 0xbffffce7ffff0003 0xfbffffce7ffff000

def z1093 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x3ed3bc0603df81c7 0x73ed3bc0603df81c

def z1094 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x0e13fc0783ff01f3 0x10e13fc0783ff01f

def z1095 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2b0e6735c98c1 0x5bef2b0e6735c98c

def z1096 : W := mkw 0xf0a017dfe0010210 0x0f0a017dfe001021 0xf02003fff0000638 0x1f02003fff000063

def z1097 : W := mkw 0xf02b3edaea8a000c 0x5f02b3edaea8a000 0xdf737cf9f3bf0003 0xbdf737cf9f3bf000

def z1098 : W := mkw 0x0500002011149941 0x0050000201114994 0x92500000035c99c7 0x692500000035c99c

def z1099 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xcf414c19f0b31e3b 0xacf414c19f0b31e3

def z1100 : W := mkw 0x0804e800046a0004 0x30804e800046a000 0x0c10fc00037f0003 0x60c10fc00037f000

def z1101 : W := mkw 0x02000105000020a2 0x002000105000020a 0x75cc83078c40e1fe 0xf75cc83078c40e1f

def z1102 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x3fdffc000fff8007 0xe3fdffc000fff800

def z1103 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf41cc1ff0f31fff 0xbdf41cc1ff0f31ff

def z1104 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x8f637cf870000000 0x08f637cf87000000

def z1105 : W := mkw 0xf82fffdfe4600000 0x7f82fffdfe460000 0xffeffffffc6081c6 0xfffeffffffc6081c

def z1106 : W := mkw 0x4500106251149941 0x0450010625114994 0xbffeb0e67f5c99c7 0xfbffeb0e67f5c99c

def z1107 : W := mkw 0x4000104240000000 0x0400010424000000 0xb4e080e670000000 0x1b4e080e67000000

def z1108 : W := mkw 0x4500106251149941 0x0450010625114994 0xb2f2b0e6734c99c5 0x7b2f2b0e6734c99c

def z1109 : W := mkw 0xf02fffdfea800008 0x7f02fffdfea80000 0xffefffffff801e0d 0xfffefffffff801e0

def z1110 : W := mkw 0xf02fffdfea804408 0x7f02fffdfea80440 0xffeffffffc807e0d 0xbffeffffffc807e0

def z1111 : W := mkw 0x0f04c1251ff4fdeb 0x20f04c1251ff4fde 0x75dcc3078ffcffff 0xf75dcc3078ffcfff

def z1112 : W := mkw 0xf82fffdfe46a0004 0x7f82fffdfe46a000 0xfffffffff37f0003 0x7fffffffff37f000

def z1113 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x3fdffc078fff81f7 0xf3fdffc078fff81f

def z1114 : W := mkw 0xfa24d7dfe46020a2 0x2fa24d7dfe46020a 0xffeef3fffc60e1fe 0xfffeef3fffc60e1f

def z1115 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc20e03c 0xfffeffffffc20e03

def z1116 : W := mkw 0x850b02b01b94dd49 0x4850b02b01b94dd4 0x411d03180fdcffcf 0xe411d03180fdcffc

def z1117 : W := mkw 0x4004d04240000000 0x24004d0424000000 0xbfeef0e670000000 0x1bfeef0e67000000

def z1118 : W := mkw 0xc00b12d240000000 0x4c00b12d24000000 0xfbef33f870000000 0x0fbef33f87000000

def z1119 : W := mkw 0x0f0000201574b9e3 0x00f0000201574b9e 0x00100000037c99f7 0x600100000037c99f

def z1120 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x7fdfff078fff603b 0xf7fdfff078fff603

def z1121 : W := mkw 0x480ff8424eea000c 0x7480ff8424eea000 0x8ffffce07fff0003 0xe8ffffce07fff000

def z1122 : W := mkw 0x0a0fe8000eea20ae 0x70a0fe8000eea20a 0x7fdfff000fffe1ff 0xe7fdfff000fffe1f

def z1123 : W := mkw 0xf02fffdfea800008 0x7f02fffdfea80000 0xffefffffff80e00d 0xfffefffffff80e00

def z1124 : W := mkw 0xf22fffdfe00020a2 0x7f22fffdfe00020a 0xffeffffff000e0c0 0x1ffeffffff000e0c

def z1125 : W := mkw 0x0580002011159b51 0x00580002011159b5 0x00100000037f99f7 0x600100000037f99f

def z1126 : W := mkw 0x02000105000020a2 0x002000105000020a 0x710c03078c00e1fc 0x9710c03078c00e1f

def z1127 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x7fdfff078fffe0c3 0xf7fdfff078fffe0c

def z1128 : W := mkw 0x4a04d147446020a2 0x24a04d147446020a 0xfffef3e7ff7ce1ff 0xffffef3e7ff7ce1f

def z1129 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf36103fff0801e0d 0xbf36103fff0801e0

def z1130 : W := mkw 0x0c8000201ffbdf1c 0x00c8000201ffbdf1 0x001000000fffff3f 0xe001000000fffff3

def z1131 : W := mkw 0x7024fd4fe0000000 0x37024fd4fe000000 0xffe3fcfff0000000 0x1ffe3fcfff000000

def z1132 : W := mkw 0xf02fffdfea8a000c 0x7f02fffdfea8a000 0xfffffffff3bf0003 0xbfffffffff3bf000

def z1133 : W := mkw 0x4004d14740000000 0x24004d1474000000 0xbeeeb3e670000000 0x1beeeb3e67000000

def z1134 : W := mkw 0x0580002011159b51 0x00580002011159b5 0x00100000039f1e01 0x000100000039f1e0

def z1135 : W := mkw 0xfa2fffdfeeea20ae 0x7fa2fffdfeeea20a 0xffffffffffffe0c3 0xfffffffffffffe0c

def z1136 : W := mkw 0x0d0fe8201ffe994d 0x70d0fe8201ffe994 0x0fdffc000fff1803 0xe0fdffc000fff180

def z1137 : W := mkw 0xf22fffdfe00020a2 0x7f22fffdfe00020a 0xffeffffff00001f0 0x1ffeffffff00001f

def z1138 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0x8ffffcffffff0003 0xf8ffffcffffff000

def z1139 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xafeffffe70000000 0x0afeffffe7000000

def z1140 : W := mkw 0x0f04c1251574b9e3 0x20f04c1251574b9e 0x7fdef3078f7cf9ff 0xf7fdef3078f7cf9f

def z1141 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf02003fff0001e0c 0x1f02003fff0001e0

def z1142 : W := mkw 0x880fea900eea440c 0x7880fea900eea440 0xfffffff80fff660b 0xefffffff80fff660

def z1143 : W := mkw 0x8e0fc3b50fe0f4aa 0x68e0fc3b50fe0f4a 0x8623c0ff83e01ff3 0x18623c0ff83e01ff

def z1144 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xcb237cf9f0000000 0x0cb237cf9f000000

def z1145 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0800608 0x9ffeffffff080060

def z1146 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x8ef3bcf8735c0003 0x68ef3bcf8735c000

def z1147 : W := mkw 0x4500106251149941 0x0450010625114994 0xfff2f0e7f35c99c7 0x7fff2f0e7f35c99c

def z1148 : W := mkw 0x7a24fd4fe46020a2 0x37a24fd4fe46020a 0xffeeffe7fc60e1fe 0xfffeeffe7fc60e1f

def z1149 : W := mkw 0xf024ffdfe0000000 0x3f024ffdfe000000 0xff61fffff0000000 0x1ff61fffff000000

def z1150 : W := mkw 0x880fea900eea440c 0x7880fea900eea440 0x7fdfff180fffe60f 0xe7fdfff180fffe60

def z1151 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf414c19f0f39fff 0xfdf414c19f0f39ff

def z1152 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0x7deeffe7fc60e1fe 0xf7deeffe7fc60e1f

def z1153 : W := mkw 0x000028000a8a000c 0x1000028000a8a000 0x08103c00039f0001 0x008103c00039f000

def z1154 : W := mkw 0xd82ffbd74eea000c 0x7d82ffbd74eea000 0xbfffffe67fff0003 0xfbfffffe67fff000

def z1155 : W := mkw 0xf02016dae0000000 0x0f02016dae000000 0x8a2230f870000000 0x08a2230f87000000

def z1156 : W := mkw 0x982feb950eea000c 0x7982feb950eea000 0x0fdfff000fff0003 0xe0fdfff000fff000

def z1157 : W := mkw 0x4500106251149941 0x0450010625114994 0xfef2b0fe735c9fcf 0x7fef2b0fe735c9fc

def z1158 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xde014c19f0b31f3f 0x1de014c19f0b31f3

def z1159 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0xffcdcf1f8cf3ffff 0xfffcdcf1f8cf3fff

def z1160 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffffffffff7ce1ff 0xfffffffffff7ce1f

def z1161 : W := mkw 0x0500002011149941 0x0050000201114994 0xd351001803dc9fcf 0xed351001803dc9fc

def z1162 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf02003fff000013c 0x1f02003fff000013

def z1163 : W := mkw 0x0580002011159b51 0x00580002011159b5 0x0010000003bf1f3f 0xa0010000003bf1f3

def z1164 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a133c00039f0001 0x00a133c00039f000

def z1165 : W := mkw 0x0a04e905046a20a6 0x30a04e905046a20a 0x75dcf3078c6ce1fe 0xf75dcf3078c6ce1f

def z1166 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xaabfbffe7fdf0001 0x4aabfbffe7fdf000

def z1167 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0a01f3f 0xbffeffffff0a01f3

def z1168 : W := mkw 0x480ff8424eea000c 0x7480ff8424eea000 0xbefeb0e67f4c0000 0x5befeb0e67f4c000

def z1169 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xfc204ffff0000000 0x1fc204ffff000000

def z1170 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf36d03f80c80fe0d 0xaf36d03f80c80fe0

def z1171 : W := mkw 0x0a04e905046a20a6 0x30a04e905046a20a 0x75cccf078c63e1fe 0xf75cccf078c63e1f

def z1172 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffce0ffff 0xfffeffffffce0fff

def z1173 : W := mkw 0x048000201111df10 0x0048000201111df1 0x0000000000b3ff3f 0xa0000000000b3ff3

def z1174 : W := mkw 0xf02fffdfea800008 0x7f02fffdfea80000 0xffeffffffc800000 0x9ffeffffffc80000

def z1175 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0930001 0x1ffeffffff093000

def z1176 : W := mkw 0x702ffd4fe0000000 0x7702ffd4fe000000 0xbfeffce7f0000000 0x1bfeffce7f000000

def z1177 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x8f637cf870b30003 0xa8f637cf870b3000

def z1178 : W := mkw 0x4804d14744600000 0x24804d1474460000 0xfffef3e7ff7c0003 0xffffef3e7ff7c000

def z1179 : W := mkw 0xf02b17dfe0000000 0x4f02b17dfe000000 0xf22303fff0000000 0x1f22303fff000000

def z1180 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xf02c03fff0000000 0x1f02c03fff000000

def z1181 : W := mkw 0xf82fffdfe4600000 0x7f82fffdfe460000 0xffeffffff0600002 0x1ffeffffff060000

def z1182 : W := mkw 0x0a04e905046a20a6 0x30a04e905046a20a 0x7fddff078cffe1ff 0xf7fddff078cffe1f

def z1183 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xdf63fcfff0000000 0x1df63fcfff000000

def z1184 : W := mkw 0xf0afffdfea814618 0x7f0afffdfea81461 0xffeffffffca36638 0x9ffeffffffca3663

def z1185 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xc02003f9f0000000 0x0c02003f9f000000

def z1186 : W := mkw 0x0500002011149941 0x0050000201114994 0x0a123000031c1801 0x00a123000031c180

def z1187 : W := mkw 0x7024fd4fe0000000 0x37024fd4fe000000 0xbc20fce7f0000000 0x1bc20fce7f000000

def z1188 : W := mkw 0x00002800000a0004 0x100002800000a000 0x0ed2bc00035f0003 0x60ed2bc00035f000

def z1189 : W := mkw 0xaa0fc79da46020a2 0x6aa0fc79da46020a 0xffefcffffc60e1fe 0xfffefcffffc60e1f

def z1190 : W := mkw 0x0500002011149941 0x0050000201114994 0x71dc03000f5cf9cf 0xe71dc03000f5cf9c

def z1191 : W := mkw 0xf8afffdfeeeb021c 0x7f8afffdfeeeb021 0xffffffffffff063b 0xfffffffffffff063

def z1192 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x9fdffc007fff0003 0xf9fdffc007fff000

def z1193 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03f80f00fe0c 0x4f3ef03f80f00fe0

def z1194 : W := mkw 0xd82ffbd74eea000c 0x7d82ffbd74eea000 0xbefeb3e67f5c0003 0x7befeb3e67f5c000

def z1195 : W := mkw 0xfa2fffdfeeea20ae 0x7fa2fffdfeeea20a 0xffffffffff6ce1fe 0xfffffffffff6ce1f

def z1196 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03f80f807e09 0x8f3ef03f80f807e0

def z1197 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffffc00e000 0x5ffeffffffc00e00

def z1198 : W := mkw 0x20000408a0000000 0x020000408a000000 0xffe34cf9f0000000 0x1ffe34cf9f000000

def z1199 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000031c1907 0x200100000031c190

def z1200 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xbeeeffe7f0000000 0x1beeeffe7f000000

def z1201 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0800001 0xbffeffffff080000

def z1202 : W := mkw 0xfa24d7dfe46020a2 0x2fa24d7dfe46020a 0xf0ac83fffc40e0c0 0x5f0ac83fffc40e0c

def z1203 : W := mkw 0x080fe9050eea000c 0x7080fe9050eea000 0x7fdfff078fffe00f 0xf7fdfff078fffe00

def z1204 : W := mkw 0xe58b16fafb95df59 0x4e58b16fafb95df5 0x8a333cf8739f1e01 0x08a333cf8739f1e0

def z1205 : W := mkw 0x050000201b9e994d 0x0050000201b9e994 0x00100000039f1801 0x000100000039f180

def z1206 : W := mkw 0xfa2017dfe46020a2 0x0fa2017dfe46020a 0xf02003fffc60e1fe 0xff02003fffc60e1f

def z1207 : W := mkw 0xf02fffdfea8a000c 0x7f02fffdfea8a000 0xffeffffff0830000 0x1ffeffffff083000

def z1208 : W := mkw 0x4000104240000000 0x0400010424000000 0xbae230e070000000 0x0bae230e07000000

def z1209 : W := mkw 0x080fe800046a0004 0x7080fe800046a000 0x0fdffc00037f0003 0x60fdffc00037f000

def z1210 : W := mkw 0x0500002011149941 0x0050000201114994 0x00000000004099c6 0x600000000004099c

def z1211 : W := mkw 0xf02b3edaea800008 0x5f02b3edaea80000 0x8bef3cf87f800001 0xe8bef3cf87f80000

def z1212 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0100003 0x3ffeffffff010000

def z1213 : W := mkw 0xf02b3fdfe0000000 0x5f02b3fdfe000000 0x8a233cfff0000000 0x18a233cfff000000

def z1214 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x4fdffc018fff003b 0xe4fdffc018fff003

def z1215 : W := mkw 0xf824d7dfe4600000 0x2f824d7dfe460000 0xf5ecc3fffc600002 0xff5ecc3fffc60000

def z1216 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf02c03f80c00fe0c 0x0f02c03f80c00fe0

def z1217 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75ccc3078ce0ffff 0xf75ccc3078ce0fff

def z1218 : W := mkw 0xf0afffdfe0010210 0x7f0afffdfe001021 0xffeffffff0830600 0x1ffeffffff083060

def z1219 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x8f414c19f0b31f33 0xb8f414c19f0b31f3

def z1220 : W := mkw 0x048000201b91df18 0x0048000201b91df1 0x0000000003b31f3f 0xa0000000003b31f3

def z1221 : W := mkw 0x0a000105046020a2 0x00a000105046020a 0x71cc03078c60e1fe 0xf71cc03078c60e1f

def z1222 : W := mkw 0xc00b12d24a800008 0x4c00b12d24a80000 0xffffb3fe7fdc0003 0xfffffb3fe7fdc000

def z1223 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0bdf7c000fbf0001 0xe0bdf7c000fbf000

def z1224 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xffffb3fe0fdcffcf 0xfffffb3fe0fdcffc

def z1225 : W := mkw 0x4500106251149941 0x0450010625114994 0x28b2b0e6735c80c0 0x428b2b0e6735c80c

def z1226 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x248cc3078c60e1fe 0xf248cc3078c60e1f

def z1227 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x5f537c0183bf013f 0xb5f537c0183bf013

def z1228 : W := mkw 0x040000201b90dd08 0x0040000201b90dd0 0x000000000f90ff0f 0xe000000000f90ff0

def z1229 : W := mkw 0x0000000000000000 0x0000000000000000 0x75ccc3078c60e1fe 0xf75ccc3078c60e1f

def z1230 : W := mkw 0x0d0000201ffe994d 0x00d0000201ffe994 0x001000000fff1803 0xe001000000fff180

def z1231 : W := mkw 0xf02ffedae0000000 0x7f02ffedae000000 0x8b2f7cf870000000 0x08b2f7cf87000000

def z1232 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xdb633cf870000000 0x0db633cf87000000

def z1233 : W := mkw 0x880fea900eea000c 0x7880fea900eea000 0x2fffffe00fff0003 0xe2fffffe00fff000

def z1234 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffffc40e1ce 0xfffeffffffc40e1c

def z1235 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x8a237cf9f0000000 0x08a237cf9f000000

def z1236 : W := mkw 0xf02b3fdfe0000000 0x5f02b3fdfe000000 0xfbef3ffff0000000 0x1fbef3ffff000000

def z1237 : W := mkw 0xf02b3edaea8a000c 0x5f02b3edaea8a000 0x8a333cf8730c0000 0x08a333cf8730c000

def z1238 : W := mkw 0x0500002011149941 0x0050000201114994 0x0c10b000035c99c7 0x60c10b000035c99c

def z1239 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffffffe00f 0xfffffffffffffe00

def z1240 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xa0ae03f80f00fe00 0x4a0ae03f80f00fe0

def z1241 : W := mkw 0x4500106251149941 0x0450010625114994 0xaef2b0e6735c98c3 0x6aef2b0e6735c98c

def z1242 : W := mkw 0x4580106251159b51 0x04580106251159b5 0xbef2b0e6737f99f7 0x7bef2b0e6737f99f

def z1243 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdfc34c19f3b31f3f 0xfdfc34c19f3b31f3

def z1244 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc40e1fc 0x5ffeffffffc40e1f

def z1245 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xfffffff80ffffe0f 0xefffffff80ffffe0

def z1246 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x7fdfff060fffe0cf 0xe7fdfff060fffe0c

def z1247 : W := mkw 0x050fe82011149941 0x7050fe8201114994 0x0fdffc00035c99c7 0x60fdffc00035c99c

def z1248 : W := mkw 0xa00b0698a0000000 0x4a00b0698a000000 0xfbef0ff870000000 0x0fbef0ff87000000

def z1249 : W := mkw 0xc00ffad240000000 0x7c00ffad24000000 0xffeffffe70000000 0x1ffeffffe7000000

def z1250 : W := mkw 0x0204c105000020a2 0x20204c105000020a 0x75ccc3078c00e1fc 0xf75ccc3078c00e1f

def z1251 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfbef7ff9f0000000 0x0fbef7ff9f000000

def z1252 : W := mkw 0x7824fd4fe46a0004 0x37824fd4fe46a000 0xbef2fce7f37f0003 0x7bef2fce7f37f000

def z1253 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xaeaffffff0000000 0x1aeaffffff000000

def z1254 : W := mkw 0x080fe9050eea000c 0x7080fe9050eea000 0x4fdfff018fff0003 0xe4fdfff018fff000

def z1255 : W := mkw 0x0804e8000eea000c 0x30804e8000eea000 0x0f51fc000fff0003 0xe0f51fc000fff000

def z1256 : W := mkw 0x0804e8000eea000c 0x30804e8000eea000 0x0c10fc000f7f0002 0x40c10fc000f7f000

def z1257 : W := mkw 0x0580002011159b51 0x00580002011159b5 0x0010000003df9fc7 0x60010000003df9fc

def z1258 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc000fbf0001 0x80fdffc000fbf000

def z1259 : W := mkw 0x800b029000000000 0x4800b02900000000 0xf3ef03f80c80fe0d 0xef3ef03f80c80fe0

def z1260 : W := mkw 0x6000144ae0000000 0x06000144ae000000 0xfee2b0fff0000000 0x1fee2b0fff000000

def z1261 : W := mkw 0x4000104240000000 0x0400010424000000 0xbef2b0e6705c0002 0x1bef2b0e6705c000

def z1262 : W := mkw 0x0d04e820157e9945 0x30d04e820157e994 0x0c10fc00037f99c7 0x60c10fc00037f99c

def z1263 : W := mkw 0x0500002011149941 0x0050000201114994 0x001000000f5cf9cf 0xe001000000f5cf9c

def z1264 : W := mkw 0x0f0000201ffeb9ef 0x00f0000201ffeb9e 0x001000000ffff9ff 0xe001000000ffff9f

def z1265 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf1ed03f80c80fe0c 0xef1ed03f80c80fe0

def z1266 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x8a014c19f0b31e31 0x08a014c19f0b31e3

def z1267 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2fce6737f99c7 0x7bef2fce6737f99c

def z1268 : W := mkw 0xf02ffedae0000000 0x7f02ffedae000000 0x8e23fcf870000000 0x08e23fcf87000000

def z1269 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xd36f03f80f807e0d 0xad36f03f80f807e0

def z1270 : W := mkw 0xf02fffdfea8a000c 0x7f02fffdfea8a000 0xffffffffff9f0001 0xfffffffffff9f000

def z1271 : W := mkw 0xf02b3edaea804408 0x5f02b3edaea80440 0x8a233cf870800600 0x08a233cf87080060

def z1272 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0ed3fc0003ff0003 0x60ed3fc0003ff000

def z1273 : W := mkw 0x020b29050a8a20ae 0x5020b29050a8a20a 0x7a133f07839fe1fd 0x17a133f07839fe1f

def z1274 : W := mkw 0x4500106251149941 0x0450010625114994 0xfef2b0e7f35c99ff 0x7fef2b0e7f35c99f

def z1275 : W := mkw 0x0d0000201ffe994d 0x00d0000201ffe994 0x001000000f5c99c7 0x6001000000f5c99c

def z1276 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0xdb533c18039f1e0d 0xadb533c18039f1e0

def z1277 : W := mkw 0xf02b17dfea804408 0x4f02b17dfea80440 0xf12d03fffc806608 0x9f12d03fffc80660

def z1278 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x74cc83078c40e1fe 0x774cc83078c40e1f

def z1279 : W := mkw 0x7024fd4fe0000000 0x37024fd4fe000000 0xffeeffe7f0000000 0x1ffeeffe7f000000

def z1280 : W := mkw 0x4000104240000000 0x0400010424000000 0xbee2b0e670100003 0x3bee2b0e67010000

def z1281 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xbae33cf870000000 0x0bae33cf87000000

def z1282 : W := mkw 0x02000105000020a2 0x002000105000020a 0x75cc43078c20e1fe 0xf75cc43078c20e1f

def z1283 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2b0e6735c81c2 0x5bef2b0e6735c81c

def z1284 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2f0e7f37c99f7 0x7bef2f0e7f37c99f

def z1285 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0xffdfff180ffffe0f 0xeffdfff180ffffe0

def z1286 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0ed3bc00039f0001 0x00ed3bc00039f000

def z1287 : W := mkw 0x050000201b94dd49 0x0050000201b94dd4 0x001000000f9cfe0d 0xe001000000f9cfe0

def z1288 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0a133c0003bf0003 0xa0a133c0003bf000

def z1289 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xfffffffffcff0002 0x9fffffffffcff000

def z1290 : W := mkw 0x4580106251159b51 0x04580106251159b5 0xfff3b0fe73ff9fff 0xffff3b0fe73ff9ff

def z1291 : W := mkw 0x4000104240000000 0x0400010424000000 0xbee2b0e6700081c4 0x1bee2b0e6700081c

def z1292 : W := mkw 0x880fea900eea000c 0x7880fea900eea000 0x8ffffcf80fff0003 0xe8ffffcf80fff000

def z1293 : W := mkw 0xda2ffbd7446020a2 0x7da2ffbd7446020a 0xffeef3e7fc60e1fe 0xfffeef3e7fc60e1f

def z1294 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xffc1cc1ff0b31f3f 0xbffc1cc1ff0b31f3

def z1295 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdfcd4c19fcb31f3f 0xfdfcd4c19fcb31f3

def z1296 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x718cc3078c60e1fc 0xd718cc3078c60e1f

def z1297 : W := mkw 0x4500106251149941 0x0450010625114994 0xbefeb3e67f5cf9c7 0x7befeb3e67f5cf9c

def z1298 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03f80fb3fe0f 0xef3ef03f80fb3fe0

def z1299 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xa2af03f80f80fe0d 0xea2af03f80f80fe0

def z1300 : W := mkw 0xf024ffdfe0000000 0x3f024ffdfe000000 0xfee2fffff0000000 0x1fee2fffff000000

def z1301 : W := mkw 0x0804e8000eea000c 0x30804e8000eea000 0x0c10fc0003ff0003 0x00c10fc0003ff000

def z1302 : W := mkw 0x0a04e9050eea20ae 0x30a04e9050eea20a 0x7ddcff078fffe1ff 0xf7ddcff078fffe1f

def z1303 : W := mkw 0x7424fd6feb80d408 0x37424fd6feb80d40 0x0c00fc07ff80fe0d 0xf0c00fc07ff80fe0

def z1304 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffcf3e1ff 0xfffeffffffcf3e1f

def z1305 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xf5edcffff0000000 0x1f5edcffff000000

def z1306 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0a30000 0x9ffeffffff0a3000

def z1307 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xffef4ff80f80fe0d 0xeffef4ff80f80fe0

def z1308 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffffc80fe0d 0xfffeffffffc80fe0

def z1309 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xffe34cf9f0b31f3f 0xbffe34cf9f0b31f3

def z1310 : W := mkw 0xf82fffdfeeea440c 0x7f82fffdfeeea440 0xffeffffffca36608 0x9ffeffffffca3660

def z1311 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0000106 0x3ffeffffff000010

def z1312 : W := mkw 0x4500106251149941 0x0450010625114994 0xfff3fcfe73ff9fcf 0xffff3fcfe73ff9fc

def z1313 : W := mkw 0xf82fffdfe46a0004 0x7f82fffdfe46a000 0xfffffffff0ff0003 0xbfffffffff0ff000

def z1314 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf02003fff00081c4 0x1f02003fff00081c

def z1315 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0330002 0x1ffeffffff033000

def z1316 : W := mkw 0x0500002011149941 0x0050000201114994 0x3ed2b006035c99c7 0x73ed2b006035c99c

def z1317 : W := mkw 0xa00b0698a0000000 0x4a00b0698a000000 0xffef4ff9fc20e13e 0xfffef4ff9fc20e13

def z1318 : W := mkw 0x880fea900eea440c 0x7880fea900eea440 0x0fdfff000fff6003 0xe0fdfff000fff600

def z1319 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff04080c0 0x5ffeffffff04080c

def z1320 : W := mkw 0xf0ab3edae0010210 0x5f0ab3edae001021 0xcb237cf9f0a30638 0x8cb237cf9f0a3063

def z1321 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x450cc3078c60e1fe 0xf450cc3078c60e1f

def z1322 : W := mkw 0x050000201b9e994d 0x0050000201b9e994 0x0010000003df99c7 0x60010000003df99c

def z1323 : W := mkw 0xf82b3edaeeea000c 0x5f82b3edaeeea000 0x8a333cf87fff0003 0xe8a333cf87fff000

def z1324 : W := mkw 0x4500106251149941 0x0450010625114994 0xfff3f0fff3fc9fff 0xffff3f0fff3fc9ff

def z1325 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0a1f3c000f9f0001 0x00a1f3c000f9f000

def z1326 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf1ec03fffc00e00c 0xff1ec03fffc00e00

def z1327 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0f5f7c000fbf0003 0xa0f5f7c000fbf000

def z1328 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc018fff0133 0xf0fdffc018fff013

def z1329 : W := mkw 0xfa2fffdfeeea20ae 0x7fa2fffdfeeea20a 0xffeffffffca36038 0x9ffeffffffca3603

def z1330 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x7dcccf078c73e1fe 0xf7dcccf078c73e1f

def z1331 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdb414c19f0b31e3d 0xadb414c19f0b31e3

def z1332 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0200002 0xbffeffffff020000

def z1333 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x8a233cf870930001 0x08a233cf87093000

def z1334 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xffefb3f80f80fe0d 0xeffefb3f80f80fe0

def z1335 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xcf2ffffff0000000 0x1cf2ffffff000000

def z1336 : W := mkw 0xfaafffdfe46122b2 0x7faafffdfe46122b 0xffeffffffce3e7fe 0xfffeffffffce3e7f

def z1337 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfeeeb3fff0000000 0x1feeeb3fff000000

def z1338 : W := mkw 0x4500106251149941 0x0450010625114994 0xbff3b0e673dc99c7 0xfbff3b0e673dc99c

def z1339 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0a133c000f9f0001 0xe0a133c000f9f000

def z1340 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc60e0c2 0xfffeffffffc60e0c

def z1341 : W := mkw 0xda2ffbd7446020a2 0x7da2ffbd7446020a 0xbeeeb3e67c40e1c6 0x7beeeb3e67c40e1c

def z1342 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xaaafbffe7c40e0c0 0x4aaafbffe7c40e0c

def z1343 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xcf014c19f0b31f3b 0x9cf014c19f0b31f3

def z1344 : W := mkw 0x6000144ae0000000 0x06000144ae000000 0xffe3fcfff06081fe 0xfffe3fcfff06081f

def z1345 : W := mkw 0x800b2a900a8a440c 0x5800b2a900a8a440 0x0a133c18039f0601 0x00a133c18039f060

def z1346 : W := mkw 0xf22017dfe00020a2 0x0f22017dfe00020a 0xff614ffff020e1fe 0xbff614ffff020e1f

def z1347 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffff0200030 0x1ffeffffff020003

def z1348 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000035c19c3 0x000100000035c19c

def z1349 : W := mkw 0x0000000000000000 0x0000000000000000 0x0ed2fc00037f0003 0x60ed2fc00037f000

def z1350 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x7fdfff018fffe03f 0xe7fdfff018fffe03

def z1351 : W := mkw 0x400ff94740000000 0x7400ff9474000000 0xffefffe7f0000000 0x1ffefffe7f000000

def z1352 : W := mkw 0x0500002011149941 0x0050000201114994 0x04108006035c99c7 0x704108006035c99c

def z1353 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x658cc3078c60e1fa 0xd658cc3078c60e1f

def z1354 : W := mkw 0xf02fffdfea800008 0x7f02fffdfea80000 0xffeffffff3800001 0x1ffeffffff380000

def z1355 : W := mkw 0xf02b3fdfe0000000 0x5f02b3fdfe000000 0xf02233fff0000000 0x1f02233fff000000

def z1356 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf0a2b3fff0000000 0x1f0a2b3fff000000

def z1357 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x7fcdcf078c60e1fe 0xf7fcdcf078c60e1f

def z1358 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc6001f2 0xfffeffffffc6001f

def z1359 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xbee3bcfe704081c6 0x7bee3bcfe704081c

def z1360 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0001e0c 0x1ffeffffff0001e0

def z1361 : W := mkw 0x0a0fe8000eea20ae 0x70a0fe8000eea20a 0x0fdffc000fff01f3 0xe0fdffc000fff01f

def z1362 : W := mkw 0xc00b12d24a804408 0x4c00b12d24a80440 0xffefb3fe7c806608 0x9ffefb3fe7c80660

def z1363 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc000fffe00f 0xe0fdffc000fffe00

def z1364 : W := mkw 0xfa2fd7dfe46020a2 0x6fa2fd7dfe46020a 0xf7efc3fffc60e1fe 0xff7efc3fffc60e1f

def z1365 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffefffffffa30001 0xfffefffffffa3000

def z1366 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x2c9eff078f7fe1f2 0x52c9eff078f7fe1f

def z1367 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xc3ef03f80f807e09 0xec3ef03f80f807e0

def z1368 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xffcdcf1ffcf3ffff 0xfffcdcf1ffcf3fff

def z1369 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf56043fff0000000 0x1f56043fff000000

def z1370 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x8e23bcfe70000000 0x18e23bcfe7000000

def z1371 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xd5414c19f0a31f3e 0xbd5414c19f0a31f3

def z1372 : W := mkw 0xf02fffdfea804408 0x7f02fffdfea80440 0xffefffffff806609 0xfffefffffff80660

def z1373 : W := mkw 0xf02b3edaea8a000c 0x5f02b3edaea8a000 0x8a233cf870830000 0x08a233cf87083000

def z1374 : W := mkw 0x050000201b94dd49 0x0050000201b94dd4 0x00100000039c1e01 0x000100000039c1e0

def z1375 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0f537c00039f0001 0x00f537c00039f000

def z1376 : W := mkw 0x4000104240000000 0x0400010424000000 0xb4e080e6704081c6 0x7b4e080e6704081c

def z1377 : W := mkw 0x048000201111df10 0x0048000201111df1 0x000000000000ff3c 0x0000000000000ff3

def z1378 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0a9f3c000f9f0001 0x40a9f3c000f9f000

def z1379 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0x2caeffe7fc60e1f2 0x52caeffe7fc60e1f

def z1380 : W := mkw 0xf0ab3edae0010210 0x5f0ab3edae001021 0x8a233cf870830600 0x08a233cf87083060

def z1381 : W := mkw 0x000fe8000a8a000c 0x7000fe8000a8a000 0x0b1f7c00039f0001 0x00b1f7c00039f000

def z1382 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf4d4f19fcb37f3f 0xbdf4d4f19fcb37f3

def z1383 : W := mkw 0xf02fffdfe00a0004 0x7f02fffdfe00a000 0xfffffffff01f0000 0x1fffffffff01f000

def z1384 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xcb2f7ff9fc206038 0x8cb2f7ff9fc20603

def z1385 : W := mkw 0x070001251114b9e3 0x0070001251114b9e 0x700003078000f9fc 0x1700003078000f9f

def z1386 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xffefbffe70000000 0x1ffefbffe7000000

def z1387 : W := mkw 0x4500106251149941 0x0450010625114994 0xfffef3e7ff7cf9ff 0xffffef3e7ff7cf9f

def z1388 : W := mkw 0xf02b3fdfe0000000 0x5f02b3fdfe000000 0xfee3bffff0000000 0x1fee3bffff000000

def z1389 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfbefbffe70000000 0x0fbefbffe7000000

def z1390 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000005c99c6 0x000100000005c99c

def z1391 : W := mkw 0x0500002011149941 0x0050000201114994 0x04d08000035c99c7 0x604d08000035c99c

def z1392 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffffff81c7 0xfffffffffffff81c

def z1393 : W := mkw 0xf02017dfe0004400 0x0f02017dfe000440 0xf02003fff0006608 0x1f02003fff000660

def z1394 : W := mkw 0x0a0fe8000eea20ae 0x70a0fe8000eea20a 0x0fdffc000fffe0c3 0xe0fdffc000fffe0c

def z1395 : W := mkw 0xf82ffedaeeea000c 0x7f82ffedaeeea000 0xdffffcf9ffff0003 0xfdffffcf9ffff000

def z1396 : W := mkw 0xf02ffedae0000000 0x7f02ffedae000000 0xffeffff870000000 0x0ffeffff87000000

def z1397 : W := mkw 0x050000201b94dd49 0x0050000201b94dd4 0x000000000f80ffcd 0xe000000000f80ffc

def z1398 : W := mkw 0x880fea900eea000c 0x7880fea900eea000 0xfffffff80fff1e0f 0xefffffff80fff1e0

def z1399 : W := mkw 0x0d04c02015749941 0x20d04c0201574994 0x05dcc0000f7c99c7 0xe05dcc0000f7c99c

def z1400 : W := mkw 0x840002b00100d400 0x0840002b00100d40 0xf3ed03f80c80fe0d 0xef3ed03f80c80fe0

def z1401 : W := mkw 0x4580106251159b51 0x04580106251159b5 0xfff2f0e7f3ff9fff 0xffff2f0e7f3ff9ff

def z1402 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0c9efc000fff0003 0xe0c9efc000fff000

def z1403 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x2a9fbf060fdfe0c1 0x42a9fbf060fdfe0c

def z1404 : W := mkw 0x400b104240000000 0x4400b10424000000 0xbfefb0e670000000 0x1bfefb0e67000000

def z1405 : W := mkw 0xf02b3edaea8a000c 0x5f02b3edaea8a000 0xbef3bcfe73df0003 0x7bef3bcfe73df000

def z1406 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf7ef83fe0f80fe0d 0xff7ef83fe0f80fe0

def z1407 : W := mkw 0xa48b06b8bb91df18 0x4a48b06b8bb91df1 0x410d4f198fb3ff3f 0xe410d4f198fb3ff3

def z1408 : W := mkw 0x4500106251149941 0x0450010625114994 0xb4f2b0e6734c99c6 0x7b4f2b0e6734c99c

def z1409 : W := mkw 0xb02fef9da0000000 0x7b02fef9da000000 0xffef4ff9f0000000 0x1ffef4ff9f000000

def z1410 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0200038 0x9ffeffffff020003

def z1411 : W := mkw 0x000fe80000000000 0x7000fe8000000000 0x0fdffc0003ff0003 0xe0fdffc0003ff000

def z1412 : W := mkw 0xf22b17dfe00020a2 0x4f22b17dfe00020a 0xf3ef03fffc00e1fc 0xff3ef03fffc00e1f

def z1413 : W := mkw 0xfa2fffdfeeea20ae 0x7fa2fffdfeeea20a 0xffffffffffff01f3 0xfffffffffffff01f

def z1414 : W := mkw 0x0580002011159b51 0x00580002011159b5 0x0fd3fc0003ff9fff 0xe0fd3fc0003ff9ff

def z1415 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0a13bc0003df0001 0x00a13bc0003df000

def z1416 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xff414f19f0b3ff3f 0xbff414f19f0b3ff3

def z1417 : W := mkw 0x080b28000eea000c 0x5080b28000eea000 0x0ed3bc000fff0003 0xe0ed3bc000fff000

def z1418 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0c12fc00037f0002 0x00c12fc00037f000

def z1419 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0f53fc0003ff0003 0xa0f53fc0003ff000

def z1420 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0a9fbc000fff0003 0xe0a9fbc000fff000

def z1421 : W := mkw 0x4000104240000000 0x0400010424000000 0xbfe3fce670b30003 0xbbfe3fce670b3000

def z1422 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xf5edcffffc60e1fe 0xff5edcffffc60e1f

def z1423 : W := mkw 0xc00fd3d740000000 0x6c00fd3d74000000 0xffeff3fff0000000 0x1ffeff3fff000000

def z1424 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffeffffffce30002 0xfffeffffffce3000

def z1425 : W := mkw 0x0d0fe8201ffe994d 0x70d0fe8201ffe994 0x009eb0000f5c99c7 0x6009eb0000f5c99c

def z1426 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0x8e014c19f0b31f3f 0xb8e014c19f0b31f3

def z1427 : W := mkw 0x840b02b00100d400 0x4840b02b00100d40 0xf3ef03f80c00fe0c 0xef3ef03f80c00fe0

def z1428 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xaaaf3ff870000000 0x0aaaf3ff87000000

def z1429 : W := mkw 0x000fe8000a8a000c 0x7000fe8000a8a000 0x0fdffc0003bf0003 0xa0fdffc0003bf000

def z1430 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xc12d4ff9f0000000 0x0c12d4ff9f000000

def z1431 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0x8e33fcfff3ff0003 0x18e33fcfff3ff000

def z1432 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0xbffffce00fff0003 0xebffffce00fff000

def z1433 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0d1dfc000fff0003 0xe0d1dfc000fff000

def z1434 : W := mkw 0x4000114740000000 0x0400011474000000 0xfee2b3e7f0000000 0x1fee2b3e7f000000

def z1435 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75ccc3078c20e1fc 0x975ccc3078c20e1f

def z1436 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xcffffff9ffff0003 0xecffffff9ffff000

def z1437 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf7ef43f80fa0fe0f 0xef7ef43f80fa0fe0

def z1438 : W := mkw 0x0f0000201574b9e3 0x00f0000201574b9e 0x001000000f5cf9c7 0x6001000000f5cf9c

def z1439 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75cdc31f8ce0e7fe 0xf75cdc31f8ce0e7f

def z1440 : W := mkw 0x800b2a900a8a440c 0x5800b2a900a8a440 0x4b1f3f180f9f6609 0x84b1f3f180f9f660

def z1441 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc0003ff0003 0x00fdffc0003ff000

def z1442 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xfa210ffff0000000 0x1fa210ffff000000

def z1443 : W := mkw 0xc00b12d240000000 0x4c00b12d24000000 0xbee3b0fe70000000 0x1bee3b0fe7000000

def z1444 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff04001c2 0x1ffeffffff04001c

def z1445 : W := mkw 0x4000104240000000 0x0400010424000000 0xbee2b0e670001805 0x3bee2b0e67000180

def z1446 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xfffffffff3ff0003 0x1fffffffff3ff000

def z1447 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0a93bc0003df0001 0x40a93bc0003df000

def z1448 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffffc20e13e 0xfffeffffffc20e13

def z1449 : W := mkw 0xf024ffdfe0000000 0x3f024ffdfe000000 0x2c20ffe7f0000000 0x12c20ffe7f000000

def z1450 : W := mkw 0xf02b3edaea8a000c 0x5f02b3edaea8a000 0xfbff3ff87f9f0001 0xefbff3ff87f9f000

def z1451 : W := mkw 0x4500106251149941 0x0450010625114994 0xbef2b0e6734c99c4 0x5bef2b0e6734c99c

def z1452 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x80210cf870000000 0x080210cf87000000

def z1453 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf7efc3ff8fe0ffff 0xff7efc3ff8fe0fff

def z1454 : W := mkw 0xe58016faf115df51 0x0e58016faf115df5 0xf02003fff000fffc 0x1f02003fff000fff

def z1455 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x754c43078c20e1fe 0xb754c43078c20e1f

def z1456 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0fd3fc0003ff0003 0xe0fd3fc0003ff000

def z1457 : W := mkw 0x0f04c1251574b9e3 0x20f04c1251574b9e 0x75ccc3078c60f9fe 0xf75ccc3078c60f9f

def z1458 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x5fdfff018fff613f 0xf5fdfff018fff613

def z1459 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xbeefbffe70000000 0x1beefbffe7000000

def z1460 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xdb633cf870801e0d 0xadb633cf870801e0

def z1461 : W := mkw 0x6000144ae0000000 0x06000144ae000000 0xf02000fff0000000 0x1f02000fff000000

def z1462 : W := mkw 0x0580002011159b51 0x00580002011159b5 0x75d0c00783ff9fff 0xf75d0c00783ff9ff

def z1463 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x0fdffc060fff00c3 0xe0fdffc060fff00c

def z1464 : W := mkw 0x6f84d56ff575bbf3 0x26f84d56ff575bbf 0xf5ecc3fffc60fffe 0xff5ecc3fffc60fff

def z1465 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xda233cf9f0000000 0x1da233cf9f000000

def z1466 : W := mkw 0xfa2fffdfeeea20ae 0x7fa2fffdfeeea20a 0xffffffffffff603b 0xfffffffffffff603

def z1467 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc20e1fc 0x9ffeffffffc20e1f

def z1468 : W := mkw 0x480010424eea000c 0x0480010424eea000 0xbef2b0e67fff0003 0xfbef2b0e67fff000

def z1469 : W := mkw 0x0000000000000000 0x0000000000000000 0x0ed3bc0003df0003 0x60ed3bc0003df000

def z1470 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xfc20b3fff0000000 0x1fc20b3fff000000

def z1471 : W := mkw 0x4500106251149941 0x0450010625114994 0x20b2b0e6734c81c0 0x520b2b0e6734c81c

def z1472 : W := mkw 0xf024d7dfe0000000 0x2f024d7dfe000000 0xf12c43fff0000000 0x1f12c43fff000000

def z1473 : W := mkw 0x0500002011149941 0x0050000201114994 0x0e500000035c99c7 0x60e500000035c99c

def z1474 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xf12d4ffffca30000 0x9f12d4ffffca3000

def z1475 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffffc000000 0xfffeffffffc00000

def z1476 : W := mkw 0xf02016dae0000000 0x0f02016dae000000 0xdf614cf9f0000000 0x1df614cf9f000000

def z1477 : W := mkw 0x050b00201b949949 0x4050b00201b94994 0x03df00000fdc99c7 0xe03df00000fdc99c

def z1478 : W := mkw 0x000fe9050a8a000c 0x7000fe9050a8a000 0x7fdfff07839f0001 0x17fdfff07839f000

def z1479 : W := mkw 0x0580002011159b51 0x00580002011159b5 0x0000000000b39fff 0xa0000000000b39ff

def z1480 : W := mkw 0x880fea900eea440c 0x7880fea900eea440 0xdfdfff180fff7e0f 0xedfdfff180fff7e0

def z1481 : W := mkw 0xf82ffedae46a0004 0x7f82ffedae46a000 0x8e33fcf8707f0002 0x08e33fcf8707f000

def z1482 : W := mkw 0x4500106251149941 0x0450010625114994 0x8e32b0e6735c99c7 0x78e32b0e6735c99c

def z1483 : W := mkw 0x680ffc4aeeea000c 0x7680ffc4aeeea000 0xfffffcffffff0003 0xffffffcffffff000

def z1484 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x0c22fce7f0000000 0x10c22fce7f000000

def z1485 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x7ddeff078f7fe1fe 0xf7ddeff078f7fe1f

def z1486 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x08223ce070000000 0x008223ce07000000

def z1487 : W := mkw 0x0000000000000000 0x0000000000000000 0x7fd3fc0783ff81ff 0xf7fd3fc0783ff81f

def z1488 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfaafbffff0000000 0x1faafbffff000000

def z1489 : W := mkw 0x70203c4ae0000000 0x170203c4ae000000 0x8a223ce070000000 0x08a223ce07000000

def z1490 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x5fdffc078fff01ff 0xf5fdffc078fff01f

def z1491 : W := mkw 0x00002800000a0004 0x100002800000a000 0x0a123c00031f0001 0x00a123c00031f000

def z1492 : W := mkw 0x480ff8424eea000c 0x7480ff8424eea000 0xbffffce67fff81c7 0xfbffffce67fff81c

def z1493 : W := mkw 0x4000104240000000 0x0400010424000000 0xffe3b0fe70801e0d 0xbffe3b0fe70801e0

def z1494 : W := mkw 0x4804f842446a0004 0x34804f842446a000 0xbef2fce6707f0002 0x1bef2fce6707f000

def z1495 : W := mkw 0x080000000eea000c 0x0080000000eea000 0x0fd3fc000fff0003 0xe0fd3fc000fff000

def z1496 : W := mkw 0x0e84c1251ff1ffba 0x20e84c1251ff1ffb 0x75ccc3078ff3ffff 0xf75ccc3078ff3fff

def z1497 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc000fdf0001 0x40fdffc000fdf000

def z1498 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x7deeffe7f0000000 0x17deeffe7f000000

def z1499 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf32f03f80f80fe0d 0x8f32f03f80f80fe0

def z1500 : W := mkw 0xf02b3edaea800008 0x5f02b3edaea80000 0x8a233cf873800001 0x08a233cf87380000

def z1501 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0b1f7c000fff0003 0xe0b1f7c000fff000

def z1502 : W := mkw 0x4500106251149941 0x0450010625114994 0x9e72b0e6735c19c7 0x39e72b0e6735c19c

def z1503 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc40e0cc 0xfffeffffffc40e0c

def z1504 : W := mkw 0x4004f84240000000 0x34004f8424000000 0xbee2fce670000000 0x1bee2fce67000000

def z1505 : W := mkw 0xf02b3fdfe0000000 0x5f02b3fdfe000000 0xca233ff9f0000000 0x0ca233ff9f000000

def z1506 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffff06081f6 0x7ffeffffff06081f

def z1507 : W := mkw 0xf02b3fdfe0000000 0x5f02b3fdfe000000 0xff637ffff0000000 0x1ff637ffff000000

def z1508 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xffe3fffff0000000 0x1ffe3fffff000000

def z1509 : W := mkw 0xf82ffedaeeea000c 0x7f82ffedaeeea000 0x8abfbcf87f4c0000 0x48abfbcf87f4c000

def z1510 : W := mkw 0x0a04e905046020a2 0x30a04e905046020a 0x7dccff078c60e1fe 0xf7dccff078c60e1f

def z1511 : W := mkw 0x0c8fe8201ffbdf1c 0x70c8fe8201ffbdf1 0x0fdffc000fffff3f 0xe0fdffc000fffff3

def z1512 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x5fdffc018fff0003 0xf5fdffc018fff000

def z1513 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0b1f3c000f9f0001 0x80b1f3c000f9f000

def z1514 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0801e01 0x1ffeffffff0801e0

def z1515 : W := mkw 0x0500002011149941 0x0050000201114994 0x00100000035c1803 0x600100000035c180

def z1516 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef83fe0fc0fecd 0xef3ef83fe0fc0fec

def z1517 : W := mkw 0xa00fee98a0000000 0x7a00fee98a000000 0xffeffff9f0000000 0x1ffeffff9f000000

def z1518 : W := mkw 0x050000201114dd41 0x0050000201114dd4 0x00100000035cffcf 0x600100000035cffc

def z1519 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xf5eef3fffc60e1fe 0xff5eef3fffc60e1f

def z1520 : W := mkw 0x0f04c1251574b9e3 0x20f04c1251574b9e 0x411c43018f7cf9ff 0xe411c43018f7cf9f

def z1521 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xb2ef03f80f80fe05 0x6b2ef03f80f80fe0

def z1522 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffffbf0001 0x9ffffffffffbf000

def z1523 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x7fdfff018fffe13f 0xf7fdfff018fffe13

def z1524 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc000fff013f 0xe0fdffc000fff013

def z1525 : W := mkw 0x4500106251149941 0x0450010625114994 0x2cb2b0e6735c99c7 0x72cb2b0e6735c99c

def z1526 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0a133c0003df0003 0x60a133c0003df000

def z1527 : W := mkw 0x0500002011149941 0x0050000201114994 0x30000006000099c4 0x130000006000099c

def z1528 : W := mkw 0x070000201114b9e3 0x0070000201114b9e 0x000000000000f9fc 0x0000000000000f9f

def z1529 : W := mkw 0xf02b3edae00a0004 0x5f02b3edae00a000 0x8a333cf8701f0000 0x08a333cf8701f000

def z1530 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0x802000fff0000000 0x1802000fff000000

def z1531 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x4fdfff000fff600b 0xe4fdfff000fff600

def z1532 : W := mkw 0xa00fc79da0000000 0x6a00fc79da000000 0xffefcffff0000000 0x1ffefcffff000000

def z1533 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0f1ffc000fff0003 0x80f1ffc000fff000

def z1534 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc6061fa 0x9ffeffffffc6061f

def z1535 : W := mkw 0xf82ffedaeeea000c 0x7f82ffedaeeea000 0x8b2f7cf87ca30000 0x88b2f7cf87ca3000

def z1536 : W := mkw 0xd02013d740000000 0x0d02013d74000000 0xb02003e670000000 0x1b02003e67000000

def z1537 : W := mkw 0xfa2fffdfeeea20ae 0x7fa2fffdfeeea20a 0xffffffffff4ce0c0 0x5ffffffffff4ce0c

def z1538 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0x2fffffe7ffff0003 0xf2fffffe7ffff000

def z1539 : W := mkw 0x6780156ff115bbf3 0x06780156ff115bbf 0xf02003fff000fffc 0x1f02003fff000fff

def z1540 : W := mkw 0x600ffc4ae0000000 0x7600ffc4ae000000 0xffeffcfff0000000 0x1ffeffcfff000000

def z1541 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xfa2233fff0000000 0x1fa2233fff000000

def z1542 : W := mkw 0xf22017dfe00020a2 0x0f22017dfe00020a 0xfee2b3fff040e1fe 0x7fee2b3fff040e1f

def z1543 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x6daffffff0000000 0x16daffffff000000

def z1544 : W := mkw 0x4000104240000000 0x0400010424000000 0xbee2b0e6704001c2 0x1bee2b0e6704001c

def z1545 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xff414c1ff0b39fff 0xbff414c1ff0b39ff

def z1546 : W := mkw 0x4500106241049041 0x0450010624104904 0x2cb2b0e6734c80c0 0x52cb2b0e6734c80c

def z1547 : W := mkw 0x6000144ae0000000 0x06000144ae000000 0xbee3bcfe70000000 0x1bee3bcfe7000000

def z1548 : W := mkw 0xf82fffdfeee00008 0x7f82fffdfeee0000 0xffefffffffe00003 0xfffefffffffe0000

def z1549 : W := mkw 0x0500002011149941 0x0050000201114994 0x0010000003dc9fcf 0xe0010000003dc9fc

def z1550 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0d9ffc000fff0002 0xc0d9ffc000fff000

def z1551 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0e13bc0003df0003 0x00e13bc0003df000

def z1552 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ffb3f80fccfe0d 0xef3ffb3f80fccfe0

def z1553 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xbee3fcfff0000000 0x1bee3fcfff000000

def z1554 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x0fdffc018fff0033 0xe0fdffc018fff003

def z1555 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfffffffff05c0002 0x1fffffffff05c000

def z1556 : W := mkw 0x4000104240000000 0x0400010424000000 0xb2e200e670000000 0x1b2e200e67000000

def z1557 : W := mkw 0xc00b12d240000000 0x4c00b12d24000000 0x8a2330f870000000 0x08a2330f87000000

def z1558 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x748cc3078c60e1fe 0x5748cc3078c60e1f

def z1559 : W := mkw 0xf82ffedaeeea000c 0x7f82ffedaeeea000 0xbffffcfe7fff0003 0xfbffffcfe7fff000

def z1560 : W := mkw 0x4a04d147446020a2 0x24a04d147446020a 0xbee2f0e7f06001f2 0x1bee2f0e7f06001f

def z1561 : W := mkw 0xf82ffedae4600000 0x7f82ffedae460000 0x8feffcf87c600002 0xe8feffcf87c60000

def z1562 : W := mkw 0x0f04c1251574b9e3 0x20f04c1251574b9e 0x0410c007837c99f7 0x70410c007837c99f

def z1563 : W := mkw 0xf02016dae0000000 0x0f02016dae000000 0xf02003f870000000 0x0f02003f87000000

def z1564 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75ccc3078cf3e1ff 0xf75ccc3078cf3e1f

def z1565 : W := mkw 0xf82fffdfe46a0004 0x7f82fffdfe46a000 0xfffffffffc7f0002 0xffffffffffc7f000

def z1566 : W := mkw 0x0504c12511149941 0x20504c1251114994 0x75dcc307835c99c7 0x775dcc307835c99c

def z1567 : W := mkw 0xd02ffbd740000000 0x7d02ffbd74000000 0xb0aeb3e670000000 0x1b0aeb3e67000000

def z1568 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x8a2f3ff870000000 0x08a2f3ff87000000

def z1569 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf1af03f80f80fe0c 0xcf1af03f80f80fe0

def z1570 : W := mkw 0x0a04c105046a20a6 0x20a04c105046a20a 0x75dcc3078c7fe1fe 0xf75dcc3078c7fe1f

def z1571 : W := mkw 0xf02fffdfe0004400 0x7f02fffdfe000440 0xffeffffff0006608 0x1ffeffffff000660

def z1572 : W := mkw 0x6004d54fe0000000 0x26004d54fe000000 0xffeffffff0000000 0x1ffeffffff000000

def z1573 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x77cdc3078ce0e1ff 0xf77cdc3078ce0e1f

def z1574 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xe3af03f80f80fe09 0xce3af03f80f80fe0

def z1575 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdd014c19f0b31f3e 0x9dd014c19f0b31f3

def z1576 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc006000 0x1ffeffffffc00600

def z1577 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75dcc3078f7ce1ff 0xf75dcc3078f7ce1f

def z1578 : W := mkw 0x4000104240000000 0x0400010424000000 0xbc20b0e670000000 0x1bc20b0e67000000

def z1579 : W := mkw 0x0f0fe8201ffeb9ef 0x70f0fe8201ffeb9e 0x0fdffc000ffff9ff 0xe0fdffc000ffff9f

def z1580 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xc32f03f80f80fe0d 0xec32f03f80f80fe0

def z1581 : W := mkw 0xf0203fdfe0000000 0x1f0203fdfe000000 0xf8203ffff0000000 0x1f8203ffff000000

def z1582 : W := mkw 0x058000201b95df59 0x0058000201b95df5 0x001000000fffffff 0xe001000000ffffff

def z1583 : W := mkw 0x0d0fe8201ffedd4d 0x70d0fe8201ffedd4 0x0fdffc000fffffcf 0xe0fdffc000fffffc

def z1584 : W := mkw 0x4000104240000000 0x0400010424000000 0xbee2b0e670000106 0x3bee2b0e67000010

def z1585 : W := mkw 0x6000144ae0000000 0x06000144ae000000 0xdf637cf9f0000000 0x1df637cf9f000000

def z1586 : W := mkw 0x080fe9050eea000c 0x7080fe9050eea000 0x0fdffc078fff0003 0xf0fdffc078fff000

def z1587 : W := mkw 0x0a0b28000eea20ae 0x50a0b28000eea20a 0x0a133c000fffe1ff 0xe0a133c000fffe1f

def z1588 : W := mkw 0x4000114740000000 0x0400011474000000 0xf02003e7f0000000 0x1f02003e7f000000

def z1589 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0x8e23fcfff06001f2 0x18e23fcfff06001f

def z1590 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffffcc0001 0xfffffffffffcc000

def z1591 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfb2f7ffff0000000 0x1fb2f7ffff000000

def z1592 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf02003fff000e00c 0x1f02003fff000e00

def z1593 : W := mkw 0xf22fffdfe00020a2 0x7f22fffdfe00020a 0xffeffffff040e1fe 0x7ffeffffff040e1f

def z1594 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xaffffffe7fff0003 0xeaffffffe7fff000

def z1595 : W := mkw 0xf02fffdfea800008 0x7f02fffdfea80000 0xffefffffff000000 0x5ffefffffff00000

def z1596 : W := mkw 0xfa24d7dfe46020a2 0x2fa24d7dfe46020a 0xffedcffffc60e1fe 0xfffedcffffc60e1f

def z1597 : W := mkw 0xd02ffbd740000000 0x7d02ffbd74000000 0xffeef3e7f0000000 0x1ffeef3e7f000000

def z1598 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffff5c0003 0x7ffffffffff5c000

def z1599 : W := mkw 0x0804e800046a0004 0x30804e800046a000 0x0fdefc000f7f0003 0xe0fdefc000f7f000

def z1600 : W := mkw 0x840b2ab00b8ad40c 0x5840b2ab00b8ad40 0xffffbff80fdffe0f 0xeffffbff80fdffe0

def z1601 : W := mkw 0x4000104240000000 0x0400010424000000 0xbee2b0e6704080c0 0x5bee2b0e6704080c

def z1602 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf36103fff0000000 0x1f36103fff000000

def z1603 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x6fdfff078fffe0fb 0xe6fdfff078fffe0f

def z1604 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0008004 0x7ffeffffff000800

def z1605 : W := mkw 0x4500106251149941 0x0450010625114994 0xbe32b0e6735c99c7 0x1be32b0e6735c99c

def z1606 : W := mkw 0x4500106251149941 0x0450010625114994 0xfff3b0fe735c99c7 0x7fff3b0fe735c99c

def z1607 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xebaffffff0000000 0x0ebaffffff000000

def z1608 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x0fdffc078fffe1ff 0xf0fdffc078fffe1f

def z1609 : W := mkw 0x4a0ff947446020a2 0x74a0ff947446020a 0xffefffe7fc60e1fe 0xfffefffe7fc60e1f

def z1610 : W := mkw 0xc00012d240000000 0x0c00012d24000000 0xfee2b3fe70000000 0x1fee2b3fe7000000

def z1611 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x7fdffc078fff81ff 0xf7fdffc078fff81f

def z1612 : W := mkw 0x050000201b94dd49 0x0050000201b94dd4 0x001000000f5cf9c7 0x6001000000f5cf9c

def z1613 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xba233cfe70000000 0x1ba233cfe7000000

def z1614 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff3000001 0x7ffeffffff300000

def z1615 : W := mkw 0x0f0000201574b9e3 0x00f0000201574b9e 0x000000000c60f9fe 0xe000000000c60f9f

def z1616 : W := mkw 0x4000104240000000 0x0400010424000000 0x8a3230e0731c0001 0x08a3230e0731c000

def z1617 : W := mkw 0xd02b3ad240000000 0x5d02b3ad24000000 0xbee2b0e670000000 0x1bee2b0e67000000

def z1618 : W := mkw 0x8a0feb950eea20ae 0x78a0feb950eea20a 0xffffffff8fffe1ff 0xfffffffff8fffe1f

def z1619 : W := mkw 0x6000144ae0000000 0x06000144ae000000 0xfff3fcfff3ff0003 0xffff3fcfff3ff000

def z1620 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc60603a 0xfffeffffffc60603

def z1621 : W := mkw 0xfa2fffdfeee064aa 0x7fa2fffdfeee064a 0xffeffffffca06638 0x9ffeffffffca0663

def z1622 : W := mkw 0x048000201b91df18 0x0048000201b91df1 0x000000000f80ff3d 0xe000000000f80ff3

def z1623 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x8a333cf8731c0001 0x08a333cf8731c000

def z1624 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xaaa3bcfe70000000 0x0aaa3bcfe7000000

def z1625 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0ddefc000f7f0002 0xe0ddefc000f7f000

def z1626 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffffc006008 0x9ffeffffffc00600

def z1627 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xc12d03f80c807e08 0x8c12d03f80c807e0

def z1628 : W := mkw 0x4500106241049041 0x0450010624104904 0xbef2b0e6734c98c5 0x7bef2b0e6734c98c

def z1629 : W := mkw 0x0500002011149941 0x0050000201114994 0x0a123000035c99c7 0x60a123000035c99c

def z1630 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff0200132 0x1ffeffffff020013

def z1631 : W := mkw 0xf024d7dfe0000000 0x2f024d7dfe000000 0xf0ac83fff0000000 0x1f0ac83fff000000

def z1632 : W := mkw 0x000fe8000a8a000c 0x7000fe8000a8a000 0x0fdffc0003df0003 0x60fdffc0003df000

def z1633 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0xdfdffc198fff1f3f 0xfdfdffc198fff1f3

def z1634 : W := mkw 0x808b029010110b10 0x4808b029010110b1 0xf3ef03f800b31f3f 0xaf3ef03f800b31f3

def z1635 : W := mkw 0x0580002011159b51 0x00580002011159b5 0x0000000000009ffc 0x00000000000009ff

def z1636 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0x8a233cf870801e01 0x08a233cf870801e0

def z1637 : W := mkw 0x4500106251149941 0x0450010625114994 0xfffeb3e6735c99c7 0x7fffeb3e6735c99c

def z1638 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfffffffff35c81c7 0x7fffffffff35c81c

def z1639 : W := mkw 0x0500002011149941 0x0050000201114994 0x0092b000035c99c7 0x60092b000035c99c

def z1640 : W := mkw 0x4a04d147446020a2 0x24a04d147446020a 0xffeef3e7fc206038 0x9ffeef3e7fc20603

def z1641 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfcaefffff0000000 0x1fcaefffff000000

def z1642 : W := mkw 0x840b2ab00b8ad40c 0x5840b2ab00b8ad40 0xffff7ff80fbffe0f 0xeffff7ff80fbffe0

def z1643 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0xb02000fe70009fc4 0x1b02000fe70009fc

def z1644 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x28aebfe670000000 0x028aebfe67000000

def z1645 : W := mkw 0x0804e8000eea000c 0x30804e8000eea000 0x0ed2fc000fff0003 0xe0ed2fc000fff000

def z1646 : W := mkw 0x4004d14740000000 0x24004d1474000000 0xbee2f0e7f0000000 0x1bee2f0e7f000000

def z1647 : W := mkw 0x080fe9050eea000c 0x7080fe9050eea000 0x7fdfff078fff81c7 0xf7fdfff078fff81c

def z1648 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x8fdffc180fff1e03 0xe8fdffc180fff1e0

def z1649 : W := mkw 0xa00b0698a0000000 0x4a00b0698a000000 0x8a230cf870000000 0x08a230cf87000000

def z1650 : W := mkw 0x4000104240000000 0x0400010424000000 0x802000e070000000 0x0802000e07000000

def z1651 : W := mkw 0xf02b3fdfe0000000 0x5f02b3fdfe000000 0xaa233ffe70000000 0x0aa233ffe7000000

def z1652 : W := mkw 0x70203c4ae0000000 0x170203c4ae000000 0xbee2bce670000000 0x1bee2bce67000000

def z1653 : W := mkw 0x000fe8000a8a000c 0x7000fe8000a8a000 0x0e13fc00039f0001 0x00e13fc00039f000

def z1654 : W := mkw 0x080fe8000eea440c 0x7080fe8000eea440 0x0fdffc000fff660b 0xe0fdffc000fff660

def z1655 : W := mkw 0x4000104240000000 0x0400010424000000 0xbee2b0e670008004 0x7bee2b0e67000800

def z1656 : W := mkw 0x800b2a900a8a000c 0x5800b2a900a8a000 0x8a333cf8039f0001 0x08a333cf8039f000

def z1657 : W := mkw 0x0d0000201ffedd4d 0x00d0000201ffedd4 0x001000000fffffcf 0xe001000000fffffc

def z1658 : W := mkw 0xf02b17dfe0000000 0x4f02b17dfe000000 0xf0ae03fff0000000 0x1f0ae03fff000000

def z1659 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x7fdfff078fff01f3 0xf7fdfff078fff01f

def z1660 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffff060e1fe 0x1ffeffffff060e1f

def z1661 : W := mkw 0x4000104240000000 0x0400010424000000 0x8e22b0e670000000 0x18e22b0e67000000

def z1662 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75def3078f6ce1fe 0xf75def3078f6ce1f

def z1663 : W := mkw 0x4a04d147446020a2 0x24a04d147446020a 0xf5ecc3e7fc60e1fe 0xff5ecc3e7fc60e1f

def z1664 : W := mkw 0x880feb950eea000c 0x7880feb950eea000 0xffffffff8fff0003 0xfffffffff8fff000

def z1665 : W := mkw 0x048000201b91df18 0x0048000201b91df1 0x000000000f93fe0d 0xe000000000f93fe0

def z1666 : W := mkw 0x0f84c1251575bbf3 0x20f84c1251575bbf 0x75dcc3078fffffff 0xf75dcc3078ffffff

def z1667 : W := mkw 0x4500106251149941 0x0450010625114994 0xbab2b0e6735c99c5 0x5bab2b0e6735c99c

def z1668 : W := mkw 0xf02b3edae0000000 0x5f02b3edae000000 0xfbef3ff87c00e00c 0xefbef3ff87c00e00

def z1669 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffffef0000 0xdffffffffffef000

def z1670 : W := mkw 0xf82fffdfe4600000 0x7f82fffdfe460000 0xffffffffff7c0003 0xfffffffffff7c000

def z1671 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0e137c0003bf0003 0x00e137c0003bf000

def z1672 : W := mkw 0xc80ffad24eea000c 0x7c80ffad24eea000 0xfffffffe7fff0003 0xffffffffe7fff000

def z1673 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf7ef83f80fc0fe0f 0xef7ef83f80fc0fe0

def z1674 : W := mkw 0xd02ffbd740000000 0x7d02ffbd74000000 0x2caeb3e670000000 0x12caeb3e67000000

def z1675 : W := mkw 0x4804d04244600000 0x24804d0424460000 0xbfeef0e67c600002 0xfbfeef0e67c60000

def z1676 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffff04000c0 0x1ffeffffff04000c

def z1677 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffff7f0002 0x5ffffffffff7f000

def z1678 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03fe0f80ffcd 0xff3ef03fe0f80ffc

def z1679 : W := mkw 0xc00b12d240000000 0x4c00b12d24000000 0xf3ef03fe70000000 0x1f3ef03fe7000000

def z1680 : W := mkw 0x0d8000201fff9b5d 0x00d8000201fff9b5 0x001000000fff9fff 0xe001000000fff9ff

def z1681 : W := mkw 0x4500106251149941 0x0450010625114994 0xfff2b0e6735c99cf 0xffff2b0e6735c99c

def z1682 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0x8feffcfff0000000 0x18feffcfff000000

def z1683 : W := mkw 0x0d04c0201ffe994d 0x20d04c0201ffe994 0x35dcc0060fff99c7 0xf35dcc0060fff99c

def z1684 : W := mkw 0x02000105000020a2 0x002000105000020a 0x708c03078c00e1fc 0x5708c03078c00e1f

def z1685 : W := mkw 0x4500106251149941 0x0450010625114994 0xbff2f0e6737c99c7 0xfbff2f0e6737c99c

def z1686 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef4ff80fa3fe0d 0xef3ef4ff80fa3fe0

def z1687 : W := mkw 0x400b384240000000 0x5400b38424000000 0x8a233ce070000000 0x08a233ce07000000

def z1688 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x75ccc3078c40e1fc 0x575ccc3078c40e1f

def z1689 : W := mkw 0xf82fffdfeeea000c 0x7f82fffdfeeea000 0xffffffffff6c0002 0xfffffffffff6c000

def z1690 : W := mkw 0xd02ffbd740000000 0x7d02ffbd74000000 0xbfefffe670000000 0x1bfefffe67000000

def z1691 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0x4fdfff078fff61fb 0xf4fdfff078fff61f

def z1692 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0xf5ccc31f8c60fffe 0xff5ccc31f8c60fff

def z1693 : W := mkw 0x4004d14740000000 0x24004d1474000000 0xf5ecc3e7f0000000 0x1f5ecc3e7f000000

def z1694 : W := mkw 0x080028000eea000c 0x1080028000eea000 0x08103c000fff0003 0xe08103c000fff000

def z1695 : W := mkw 0xf22b3fdfe00020a2 0x5f22b3fdfe00020a 0xfa233ffff000e1fc 0x1fa233ffff000e1f

def z1696 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x7fdfff000fff0003 0xe7fdfff000fff000

def z1697 : W := mkw 0x42001147400020a2 0x042001147400020a 0xfee2b3e7f000e1fc 0x1fee2b3e7f000e1f

def z1698 : W := mkw 0x050000201b94dd49 0x0050000201b94dd4 0x75dc83060fdcffcf 0xf75dc83060fdcffc

def z1699 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0b137c0003bf0001 0x80b137c0003bf000

def z1700 : W := mkw 0x880fea900eea440c 0x7880fea900eea440 0x0fdffc180fff0603 0xe0fdffc180fff060

def z1701 : W := mkw 0xf024ffdfe0000000 0x3f024ffdfe000000 0xf0204ffff0000000 0x1f0204ffff000000

def z1702 : W := mkw 0x840b02b00b80d408 0x4840b02b00b80d40 0xf3ef03f80fa0ff3f 0xef3ef03f80fa0ff3

def z1703 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc060fff01c3 0xf0fdffc060fff01c

def z1704 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0x802000f870001e00 0x0802000f870001e0

def z1705 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xfe23fffff0000000 0x1fe23fffff000000

def z1706 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xdf51fc19f0ff1f3f 0xbdf51fc19f0ff1f3

def z1707 : W := mkw 0x8a0feb950eea64ae 0x78a0feb950eea64a 0x4fdfff198fff663b 0xe4fdfff198fff663

def z1708 : W := mkw 0xfaafffdfe46122b2 0x7faafffdfe46122b 0xffeffffffca36638 0x9ffeffffffca3663

def z1709 : W := mkw 0xfa2fffdfe46020a2 0x7fa2fffdfe46020a 0xffeffffffc40e1c6 0x7ffeffffffc40e1c

def z1710 : W := mkw 0x4000104240000000 0x0400010424000000 0xbef2b0e6734c0000 0x5bef2b0e6734c000

def z1711 : W := mkw 0x6000144ae0000000 0x06000144ae000000 0xff614cfff0000000 0x1ff614cfff000000

def z1712 : W := mkw 0x0000000000000000 0x0000000000000000 0x0f537c0003bf0003 0xa0f537c0003bf000

def z1713 : W := mkw 0x0f0000201ff4fdeb 0x00f0000201ff4fde 0x001000000ffcffff 0xe001000000ffcfff

def z1714 : W := mkw 0x0480002011119b10 0x00480002011119b1 0x0000000003b39f3f 0xe0000000003b39f3

def z1715 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xff614ffff0b30003 0xbff614ffff0b3000

def z1716 : W := mkw 0xf02017dfe0000000 0x0f02017dfe000000 0xf2e203fff0000000 0x1f2e203fff000000

def z1717 : W := mkw 0x0a0fe9050eea20ae 0x70a0fe9050eea20a 0xffdfff1f8fffffff 0xfffdfff1f8ffffff

def z1718 : W := mkw 0xf824ffdfe46a0004 0x3f824ffdfe46a000 0xfc30fffff07f0002 0x1fc30fffff07f000

def z1719 : W := mkw 0x050b28201b9e994d 0x5050b28201b9e994 0x0a133c00039f1801 0x00a133c00039f180

def z1720 : W := mkw 0x20800408b0110b10 0x020800408b0110b1 0xd3414c19f0a31f3d 0xbd3414c19f0a31f3

def z1721 : W := mkw 0xf0afffdfe0010210 0x7f0afffdfe001021 0xffeffffff0000638 0x1ffeffffff000063

def z1722 : W := mkw 0xd02b3ad240000000 0x5d02b3ad24000000 0x8a2230e070000000 0x08a2230e07000000

def z1723 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0xb02000e7f00099f4 0x1b02000e7f00099f

def z1724 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0fdffc000fff1e0f 0xe0fdffc000fff1e0

def z1725 : W := mkw 0xfa24ffdfe46020a2 0x3fa24ffdfe46020a 0xfdecfffffc60e1fe 0xffdecfffffc60e1f

def z1726 : W := mkw 0xf82fffdfe4600000 0x7f82fffdfe460000 0xffeffffffc400000 0x5ffeffffffc40000

def z1727 : W := mkw 0x4000104240000000 0x0400010424000000 0xbee2b0e673000001 0x7bee2b0e67300000

def z1728 : W := mkw 0x4500106251149941 0x0450010625114994 0x3cf2b0e6735c81c6 0x73cf2b0e6735c81c

def z1729 : W := mkw 0x048000201b91df18 0x0048000201b91df1 0x0000000003931e01 0x00000000003931e0

def z1730 : W := mkw 0x4000104240000000 0x0400010424000000 0xffeeb3e67c00e00c 0xfffeeb3e67c00e00

def z1731 : W := mkw 0x070001251114b9e3 0x0070001251114b9e 0x70100307835cf9ff 0x770100307835cf9f

def z1732 : W := mkw 0x6580146af1159b51 0x06580146af1159b5 0xd02000f9f0001f3c 0x1d02000f9f0001f3

def z1733 : W := mkw 0x0500002011149941 0x0050000201114994 0x14500000035c99c7 0x714500000035c99c

def z1734 : W := mkw 0xd02ffbd740000000 0x7d02ffbd74000000 0xaaaeb3e670000000 0x0aaaeb3e67000000

def z1735 : W := mkw 0x0400002011109900 0x0040000201110990 0x0000000003109907 0x6000000000310990

def z1736 : W := mkw 0x000b28000a8a000c 0x5000b28000a8a000 0x0fdfbc000fdf0003 0xe0fdfbc000fdf000

def z1737 : W := mkw 0x0a04c105046020a2 0x20a04c105046020a 0x25ccc3078c60e1f2 0xf25ccc3078c60e1f

def z1738 : W := mkw 0x6000144ae0000000 0x06000144ae000000 0x8a233cf870000000 0x08a233cf87000000

def z1739 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x0e13fc000fff0003 0xe0e13fc000fff000

def z1740 : W := mkw 0xf0203edae0000000 0x1f0203edae000000 0x88203cf870000000 0x088203cf87000000

def z1741 : W := mkw 0xf02fffdfe0000000 0x7f02fffdfe000000 0xffeffffff000e00c 0x1ffeffffff000e00

def z1742 : W := mkw 0xf02b3edaea804408 0x5f02b3edaea80440 0xcb2f3ff87c806608 0x8cb2f3ff87c80660

def z1743 : W := mkw 0x0500002011149941 0x0050000201114994 0x34c08006004099c6 0x734c08006004099c

def z1744 : W := mkw 0x080fe8000eea000c 0x7080fe8000eea000 0x1fdffc000fff0107 0xf1fdffc000fff010

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z8,z0,z2,z3,z4,z9]),(0,[z10,z8,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z12,z3,z4,z6])],[(0,[z13,z14,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z15]),(0,[z8,z0,z2,z16,z3,z4,z6])],[],[(0,[z13,z17,z0,z2,z3,z4,z6]),(0,[z13,z0,z18,z2,z3,z4,z6]),(0,[z8,z0,z2,z2,z3,z4,z6]),(0,[z8,z0,z2,z19,z3,z4,z20]),(1,[z8,z0,z2,z3,z4,z21])],[(0,[z22,z0,z1,z2,z3,z4,z6])],[(0,[z23,z8,z0,z2,z3,z4,z24]),(0,[z8,z0,z2,z3,z4,z25,z6]),(0,[z26,z8,z0,z2,z3,z4,z6]),(0,[z27,z8,z0,z2,z3,z28,z4])],[(1,[z29,z8,z0,z2,z3,z4])],[(0,[z8,z30,z0,z2,z3,z4,z31])],[(0,[z13,z8,z0,z2,z3,z4,z31]),(1,[z32,z0,z2,z3,z4,z6])],[(1,[z8,z0,z2,z3,z4,z33]),(0,[z34,z8,z0,z2,z35,z4,z6]),(0,[z36,z8,z0,z2,z3,z37,z4]),(1,[z8,z0,z2,z3,z38,z4])],[(0,[z39,z13,z0,z2,z3,z4,z6]),(0,[z36,z40,z8,z0,z2,z3,z4]),(0,[z41,z8,z0,z2,z3,z4,z6]),(0,[z39,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z42,z3,z4,z6]),(0,[z43,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z44,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z6,z45]),(0,[z8,z0,z2,z3,z46,z4,z6])],[(0,[z13,z0,z2,z3,z4,z6,z47]),(0,[z48,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z49,z3,z4,z6])],[(1,[z8,z0,z2,z50,z3,z4])],[(0,[z51,z8,z0,z2,z3,z52,z6]),(0,[z8,z17,z2,z19,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z53])],[(0,[z40,z8,z0,z54,z3,z4,z6])]],
   [[],[(0,[z0,z1,z2,z55,z3,z4,z6]),(0,[z36,z51,z8,z0,z2,z3,z4]),(0,[z56,z8,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z11,z47]),(0,[z8,z0,z2,z3,z4,z6,z57])],[(1,[z8,z0,z2,z3,z4,z58]),(0,[z8,z0,z2,z3,z59,z4,z6])],[(0,[z34,z8,z0,z2,z3,z4,z11]),(0,[z60,z61,z0,z2,z3,z4,z6]),(0,[z62,z8,z0,z2,z3,z4,z6])],[(0,[z63,z8,z0,z2,z3,z4,z6]),(0,[z8,z64,z0,z65,z3,z4,z6]),(0,[z8,z64,z65,z2,z3,z4,z6]),(0,[z8,z0,z66,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z67]),(0,[z8,z0,z2,z3,z4,z68,z47])],[(1,[z13,z0,z2,z3,z4,z6]),(0,[z69,z8,z0,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z70,z2,z3,z4,z6])],[(0,[z71,z8,z0,z2,z3,z4,z72]),(0,[z17,z0,z73,z2,z3,z4,z6]),(0,[z0,z2,z3,z74,z28,z4,z6]),(0,[z8,z0,z2,z75,z28,z4,z6])],[],[(0,[z71,z8,z0,z2,z76,z4,z6]),(0,[z8,z0,z77,z2,z3,z4,z31]),(1,[z78,z0,z2,z3,z4,z6]),(0,[z60,z36,z8,z0,z2,z3,z4])],[(0,[z8,z0,z2,z3,z79,z4,z6]),(0,[z36,z8,z0,z80,z2,z3,z4])],[(0,[z43,z8,z0,z2,z3,z81,z6]),(0,[z8,z0,z2,z3,z4,z58,z82])],[(0,[z0,z1,z2,z83,z3,z4,z6]),(0,[z8,z0,z2,z84,z3,z4,z6]),(0,[z85,z8,z0,z2,z3,z4,z6]),(1,[z86,z8,z0,z28,z4,z6])],[(0,[z87,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z88,z6])],[(0,[z64,z0,z89,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z90,z9]),(0,[z14,z8,z0,z18,z2,z3,z4])],[(0,[z8,z91,z0,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z92]),(0,[z93,z36,z8,z0,z2,z3,z4])],[(0,[z13,z0,z2,z94,z3,z4,z6]),(0,[z8,z0,z2,z3,z95,z4,z9])]],
   [[(0,[z13,z8,z1,z2,z3,z4,z6]),(0,[z96,z8,z64,z2,z3,z4,z6]),(0,[z71,z8,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z97,z6]),(0,[z10,z8,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z11,z11]),(0,[z7,z8,z0,z2,z3,z98,z4])],[(0,[z8,z0,z1,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z99,z6])],[(0,[z8,z0,z100,z2,z3,z4,z20]),(1,[z101,z0,z2,z3,z4,z6]),(0,[z102,z8,z0,z2,z3,z4,z82]),(0,[z8,z0,z2,z103,z3,z4,z6]),(0,[z14,z36,z8,z0,z2,z3,z4])],[(1,[z39,z0,z2,z3,z104,z6]),(0,[z8,z0,z2,z3,z52,z4,z11]),(0,[z7,z8,z0,z2,z3,z4,z11])],[(0,[z8,z0,z2,z3,z4,z20,z47])],[(0,[z43,z0,z1,z2,z3,z4,z6]),(0,[z13,z8,z0,z2,z3,z105,z6]),(0,[z8,z0,z2,z3,z106,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z107]),(1,[z8,z0,z2,z3,z4,z108]),(0,[z8,z0,z2,z3,z4,z109,z6])],[(0,[z71,z8,z0,z110,z3,z4,z6]),(0,[z0,z2,z44,z3,z76,z4,z6]),(0,[z111,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z44,z3,z4]),(0,[z112,z8,z0,z2,z3,z4,z9]),(0,[z8,z17,z0,z2,z19,z4,z6]),(0,[z8,z0,z113,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z114,z6])],[(0,[z13,z0,z2,z115,z3,z4,z6]),(0,[z8,z0,z2,z75,z3,z4,z20]),(0,[z8,z0,z116,z2,z3,z4,z6])],[(0,[z117,z13,z0,z2,z3,z4,z6]),(0,[z118,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z54,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z104,z11]),(1,[z119,z8,z2,z3,z4,z6]),(0,[z51,z8,z0,z2,z3,z4,z31]),(0,[z117,z8,z0,z2,z3,z4,z20])],[(0,[z17,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z120,z65,z3,z4,z6]),(0,[z43,z8,z0,z2,z121,z4,z6])],[(0,[z8,z0,z2,z122,z3,z4,z6]),(0,[z123,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z120,z54,z3,z4,z6]),(0,[z8,z64,z0,z2,z3,z4,z9]),(1,[z8,z0,z2,z49,z4,z6]),(0,[z8,z0,z2,z3,z124,z4,z6])],[(0,[z8,z0,z125,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z31,z126]),(0,[z8,z2,z42,z3,z4,z5,z6])],[(0,[z8,z0,z42,z3,z4,z82,z6]),(0,[z8,z127,z0,z2,z3,z4,z6]),(0,[z8,z0,z128,z2,z3,z4,z6])],[(0,[z96,z123,z8,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z129,z6]),(0,[z51,z8,z0,z2,z3,z4,z130]),(0,[z8,z0,z2,z3,z131,z4,z6]),(0,[z8,z0,z120,z2,z3,z4,z132]),(0,[z8,z0,z2,z75,z3,z133,z6])],[(0,[z8,z0,z2,z44,z3,z4,z11]),(0,[z39,z36,z8,z0,z2,z3,z4]),(0,[z8,z0,z42,z3,z28,z4,z6]),(0,[z8,z0,z128,z2,z3,z82,z6])],[(1,[z51,z0,z2,z3,z52,z6]),(0,[z8,z0,z2,z3,z4,z134,z6]),(0,[z8,z0,z2,z3,z135,z4,z6]),(0,[z8,z136,z0,z2,z3,z4,z6]),(0,[z14,z8,z0,z2,z3,z98,z6])]],
   [[(1,[z0,z1,z2,z3,z4,z20]),(0,[z71,z8,z0,z2,z3,z137,z6]),(0,[z138,z8,z0,z2,z3,z4,z11])],[(0,[z56,z8,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z37,z4,z6]),(0,[z8,z0,z2,z3,z4,z90,z47])],[(0,[z8,z0,z2,z83,z4,z114,z6]),(0,[z8,z0,z2,z55,z3,z4,z90]),(0,[z8,z0,z2,z3,z139,z4,z6])],[(0,[z34,z8,z0,z2,z3,z4,z9]),(0,[z140,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z20,z11]),(0,[z8,z0,z128,z42,z3,z4,z6])],[(0,[z8,z0,z2,z3,z141,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z142]),(1,[z61,z0,z2,z3,z4,z6]),(0,[z8,z143,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z144,z3,z4,z9]),(0,[z8,z0,z80,z2,z3,z4,z6])],[(0,[z39,z8,z0,z2,z3,z4,z145])],[(0,[z8,z0,z2,z146,z44,z3,z4]),(0,[z8,z0,z2,z3,z4,z147,z6])],[(0,[z13,z0,z2,z3,z4,z90,z6])],[(0,[z8,z0,z148,z2,z3,z4,z6]),(0,[z7,z8,z0,z2,z149,z4,z6])],[(0,[z13,z36,z0,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z95,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z150]),(1,[z36,z8,z0,z2,z3,z4])],[(0,[z8,z17,z0,z2,z55,z3,z4]),(0,[z8,z0,z18,z2,z55,z3,z4])],[(1,[z17,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z75,z3,z4])],[(0,[z151,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z152,z4,z6])],[(0,[z39,z8,z0,z2,z3,z4,z153]),(0,[z8,z0,z2,z3,z4,z31,z31]),(0,[z8,z0,z2,z3,z4,z6,z92]),(0,[z8,z0,z2,z3,z154,z4,z6])],[(1,[z13,z96,z2,z3,z4,z6]),(0,[z8,z0,z155,z2,z3,z4,z6]),(0,[z8,z0,z156,z2,z3,z4,z6]),(0,[z8,z0,z157,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z158,z6]),(0,[z36,z8,z0,z2,z42,z3,z4]),(1,[z8,z0,z2,z159,z3,z4]),(0,[z8,z30,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z95,z98,z4])]],
   [[(0,[z13,z8,z0,z2,z3,z4,z6]),(0,[z36,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z160,z4,z6]),(0,[z8,z0,z2,z3,z4,z11,z9]),(0,[z161,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z1,z2,z3,z4,z9]),(1,[z8,z0,z2,z3,z162,z6]),(0,[z8,z0,z2,z3,z163,z4,z6]),(0,[z164,z8,z0,z2,z3,z4,z6]),(0,[z60,z8,z0,z2,z3,z165,z6]),(1,[z8,z30,z2,z3,z81,z6]),(0,[z8,z0,z2,z3,z37,z81,z6])],[(0,[z166,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z167,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z95,z4,z11]),(0,[z8,z0,z2,z3,z4,z6,z168]),(0,[z8,z169,z0,z2,z3,z4,z6]),(0,[z8,z170,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z54,z3,z4,z6]),(0,[z8,z0,z2,z3,z52,z4,z9]),(0,[z8,z0,z2,z3,z4,z171,z6]),(0,[z8,z0,z172,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z68,z9]),(0,[z10,z8,z0,z2,z75,z4,z6])],[(0,[z13,z64,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z173]),(0,[z43,z8,z0,z2,z174,z4,z6]),(0,[z0,z2,z3,z133,z4,z175,z6])],[(0,[z8,z1,z2,z3,z176,z4,z6]),(0,[z8,z0,z2,z177,z3,z4,z6]),(0,[z34,z8,z0,z2,z3,z178,z6]),(1,[z34,z0,z54,z3,z4,z6]),(0,[z8,z0,z2,z3,z179,z4,z6]),(0,[z60,z8,z0,z2,z176,z4,z6]),(1,[z180,z0,z2,z3,z4,z6])],[(0,[z181,z8,z0,z2,z3,z4,z6]),(0,[z36,z8,z0,z182,z2,z3,z4])],[(0,[z40,z8,z0,z2,z3,z4,z11]),(0,[z8,z183,z0,z2,z3,z4,z6])],[(1,[z8,z0,z2,z3,z4,z153]),(0,[z8,z0,z2,z3,z4,z104,z9]),(0,[z8,z0,z2,z3,z4,z20,z184]),(0,[z36,z8,z17,z0,z2,z3,z4]),(0,[z185,z8,z0,z2,z3,z4,z6])],[(0,[z186,z8,z0,z2,z3,z4,z6]),(1,[z51,z0,z2,z3,z4,z31]),(0,[z112,z8,z0,z2,z3,z4,z11]),(0,[z187,z8,z0,z2,z3,z4,z6])],[(0,[z96,z8,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z6,z188]),(0,[z8,z0,z189,z2,z3,z4,z6]),(0,[z190,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z191,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z192,z6]),(0,[z8,z0,z2,z3,z121,z4,z6]),(0,[z8,z0,z128,z2,z3,z37,z6])],[(0,[z0,z1,z2,z3,z4,z114,z6]),(0,[z8,z0,z193,z2,z3,z4,z6]),(0,[z43,z8,z0,z2,z3,z104,z6]),(0,[z117,z36,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z176,z4,z11]),(0,[z27,z8,z0,z2,z3,z4,z6])],[(0,[z8,z64,z0,z2,z3,z4,z11])],[(0,[z8,z0,z2,z19,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z6,z194])],[(0,[z8,z0,z2,z195,z3,z4,z6]),(0,[z8,z30,z0,z2,z3,z81,z6]),(0,[z196,z36,z8,z0,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z126]),(0,[z8,z0,z77,z2,z3,z4,z6]),(0,[z8,z0,z2,z197,z3,z4,z6]),(1,[z198,z0,z2,z3,z4,z6]),(0,[z138,z8,z0,z2,z3,z4,z9])],[(0,[z199,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z200,z4,z6]),(0,[z8,z0,z2,z3,z4,z201,z11]),(0,[z36,z8,z0,z2,z55,z4,z6])],[(0,[z0,z1,z128,z2,z3,z4,z6]),(1,[z8,z0,z202,z3,z4,z6]),(0,[z138,z8,z0,z128,z3,z4,z6])],[(0,[z8,z203,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z20,z9]),(0,[z8,z0,z2,z3,z204,z4,z6]),(0,[z8,z0,z2,z3,z4,z9,z205])],[(0,[z206,z8,z0,z2,z3,z4,z11])],[(0,[z23,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z207,z3,z4,z6]),(0,[z8,z0,z2,z208,z3,z4,z6]),(0,[z8,z209,z0,z2,z3,z4,z6])],[(1,[z8,z0,z2,z3,z4,z72]),(0,[z8,z0,z65,z2,z3,z4,z31]),(0,[z86,z8,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z50,z3,z4,z31])],[(0,[z0,z1,z2,z3,z37,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z68]),(1,[z8,z0,z2,z3,z4,z210]),(0,[z211,z8,z0,z2,z3,z4,z6]),(0,[z86,z8,z0,z120,z3,z4,z6])],[(0,[z71,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z212,z4,z6]),(0,[z8,z0,z2,z3,z213,z4,z6])],[(1,[z8,z0,z214,z3,z4,z6]),(0,[z8,z0,z2,z3,z215,z4,z6]),(0,[z8,z0,z2,z3,z216,z4,z6])],[(0,[z13,z0,z2,z3,z4,z11,z6]),(1,[z8,z0,z2,z3,z217,z6]),(0,[z8,z30,z2,z42,z3,z4,z6]),(0,[z8,z0,z2,z3,z218,z4,z6]),(0,[z219,z8,z0,z2,z3,z4,z6])],[(0,[z13,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z220,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z221,z6])],[(0,[z8,z0,z2,z3,z4,z222,z11]),(0,[z8,z0,z2,z3,z4,z6,z223]),(0,[z8,z0,z2,z3,z4,z108,z224])],[(0,[z13,z0,z2,z3,z52,z4,z6]),(0,[z8,z0,z2,z3,z98,z4,z31]),(0,[z8,z0,z2,z3,z4,z225,z6]),(0,[z8,z0,z2,z226,z3,z4,z6]),(1,[z227,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z228,z4,z6])],[(0,[z8,z0,z2,z3,z76,z4,z9])],[(0,[z119,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z229,z3,z4,z6]),(0,[z227,z8,z0,z2,z3,z4,z6]),(0,[z36,z8,z0,z18,z2,z3,z4])]],
   [[(0,[z8,z0,z2,z54,z3,z4,z6]),(0,[z51,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z230,z2,z3,z4,z6]),(0,[z231,z8,z0,z2,z3,z4,z9]),(0,[z36,z8,z0,z2,z3,z4,z82])],[(0,[z96,z8,z0,z2,z3,z4,z232]),(0,[z8,z0,z0,z2,z3,z4,z9]),(1,[z8,z233,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z31]),(0,[z13,z0,z2,z3,z4,z104,z6]),(0,[z36,z8,z0,z2,z3,z76,z4]),(1,[z8,z0,z2,z3,z165,z6]),(0,[z8,z0,z120,z2,z3,z4,z11])],[(0,[z8,z0,z182,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z234,z4,z6]),(0,[z8,z0,z2,z3,z81,z4,z20])],[(0,[z36,z36,z8,z0,z2,z3,z4])],[],[(0,[z8,z0,z235,z2,z3,z4,z6])],[(0,[z40,z8,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z236,z6])],[(0,[z13,z0,z2,z44,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z173]),(0,[z8,z0,z2,z3,z237,z4,z6])],[(0,[z238,z8,z0,z2,z3,z4,z6]),(0,[z239,z8,z0,z2,z3,z4,z6]),(0,[z240,z8,z0,z2,z3,z4,z6]),(0,[z241,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z242,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z243,z6])],[],[(0,[z8,z0,z2,z3,z133,z104,z6]),(0,[z244,z8,z0,z2,z3,z4,z6])],[(0,[z0,z2,z54,z3,z4,z104,z6]),(0,[z8,z0,z2,z3,z176,z4,z9]),(0,[z8,z0,z2,z3,z245,z4,z6])],[(0,[z8,z0,z2,z3,z4,z6,z126]),(0,[z13,z0,z2,z3,z105,z4,z6]),(0,[z13,z0,z2,z3,z4,z20,z6]),(0,[z96,z8,z0,z2,z3,z4,z11]),(0,[z34,z0,z2,z54,z3,z4,z6]),(0,[z117,z8,z0,z2,z3,z217,z6]),(0,[z8,z0,z120,z2,z3,z4,z246]),(0,[z8,z0,z2,z3,z38,z4,z6])],[(0,[z8,z17,z0,z2,z3,z4,z20]),(0,[z8,z0,z18,z2,z3,z4,z20])],[(0,[z8,z0,z247,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z5,z11]),(0,[z8,z0,z2,z3,z248,z4,z11]),(0,[z8,z0,z2,z3,z4,z108,z6])]],
   [[(0,[z13,z0,z2,z3,z249,z4,z6]),(0,[z8,z0,z2,z250,z3,z4,z6])],[(0,[z0,z1,z65,z2,z3,z4,z6]),(0,[z62,z0,z1,z2,z3,z4,z6]),(0,[z251,z8,z0,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z252]),(1,[z0,z2,z3,z74,z4,z6]),(0,[z10,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z55,z3,z4,z47])],[(0,[z253,z8,z0,z2,z3,z4,z31])],[(0,[z71,z0,z1,z2,z3,z4,z6]),(0,[z254,z8,z0,z2,z3,z4,z11]),(1,[z36,z8,z0,z2,z4,z114]),(0,[z14,z8,z0,z2,z3,z95,z6]),(0,[z255,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z162,z6]),(0,[z8,z0,z2,z3,z35,z4,z6]),(0,[z256,z8,z0,z2,z3,z4,z6]),(0,[z60,z8,z0,z2,z3,z257,z6]),(0,[z206,z8,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z258,z4,z9]),(0,[z8,z2,z3,z4,z11,z6,z9]),(0,[z8,z0,z2,z3,z4,z6,z68])],[(0,[z8,z0,z2,z83,z44,z4,z6])],[(0,[z39,z51,z0,z2,z3,z4,z6]),(0,[z259,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z260,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z261]),(0,[z60,z8,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z98,z4,z6]),(1,[z71,z0,z2,z76,z4,z6]),(0,[z8,z0,z2,z75,z176,z4,z6]),(0,[z8,z0,z2,z28,z4,z114,z6]),(0,[z8,z0,z2,z3,z4,z262,z6])],[],[(0,[z71,z0,z2,z3,z4,z104,z6]),(0,[z8,z263,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z264,z6]),(0,[z265,z8,z0,z2,z3,z4,z6])],[(0,[z51,z0,z1,z2,z3,z4,z6]),(0,[z13,z0,z0,z2,z3,z4,z6]),(0,[z266,z8,z0,z2,z3,z4,z6]),(0,[z267,z8,z0,z2,z3,z4,z6]),(0,[z8,z64,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z133,z4,z11]),(0,[z8,z0,z2,z3,z4,z268,z6])],[(0,[z8,z0,z2,z3,z4,z153,z6]),(0,[z8,z0,z2,z42,z3,z4,z9]),(0,[z43,z8,z0,z2,z3,z4,z9]),(0,[z36,z8,z0,z2,z3,z28,z4]),(0,[z269,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z270,z4,z6]),(0,[z51,z0,z2,z3,z52,z4,z6]),(0,[z93,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z58,z6])],[(0,[z0,z1,z182,z2,z3,z4,z6]),(0,[z39,z8,z0,z2,z3,z52,z6]),(0,[z8,z0,z2,z3,z271,z4,z11]),(0,[z272,z8,z0,z2,z3,z4,z6]),(0,[z36,z8,z0,z2,z3,z3,z4])],[(0,[z112,z0,z2,z3,z4,z6,z31]),(0,[z8,z0,z2,z3,z4,z6,z31]),(0,[z8,z273,z0,z2,z3,z4,z6]),(0,[z36,z8,z0,z65,z2,z3,z4]),(1,[z0,z2,z3,z4,z274,z6])]],
   [[(0,[z8,z0,z275,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z4,z11]),(0,[z36,z8,z0,z2,z3,z4,z68]),(1,[z276,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z76,z4,z11])],[(1,[z0,z2,z3,z4,z104,z31]),(0,[z60,z8,z0,z2,z3,z4,z31]),(0,[z56,z8,z0,z2,z55,z3,z4]),(0,[z60,z8,z2,z3,z176,z4,z6]),(0,[z43,z127,z0,z2,z3,z4,z6]),(0,[z8,z0,z120,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z277,z4,z6])],[(0,[z13,z7,z0,z2,z3,z4,z6]),(0,[z278,z8,z0,z2,z3,z4,z6]),(0,[z29,z8,z0,z2,z3,z4,z224])],[(0,[z34,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z4,z279,z6]),(0,[z8,z0,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z6,z280])],[(0,[z8,z0,z2,z3,z4,z6,z281]),(0,[z8,z0,z2,z3,z282,z4,z6])],[(0,[z13,z0,z2,z3,z176,z4,z6]),(1,[z8,z0,z2,z3,z4,z283]),(0,[z8,z0,z2,z19,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z284,z6])],[(0,[z13,z0,z2,z3,z4,z6,z285]),(1,[z13,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z286,z4,z6]),(1,[z287,z8,z0,z2,z3,z4]),(0,[z287,z8,z0,z2,z3,z4,z11])],[(0,[z51,z0,z2,z44,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z288,z20]),(1,[z8,z0,z2,z3,z4,z289]),(0,[z8,z0,z2,z3,z4,z290,z6])],[(0,[z0,z182,z2,z54,z3,z4,z6])],[(0,[z8,z0,z2,z3,z291,z4,z6]),(0,[z8,z0,z2,z3,z292,z4,z6]),(0,[z8,z0,z2,z83,z3,z4,z11])],[(0,[z36,z8,z0,z2,z3,z4,z31])],[(0,[z293,z13,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z294,z6]),(0,[z14,z8,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z295,z3,z4,z6])],[(0,[z296,z8,z0,z2,z3,z4,z6]),(0,[z297,z8,z0,z2,z3,z4,z6]),(1,[z8,z0,z2,z146,z3,z4]),(1,[z0,z2,z3,z4,z20,z31]),(0,[z8,z0,z2,z3,z4,z31,z298]),(0,[z8,z0,z2,z3,z4,z82,z20]),(1,[z8,z17,z2,z19,z4,z6])],[(0,[z8,z0,z2,z50,z3,z4,z6]),(0,[z8,z0,z65,z2,z3,z4,z6]),(0,[z299,z8,z0,z2,z3,z4,z6]),(0,[z86,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z300,z3,z4,z6])],[(0,[z8,z0,z2,z3,z28,z4,z20]),(0,[z8,z0,z2,z3,z4,z5,z9]),(1,[z8,z0,z2,z3,z301,z4]),(0,[z302,z8,z0,z2,z3,z4,z6])]],
   [[(0,[z71,z0,z2,z3,z76,z4,z6])],[(1,[z43,z1,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z126]),(0,[z8,z0,z303,z2,z3,z4,z11])],[(0,[z8,z0,z1,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z4,z304,z31]),(0,[z8,z0,z2,z3,z4,z305,z11])],[(0,[z306,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z307,z4,z6]),(0,[z308,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z309,z3,z4,z6])],[(0,[z7,z8,z0,z2,z55,z3,z4])],[(1,[z85,z0,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z257,z6]),(0,[z8,z0,z2,z55,z3,z133,z4]),(0,[z8,z0,z2,z3,z98,z4,z6])],[(0,[z8,z0,z310,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z311,z6]),(0,[z8,z0,z312,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z313,z6])],[(0,[z23,z8,z0,z2,z3,z4,z210]),(0,[z8,z0,z2,z3,z314,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z315]),(0,[z36,z8,z0,z128,z2,z3,z4]),(0,[z8,z0,z2,z4,z114,z6,z316])],[(1,[z8,z0,z2,z3,z4,z6]),(0,[z8,z1,z2,z42,z3,z4,z6]),(0,[z96,z8,z17,z2,z3,z4,z6]),(0,[z39,z8,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z317,z3,z4,z6]),(0,[z8,z0,z2,z55,z19,z3,z4]),(1,[z318,z0,z2,z3,z4,z6]),(1,[z10,z8,z0,z2,z224,z6]),(0,[z319,z36,z8,z0,z2,z3,z4])],[(0,[z40,z0,z182,z2,z3,z4,z6])],[(0,[z151,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z320]),(1,[z8,z0,z2,z3,z321,z4])],[(0,[z96,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z182,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z261]),(0,[z8,z0,z2,z3,z133,z4,z9]),(0,[z8,z0,z2,z3,z322,z4,z6])],[(0,[z13,z0,z120,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z323,z6]),(0,[z8,z0,z2,z3,z324,z4,z6]),(0,[z0,z2,z3,z98,z4,z274,z6])],[(1,[z40,z0,z182,z3,z4,z6]),(0,[z325,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z128,z3,z37,z4,z6])],[(1,[z8,z0,z2,z3,z4,z222])],[(0,[z8,z0,z2,z42,z3,z4,z11]),(0,[z43,z8,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z326,z6])]],
   [[(0,[z23,z8,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z55,z3,z4,z9]),(0,[z36,z8,z327,z0,z2,z3,z4])],[(0,[z8,z328,z0,z2,z3,z4,z6]),(0,[z329,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z330,z2,z3,z4,z6]),(0,[z138,z8,z0,z2,z55,z3,z4])],[(0,[z8,z0,z2,z3,z331,z4,z6]),(0,[z332,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z333,z2,z55,z3,z4])],[(0,[z8,z0,z2,z3,z334,z4,z6]),(1,[z8,z0,z2,z3,z4,z31]),(0,[z0,z2,z3,z4,z20,z6,z31]),(0,[z8,z0,z335,z2,z3,z4,z6]),(1,[z43,z8,z2,z3,z5,z6]),(0,[z336,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z337,z4,z6]),(0,[z338,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z339])],[(1,[z8,z0,z2,z3,z4,z340]),(0,[z8,z0,z341,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z342,z4,z6])],[(0,[z8,z0,z2,z3,z4,z6,z283]),(0,[z43,z96,z8,z2,z3,z4,z6]),(1,[z343,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z344,z4,z31])],[(0,[z0,z1,z275,z2,z3,z4,z6]),(1,[z8,z345,z2,z3,z4,z6]),(0,[z8,z0,z346,z2,z3,z4,z6]),(0,[z8,z0,z347,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z348,z6])],[(0,[z8,z0,z2,z3,z4,z349,z6]),(0,[z8,z0,z2,z75,z133,z4,z6]),(0,[z8,z350,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z351,z4,z6])],[(1,[z8,z0,z2,z3,z4,z130]),(0,[z117,z85,z0,z2,z3,z4,z6]),(1,[z117,z8,z42,z3,z4,z6]),(0,[z62,z8,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z352,z6]),(0,[z8,z0,z2,z55,z83,z3,z4])],[(0,[z86,z0,z1,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z4,z5,z6]),(1,[z8,z0,z110,z3,z4,z6]),(0,[z8,z2,z3,z81,z4,z5,z6]),(0,[z8,z327,z0,z2,z3,z4,z9])],[(1,[z13,z0,z2,z3,z4,z11]),(0,[z253,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z83,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z353,z6])],[(0,[z8,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z224,z20]),(0,[z8,z0,z2,z354,z3,z4,z6])],[(0,[z0,z1,z2,z19,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z126]),(0,[z8,z355,z0,z2,z3,z4,z6])],[(0,[z356,z8,z0,z2,z3,z4,z6])],[(0,[z60,z8,z0,z357,z3,z4,z6]),(0,[z8,z0,z18,z2,z3,z4,z68]),(0,[z196,z8,z0,z2,z3,z4,z6])],[(0,[z199,z0,z1,z2,z3,z4,z6]),(0,[z36,z8,z358,z0,z2,z3,z4])]],
   [[(1,[z60,z8,z2,z176,z4,z6]),(0,[z10,z8,z0,z2,z4,z224,z6]),(0,[z36,z8,z0,z2,z3,z4,z224]),(0,[z36,z8,z0,z2,z359,z3,z4])],[(1,[z8,z0,z2,z3,z4,z360]),(0,[z8,z361,z0,z2,z3,z4,z6])],[(1,[z8,z0,z2,z3,z4,z192]),(0,[z8,z0,z2,z3,z133,z5,z6])],[(1,[z8,z0,z2,z3,z137,z6]),(0,[z8,z0,z2,z3,z4,z362,z6]),(1,[z8,z0,z2,z103,z4,z6])],[(0,[z13,z0,z2,z3,z4,z6,z316]),(0,[z363,z8,z0,z2,z3,z4,z6]),(0,[z7,z14,z8,z0,z2,z3,z4])],[(0,[z13,z0,z2,z3,z133,z4,z6]),(0,[z8,z0,z2,z75,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z364,z6]),(0,[z365,z8,z0,z2,z3,z4,z6])],[(0,[z366,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z37,z104,z6]),(0,[z117,z8,z0,z2,z3,z4,z31]),(1,[z8,z0,z2,z367,z4,z6]),(0,[z8,z0,z2,z3,z368,z4,z6])],[(0,[z8,z0,z2,z3,z4,z6,z6]),(0,[z8,z0,z2,z369,z3,z4,z6])],[(0,[z123,z8,z0,z2,z3,z4,z31]),(0,[z34,z13,z0,z2,z3,z4,z6]),(0,[z34,z8,z0,z2,z3,z4,z20]),(0,[z40,z8,z0,z2,z55,z3,z4]),(0,[z8,z101,z0,z2,z3,z4,z6]),(0,[z8,z0,z370,z2,z3,z4,z6]),(0,[z36,z8,z0,z2,z3,z4,z114])],[(1,[z0,z1,z2,z3,z4,z222]),(0,[z8,z0,z2,z3,z4,z72,z6]),(0,[z8,z0,z2,z3,z4,z11,z316]),(0,[z8,z0,z2,z55,z3,z282,z4]),(0,[z8,z0,z2,z3,z4,z371,z6])],[(0,[z13,z0,z2,z55,z3,z4,z6]),(0,[z112,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z55,z3,z46,z4]),(0,[z8,z0,z2,z3,z372,z4,z6])],[(0,[z13,z0,z2,z3,z76,z4,z6]),(0,[z8,z233,z0,z2,z3,z4,z6]),(0,[z138,z8,z0,z2,z3,z4,z373])],[],[(0,[z374,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z367,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z31]),(0,[z375,z13,z0,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z320])],[(1,[z64,z1,z2,z3,z4,z6]),(0,[z376,z8,z0,z2,z3,z4,z6])]],
   [[(1,[z8,z0,z2,z3,z105,z6]),(0,[z8,z0,z2,z55,z3,z52,z4]),(0,[z8,z0,z2,z55,z3,z98,z4]),(0,[z8,z0,z377,z2,z3,z4,z6])],[(0,[z8,z0,z128,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z378,z6]),(0,[z8,z0,z2,z3,z4,z379,z6]),(0,[z8,z0,z2,z55,z3,z95,z4])],[(0,[z8,z0,z2,z44,z28,z4,z6])],[(0,[z13,z327,z0,z2,z3,z4,z6]),(0,[z36,z8,z0,z2,z3,z4,z104]),(0,[z380,z8,z0,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z381]),(0,[z8,z0,z2,z3,z4,z6,z205]),(0,[z8,z0,z2,z3,z382,z4,z6]),(0,[z36,z8,z0,z2,z3,z4,z6])],[(0,[z13,z0,z148,z2,z3,z4,z6]),(0,[z13,z0,z2,z83,z3,z4,z6]),(0,[z8,z30,z0,z2,z3,z104,z6]),(0,[z8,z0,z2,z383,z55,z3,z4]),(0,[z14,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z98,z6,z47])],[(0,[z8,z65,z2,z42,z3,z4,z6]),(0,[z8,z0,z384,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z385,z6]),(0,[z206,z8,z0,z2,z55,z3,z4])],[(0,[z8,z0,z2,z3,z386,z4,z6]),(0,[z8,z0,z2,z3,z37,z4,z11])],[(0,[z8,z0,z2,z3,z4,z387,z6]),(0,[z388,z8,z0,z2,z3,z4,z6]),(1,[z389,z0,z2,z3,z4,z6]),(0,[z389,z8,z0,z2,z3,z4,z6])],[(0,[z7,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z381,z6]),(0,[z62,z8,z0,z2,z3,z4,z9]),(0,[z102,z8,z0,z2,z3,z4,z6])],[(0,[z390,z8,z0,z2,z3,z4,z6]),(0,[z117,z8,z0,z2,z367,z4,z6]),(0,[z8,z0,z2,z229,z19,z3,z4])],[(0,[z391,z8,z0,z2,z3,z4,z6]),(0,[z71,z8,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z304,z6]),(0,[z8,z30,z64,z2,z3,z4,z6]),(0,[z8,z0,z2,z392,z3,z4,z6])],[(0,[z8,z0,z214,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z393,z4,z6]),(0,[z8,z0,z128,z65,z3,z4,z6]),(0,[z36,z8,z0,z2,z3,z4,z5]),(0,[z8,z0,z394,z2,z3,z4,z6]),(1,[z8,z327,z2,z3,z4,z11])],[(0,[z8,z0,z2,z3,z4,z395,z6]),(0,[z8,z0,z2,z3,z4,z20,z316]),(1,[z396,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z397]),(0,[z8,z327,z0,z2,z3,z4,z11]),(1,[z8,z0,z2,z3,z98,z47])],[(0,[z8,z0,z2,z3,z4,z104,z20]),(0,[z8,z0,z398,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z399,z6]),(0,[z8,z0,z2,z3,z4,z316,z31]),(1,[z8,z0,z2,z144,z3,z4])],[(0,[z8,z0,z2,z3,z4,z6,z298]),(1,[z8,z0,z357,z3,z4,z6])]],
   [[(0,[z8,z0,z2,z400,z3,z4,z6]),(0,[z123,z8,z1,z2,z3,z4,z6]),(0,[z327,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z75,z3,z4,z6]),(0,[z8,z401,z0,z2,z3,z4,z6]),(0,[z39,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z104,z82,z6]),(0,[z8,z0,z2,z3,z4,z217,z6])],[(0,[z402,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z403,z4,z6]),(0,[z51,z8,z230,z2,z3,z4,z6])],[(0,[z8,z0,z3,z37,z4,z82,z6]),(0,[z404,z36,z8,z0,z2,z3,z4])],[(1,[z8,z0,z2,z3,z4,z405]),(0,[z8,z0,z2,z44,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z11,z406]),(0,[z8,z0,z120,z2,z55,z3,z4])],[(1,[z13,z36,z0,z2,z3,z4]),(0,[z8,z30,z0,z2,z3,z4,z11]),(1,[z8,z0,z18,z3,z4,z68]),(0,[z8,z0,z2,z3,z4,z6,z407])],[(0,[z60,z0,z1,z2,z3,z4,z6]),(0,[z138,z13,z0,z2,z3,z4,z6]),(0,[z13,z8,z0,z2,z3,z4,z11]),(0,[z138,z8,z0,z2,z3,z4,z20]),(0,[z408,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z133,z4,z409])],[(0,[z43,z8,z0,z2,z3,z5,z6]),(0,[z8,z0,z2,z3,z149,z4,z6])],[(0,[z8,z0,z2,z3,z410,z4,z6]),(0,[z411,z17,z0,z2,z3,z4,z6]),(1,[z62,z8,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z6,z412]),(0,[z36,z413,z8,z0,z2,z3,z4])],[(0,[z23,z8,z0,z2,z3,z4,z6]),(0,[z71,z8,z0,z2,z44,z4,z6]),(0,[z8,z0,z414,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z82,z31]),(0,[z8,z0,z2,z3,z4,z20,z20])],[(0,[z30,z0,z1,z2,z3,z4,z6]),(0,[z13,z0,z2,z42,z3,z4,z6]),(0,[z415,z8,z0,z2,z3,z4,z6]),(0,[z29,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z416,z4,z20]),(0,[z417,z8,z0,z2,z3,z4,z6]),(1,[z102,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z6,z418])],[(0,[z13,z96,z8,z2,z3,z4,z6]),(0,[z8,z0,z419,z2,z3,z4,z6]),(0,[z23,z8,z0,z2,z76,z4,z6]),(0,[z8,z0,z2,z3,z4,z114,z9])],[],[(0,[z8,z0,z2,z3,z344,z4,z6])],[(1,[z1,z2,z3,z81,z4,z6]),(0,[z36,z8,z30,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z420,z4,z6])],[(0,[z14,z0,z1,z2,z3,z4,z6]),(0,[z117,z396,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z421,z3,z4,z6])]],
   [[(0,[z0,z422,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z232,z6])],[(0,[z8,z32,z0,z2,z3,z4,z6]),(0,[z8,z0,z128,z2,z3,z4,z9])],[(0,[z34,z8,z0,z2,z3,z4,z387]),(0,[z8,z0,z2,z3,z423,z4,z6]),(0,[z138,z101,z0,z2,z3,z4,z6])],[(1,[z0,z73,z2,z3,z4,z6])],[(0,[z71,z23,z0,z2,z3,z4,z6]),(0,[z424,z8,z0,z2,z3,z4,z6])],[(0,[z0,z425,z1,z2,z3,z4,z6]),(0,[z8,z0,z426,z2,z3,z4,z6]),(0,[z51,z8,z0,z2,z3,z104,z6]),(0,[z8,z0,z2,z3,z4,z90,z20])],[(0,[z427,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z428,z4,z6]),(0,[z8,z0,z2,z3,z37,z4,z9]),(0,[z8,z0,z2,z3,z429,z4,z6])],[(0,[z8,z0,z2,z3,z95,z4,z20]),(0,[z8,z0,z430,z2,z3,z4,z6]),(0,[z8,z0,z2,z83,z19,z4,z6]),(0,[z431,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z100,z2,z3,z4,z6]),(0,[z10,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z432,z6])],[(0,[z433,z8,z0,z2,z3,z4,z6]),(0,[z434,z36,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z435,z4,z6])],[(0,[z436,z8,z0,z2,z3,z4,z6]),(0,[z138,z8,z0,z2,z49,z4,z6])],[(0,[z39,z0,z1,z2,z3,z4,z6]),(0,[z437,z8,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z52,z4,z104,z6]),(0,[z8,z0,z2,z3,z4,z438,z6]),(0,[z8,z0,z2,z439,z3,z4,z6]),(0,[z138,z8,z0,z3,z4,z82,z6])],[(1,[z36,z0,z1,z2,z3,z4]),(0,[z40,z8,z0,z2,z3,z4,z20]),(0,[z8,z440,z0,z2,z3,z4,z6]),(0,[z7,z36,z8,z0,z2,z3,z4])],[(0,[z71,z8,z0,z2,z3,z4,z11]),(0,[z441,z8,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z75,z3,z4,z6])],[(0,[z8,z0,z2,z3,z104,z224,z6]),(0,[z112,z8,z0,z2,z3,z4,z20]),(0,[z117,z8,z0,z2,z3,z4,z6]),(0,[z442,z8,z0,z2,z3,z4,z6]),(0,[z10,z8,z0,z2,z3,z133,z6])],[(0,[z8,z0,z2,z3,z443,z4,z6]),(0,[z444,z8,z0,z2,z3,z4,z6])]],
   [[(0,[z123,z8,z0,z2,z3,z4,z6]),(0,[z445,z13,z0,z2,z3,z4,z6]),(1,[z8,z0,z2,z163,z4,z6]),(1,[z8,z0,z2,z3,z4,z397])],[(0,[z8,z0,z2,z3,z81,z4,z31]),(0,[z8,z0,z2,z3,z176,z4,z20]),(1,[z411,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z55,z3,z4])],[(0,[z8,z0,z2,z3,z4,z6,z405]),(0,[z39,z0,z2,z3,z4,z104,z6]),(0,[z8,z64,z0,z2,z3,z4,z20]),(0,[z43,z8,z0,z439,z3,z4,z6]),(0,[z8,z0,z83,z3,z28,z4,z6]),(0,[z343,z36,z8,z0,z2,z3,z4])],[(0,[z8,z0,z2,z3,z4,z33,z6]),(0,[z71,z8,z0,z2,z3,z4,z446]),(0,[z8,z0,z2,z447,z3,z4,z6]),(0,[z7,z8,z0,z3,z4,z90,z6])],[(0,[z8,z0,z448,z2,z3,z4,z6]),(0,[z8,z30,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z229,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z449,z6])],[(0,[z13,z0,z2,z3,z4,z114,z6]),(0,[z13,z8,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z54,z3,z4,z11]),(0,[z51,z8,z0,z2,z3,z4,z11]),(0,[z450,z8,z0,z2,z3,z4,z20]),(0,[z117,z8,z0,z42,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z224,z31]),(0,[z8,z0,z120,z2,z28,z4,z6])],[],[(0,[z138,z8,z451,z2,z3,z4,z6])],[(0,[z206,z13,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z452,z3,z4,z6]),(0,[z56,z8,z0,z2,z3,z4,z20]),(0,[z206,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z11,z107]),(0,[z453,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z454,z3,z4,z6]),(0,[z8,z455,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z456,z31]),(1,[z8,z0,z2,z121,z4,z6]),(0,[z8,z327,z0,z2,z55,z3,z4])],[(0,[z13,z0,z128,z2,z3,z4,z6]),(1,[z8,z457,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z458,z6]),(1,[z8,z0,z2,z3,z4,z412])],[(0,[z123,z8,z0,z2,z3,z4,z340]),(0,[z8,z0,z2,z76,z28,z4,z6]),(0,[z8,z17,z0,z2,z3,z4,z31]),(0,[z8,z0,z18,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z9,z9])],[(0,[z8,z0,z2,z3,z459,z4,z6]),(0,[z8,z0,z2,z3,z37,z5,z6])],[(0,[z8,z0,z2,z3,z460,z4,z6]),(0,[z8,z0,z2,z3,z4,z461,z6]),(0,[z36,z8,z0,z2,z44,z3,z4]),(0,[z8,z0,z2,z3,z462,z4,z6]),(0,[z8,z0,z2,z3,z4,z114,z11])],[]],
   [[(0,[z13,z0,z2,z3,z37,z4,z6]),(0,[z23,z0,z2,z44,z3,z4,z6]),(0,[z8,z0,z65,z2,z3,z4,z9]),(0,[z36,z8,z0,z2,z4,z114,z6])],[(0,[z8,z0,z2,z3,z4,z222,z20]),(0,[z8,z0,z2,z3,z463,z4,z6]),(0,[z8,z0,z2,z146,z55,z3,z4]),(0,[z8,z0,z2,z3,z4,z464,z6])],[(0,[z8,z17,z0,z2,z176,z4,z6])],[(0,[z117,z8,z0,z2,z163,z4,z6])],[(0,[z465,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z466,z6])],[(0,[z8,z0,z467,z2,z3,z4,z6]),(0,[z112,z56,z0,z2,z3,z4,z6])],[(0,[z51,z8,z0,z2,z3,z4,z468])],[(0,[z8,z0,z2,z3,z4,z6,z469]),(0,[z8,z0,z120,z2,z3,z4,z20]),(0,[z36,z8,z0,z2,z3,z176,z4]),(1,[z8,z0,z2,z213,z4,z6]),(0,[z8,z0,z2,z470,z3,z4,z6]),(0,[z8,z0,z2,z3,z471,z4,z6])],[(0,[z472,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z473])],[(0,[z117,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z3,z4,z20]),(1,[z8,z230,z2,z3,z4,z6]),(0,[z117,z8,z2,z42,z3,z4,z6]),(0,[z8,z0,z451,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z6,z474]),(0,[z475,z8,z0,z2,z3,z4,z6]),(0,[z476,z8,z0,z2,z3,z4,z6]),(0,[z276,z8,z0,z2,z3,z4,z6])],[(0,[z123,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z52,z4,z20]),(0,[z477,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z257,z6]),(0,[z8,z30,z0,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z81,z4,z6]),(0,[z10,z36,z8,z0,z2,z3,z4])],[(0,[z8,z0,z182,z2,z3,z4,z9]),(0,[z8,z61,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z75,z3,z224,z6])],[(0,[z13,z30,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z4,z6])],[(0,[z13,z23,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z218,z4,z9])]],
   [[(0,[z36,z8,z0,z2,z54,z3,z4]),(0,[z8,z0,z2,z3,z4,z252,z31]),(0,[z8,z0,z2,z42,z55,z3,z4]),(0,[z43,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z4,z82,z6]),(0,[z8,z0,z2,z55,z3,z139,z4])],[(0,[z478,z13,z0,z2,z3,z4,z6])],[(0,[z96,z8,z0,z2,z3,z4,z20]),(0,[z96,z8,z2,z3,z81,z4,z6]),(0,[z112,z36,z8,z0,z2,z3,z4]),(0,[z8,z0,z120,z2,z83,z4,z6]),(0,[z8,z0,z2,z3,z4,z479,z6])],[(1,[z8,z0,z2,z480,z4,z6]),(0,[z36,z8,z0,z2,z75,z3,z4])],[(0,[z8,z17,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z47,z31]),(0,[z8,z0,z2,z3,z4,z6,z481]),(0,[z411,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z28,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z246])],[(0,[z482,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z54,z3,z4,z9]),(0,[z51,z8,z0,z2,z3,z4,z9]),(0,[z43,z436,z0,z2,z3,z4,z6]),(1,[z8,z0,z2,z174,z4,z6]),(1,[z0,z2,z3,z4,z175,z6])],[(1,[z13,z0,z2,z3,z4,z285]),(0,[z308,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z483,z6])],[(0,[z0,z1,z18,z2,z3,z4,z6]),(0,[z484,z8,z0,z2,z3,z4,z6]),(0,[z60,z8,z0,z2,z3,z4,z481]),(0,[z8,z0,z2,z3,z38,z133,z4])],[(1,[z138,z8,z0,z3,z82,z6])],[(0,[z343,z8,z0,z2,z3,z4,z31]),(0,[z62,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z55,z3,z4,z316])],[(0,[z13,z0,z65,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z468])],[(1,[z13,z0,z2,z55,z3,z4]),(0,[z8,z0,z485,z2,z3,z4,z6]),(0,[z8,z0,z2,z19,z3,z4,z11]),(0,[z8,z0,z2,z3,z98,z4,z47])],[],[(0,[z34,z40,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z28,z4,z31]),(0,[z206,z36,z8,z0,z2,z3,z4])],[(0,[z36,z8,z0,z1,z2,z3,z4]),(1,[z0,z89,z2,z3,z4,z6]),(0,[z8,z0,z2,z486,z3,z4,z6])],[(0,[z34,z36,z8,z0,z2,z3,z4]),(0,[z487,z8,z0,z2,z3,z4,z31]),(0,[z356,z8,z0,z2,z3,z4,z9])]],
   [[(0,[z8,z0,z2,z3,z133,z4,z20])],[(0,[z36,z0,z1,z2,z3,z4,z6]),(0,[z138,z8,z233,z2,z3,z4,z6]),(0,[z8,z0,z2,z488,z3,z4,z6])],[(0,[z8,z0,z2,z55,z3,z81,z4]),(0,[z8,z0,z2,z489,z3,z4,z6]),(0,[z8,z0,z2,z3,z490,z4,z6])],[(0,[z8,z0,z65,z2,z3,z4,z11]),(0,[z86,z8,z0,z2,z3,z4,z11])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z491,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z492,z4,z20]),(0,[z8,z0,z2,z3,z4,z493,z6])],[(0,[z441,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z4,z20]),(0,[z227,z327,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z76,z4,z20]),(0,[z8,z0,z2,z3,z4,z494,z6]),(0,[z495,z8,z0,z2,z3,z4,z6])],[(0,[z13,z0,z182,z2,z3,z4,z6]),(0,[z8,z0,z2,z496,z3,z4,z6]),(0,[z8,z30,z0,z2,z3,z4,z326]),(0,[z8,z0,z2,z3,z95,z4,z68]),(0,[z8,z0,z2,z133,z4,z224,z6])],[],[(0,[z8,z0,z2,z3,z4,z137,z6]),(0,[z8,z0,z2,z3,z4,z497,z6]),(0,[z8,z0,z2,z3,z81,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z9])],[(0,[z8,z0,z2,z3,z4,z31,z9]),(0,[z8,z0,z2,z3,z98,z4,z11]),(0,[z8,z0,z2,z3,z498,z4,z6])],[(0,[z119,z51,z8,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z81,z82,z6])],[(0,[z8,z0,z499,z2,z3,z4,z6]),(0,[z60,z8,z0,z2,z3,z4,z9]),(1,[z8,z2,z3,z4,z11,z9]),(1,[z8,z0,z2,z3,z4,z473])],[],[(0,[z500,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z224,z6])],[(0,[z13,z0,z2,z54,z3,z4,z6]),(0,[z8,z0,z2,z83,z3,z4,z20]),(0,[z8,z0,z2,z3,z501,z4,z6])]],
   [[(0,[z8,z0,z182,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z90,z31]),(0,[z8,z0,z2,z3,z4,z11,z223]),(0,[z8,z0,z2,z55,z83,z4,z6])],[(0,[z404,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z20,z188]),(0,[z8,z0,z502,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z503,z6]),(0,[z8,z0,z2,z55,z3,z37,z4])],[(0,[z8,z0,z2,z3,z4,z456,z6]),(0,[z8,z0,z128,z2,z55,z3,z4]),(0,[z504,z36,z8,z0,z2,z3,z4])],[(0,[z505,z8,z0,z2,z3,z4,z6]),(0,[z10,z8,z0,z2,z3,z4,z31])],[(0,[z8,z506,z0,z2,z3,z4,z6]),(0,[z8,z17,z0,z2,z3,z4,z6]),(0,[z507,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z18,z2,z3,z4,z6])],[(0,[z60,z8,z0,z2,z3,z4,z508]),(0,[z8,z509,z0,z2,z3,z4,z6]),(0,[z510,z8,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z82,z6]),(0,[z23,z0,z1,z2,z3,z4,z6]),(0,[z96,z36,z8,z0,z2,z3,z4]),(0,[z117,z8,z64,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z28,z4,z6]),(1,[z8,z0,z2,z3,z4,z481]),(0,[z278,z8,z0,z2,z3,z4,z9]),(1,[z8,z0,z2,z3,z4,z246]),(0,[z8,z0,z2,z3,z4,z511,z6])],[(0,[z8,z0,z2,z3,z512,z4,z6]),(0,[z8,z8,z0,z2,z3,z4,z31]),(0,[z43,z8,z0,z2,z3,z4,z513])],[(0,[z36,z23,z8,z0,z2,z3,z4]),(0,[z319,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z83,z4,z224,z6]),(0,[z514,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z6,z515]),(0,[z8,z0,z2,z19,z3,z4,z9]),(0,[z516,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z284,z9]),(1,[z8,z0,z2,z3,z4,z132])],[(0,[z8,z517,z0,z2,z3,z4,z6]),(0,[z138,z36,z8,z0,z2,z3,z4]),(0,[z276,z0,z2,z3,z133,z4,z6])],[(0,[z8,z0,z2,z28,z4,z224,z6]),(0,[z8,z0,z2,z3,z4,z6,z47])],[(1,[z8,z0,z2,z3,z4,z468])],[(0,[z40,z8,z0,z2,z3,z4,z173]),(0,[z71,z0,z182,z2,z3,z4,z6]),(0,[z8,z518,z0,z2,z3,z4,z6])]],
   [[(0,[z8,z0,z2,z3,z4,z519,z6]),(0,[z520,z8,z0,z2,z3,z4,z6])],[(0,[z13,z8,z0,z2,z3,z4,z285]),(0,[z8,z0,z2,z3,z4,z521,z6])],[(0,[z8,z0,z1,z2,z3,z4,z126]),(0,[z8,z0,z2,z522,z3,z4,z6])],[(0,[z13,z0,z2,z3,z4,z162,z6]),(1,[z13,z0,z2,z3,z4,z33]),(0,[z13,z0,z2,z3,z4,z6,z68]),(0,[z86,z8,z0,z2,z3,z4,z9]),(0,[z299,z8,z0,z2,z3,z4,z9])],[(0,[z43,z13,z0,z2,z3,z4,z6]),(0,[z56,z8,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z42,z3,z4,z20]),(0,[z43,z8,z0,z2,z3,z4,z20])],[(1,[z8,z0,z2,z523,z3,z4]),(1,[z8,z0,z2,z3,z4,z524]),(0,[z8,z0,z2,z3,z4,z6,z525]),(0,[z8,z30,z0,z2,z55,z3,z4])],[(0,[z13,z8,z0,z2,z55,z3,z4]),(0,[z34,z8,z0,z2,z3,z4,z31])],[(0,[z526,z8,z0,z2,z3,z4,z6]),(1,[z8,z0,z156,z2,z3,z4])],[(0,[z8,z0,z2,z3,z4,z252,z6]),(0,[z8,z0,z2,z3,z165,z4,z6]),(0,[z8,z0,z2,z3,z4,z11,z68]),(0,[z527,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z528,z6])],[(0,[z34,z8,z345,z2,z3,z4,z6]),(0,[z8,z0,z2,z523,z3,z76,z4]),(0,[z8,z0,z2,z529,z3,z4,z6]),(0,[z8,z17,z0,z2,z3,z4,z397]),(0,[z8,z0,z2,z3,z81,z224,z6]),(0,[z8,z0,z2,z530,z3,z4,z6])],[(0,[z117,z8,z0,z65,z3,z4,z6]),(0,[z8,z0,z2,z3,z98,z4,z9]),(0,[z8,z0,z2,z3,z74,z4,z6]),(0,[z14,z8,z0,z2,z3,z4,z47])],[(0,[z8,z0,z2,z3,z4,z360,z6]),(0,[z60,z8,z0,z531,z3,z4,z6]),(0,[z7,z8,z0,z2,z3,z4,z68])],[(0,[z532,z8,z0,z2,z3,z4,z6])],[(0,[z62,z13,z0,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z9]),(0,[z36,z8,z0,z2,z3,z4,z90])],[(0,[z13,z0,z2,z3,z4,z6,z31]),(0,[z8,z0,z2,z3,z4,z288,z6]),(0,[z533,z8,z0,z2,z3,z4,z6]),(0,[z8,z17,z0,z2,z3,z4,z192]),(0,[z185,z8,z0,z2,z55,z3,z4])],[(0,[z0,z1,z2,z3,z4,z6,z9]),(1,[z13,z0,z2,z3,z4,z20]),(0,[z51,z0,z2,z54,z3,z4,z6]),(0,[z60,z8,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z534,z6])]],
   [[(0,[z8,z0,z2,z94,z3,z4,z6]),(0,[z190,z8,z0,z2,z55,z3,z4])],[(0,[z343,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z65,z2,z55,z3,z4])],[(0,[z0,z1,z2,z3,z535,z4,z6]),(0,[z293,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z446]),(0,[z198,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z11,z31]),(1,[z127,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z224,z6]),(0,[z8,z0,z1,z2,z3,z4,z31]),(1,[z8,z0,z2,z55,z4,z316]),(0,[z8,z0,z2,z3,z4,z536,z6])],[(0,[z8,z64,z1,z2,z3,z4,z6]),(0,[z13,z0,z2,z19,z3,z4,z6]),(0,[z39,z8,z0,z2,z3,z104,z6]),(0,[z8,z0,z2,z3,z537,z4,z6]),(0,[z8,z0,z2,z3,z28,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z538])],[(0,[z8,z0,z425,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z539,z6]),(0,[z8,z0,z540,z2,z3,z76,z4]),(0,[z8,z0,z2,z3,z4,z541,z6]),(0,[z8,z0,z2,z3,z52,z4,z31]),(0,[z8,z0,z2,z3,z4,z68,z31]),(0,[z7,z8,z0,z2,z3,z4,z31]),(1,[z8,z0,z2,z3,z4,z508]),(0,[z8,z0,z2,z3,z4,z542,z6])],[(0,[z543,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z544,z3,z4,z6]),(0,[z8,z545,z0,z2,z3,z4,z6]),(0,[z487,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z5,z20]),(0,[z546,z8,z0,z2,z3,z4,z6]),(1,[z265,z0,z2,z3,z4,z6]),(0,[z547,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z115,z3,z4,z6]),(0,[z13,z112,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z548,z6]),(0,[z117,z8,z0,z2,z3,z4,z524]),(0,[z36,z8,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z274,z6])],[(0,[z549,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z550,z4,z6]),(0,[z14,z8,z0,z2,z3,z4,z11])],[(0,[z8,z0,z2,z3,z551,z4,z6]),(0,[z8,z0,z2,z3,z552,z4,z6]),(0,[z553,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z176,z28,z4,z6])],[(0,[z8,z0,z2,z3,z4,z104,z31]),(0,[z8,z0,z2,z3,z4,z20,z68]),(0,[z8,z0,z554,z2,z3,z4,z6])],[],[(0,[z8,z0,z2,z3,z416,z4,z6])],[(0,[z71,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z4,z31,z555]),(0,[z556,z8,z0,z2,z3,z4,z6])],[(1,[z8,z0,z2,z3,z4,z515]),(1,[z8,z0,z2,z3,z178,z6]),(0,[z557,z8,z0,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z215,z6]),(0,[z558,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z559,z4,z6]),(0,[z8,z0,z2,z75,z3,z4,z9])]],
   [[(0,[z0,z193,z1,z2,z3,z4,z6]),(0,[z117,z8,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z560,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z561,z6])],[(0,[z8,z0,z54,z3,z28,z4,z6]),(0,[z8,z0,z2,z3,z562,z4,z6]),(0,[z8,z0,z2,z44,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z6,z184])],[(0,[z8,z0,z2,z3,z4,z340,z6]),(0,[z118,z13,z0,z2,z3,z4,z6]),(0,[z563,z8,z0,z2,z3,z4,z6]),(0,[z8,z396,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z47]),(0,[z138,z8,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z321,z4,z6])],[(0,[z13,z0,z2,z3,z98,z4,z6]),(1,[z8,z0,z2,z3,z4,z232]),(0,[z564,z8,z0,z2,z3,z4,z6]),(0,[z8,z565,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z566,z3,z4,z6])],[(0,[z71,z34,z0,z2,z3,z4,z6]),(0,[z39,z8,z0,z2,z3,z4,z11]),(0,[z56,z51,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z229,z55,z3,z4])],[(0,[z0,z1,z2,z3,z4,z519,z6]),(1,[z8,z0,z2,z35,z4,z6]),(0,[z8,z0,z2,z54,z55,z3,z4]),(0,[z51,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z4,z20,z31]),(1,[z56,z0,z2,z3,z4,z20])],[(0,[z8,z0,z2,z480,z3,z4,z6]),(0,[z8,z0,z531,z2,z3,z4,z6]),(0,[z567,z8,z0,z2,z3,z4,z6])],[(0,[z43,z36,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z90,z6])],[(0,[z8,z0,z2,z3,z4,z6,z568])],[(0,[z8,z0,z2,z3,z95,z4,z6])],[(0,[z569,z8,z0,z2,z3,z4,z31]),(0,[z10,z8,z0,z2,z3,z4,z6])],[(1,[z1,z2,z3,z176,z4,z6]),(0,[z8,z0,z2,z3,z570,z4,z6]),(1,[z8,z0,z531,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z373,z6])],[(0,[z23,z8,z0,z2,z3,z4,z11]),(0,[z36,z8,z0,z2,z3,z133,z4])],[(0,[z13,z8,z0,z2,z3,z4,z33]),(0,[z71,z8,z401,z2,z3,z4,z6]),(0,[z51,z0,z2,z3,z4,z6,z31]),(0,[z62,z8,z327,z2,z3,z4,z6]),(0,[z415,z8,z0,z2,z3,z4,z11]),(1,[z8,z0,z128,z3,z37,z6])],[(0,[z8,z0,z2,z3,z535,z4,z6]),(0,[z417,z8,z0,z2,z3,z4,z11])]],
   [[(0,[z36,z8,z0,z2,z19,z3,z4]),(0,[z8,z0,z571,z2,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z11])],[(0,[z8,z8,z0,z2,z3,z4,z6]),(0,[z8,z327,z0,z2,z3,z4,z20]),(0,[z8,z0,z113,z2,z3,z4,z6]),(0,[z318,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z3,z4,z90,z6,z68])],[(0,[z543,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z572,z4,z31]),(0,[z117,z8,z0,z2,z3,z215,z6]),(0,[z36,z8,z0,z156,z2,z3,z4])],[(0,[z573,z8,z0,z2,z3,z4,z6]),(0,[z8,z574,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z575]),(1,[z14,z8,z0,z2,z3,z95])],[],[(0,[z8,z0,z2,z3,z95,z4,z31]),(0,[z8,z0,z2,z576,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z577,z6])],[(1,[z8,z0,z2,z3,z4,z446]),(0,[z8,z0,z2,z176,z4,z224,z6])],[],[(0,[z8,z0,z2,z3,z4,z578,z6]),(0,[z8,z0,z2,z146,z3,z4,z20]),(0,[z8,z64,z0,z2,z3,z4,z261]),(0,[z36,z8,z0,z2,z3,z4,z9])],[(0,[z8,z0,z73,z2,z3,z4,z6]),(0,[z8,z30,z2,z3,z81,z4,z6]),(0,[z14,z8,z0,z2,z3,z4,z9])],[(0,[z13,z13,z0,z2,z3,z4,z6]),(0,[z13,z8,z0,z2,z3,z4,z20]),(0,[z40,z8,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z524,z6]),(0,[z60,z8,z17,z2,z3,z4,z6]),(0,[z579,z8,z0,z2,z3,z4,z6])],[(0,[z328,z0,z1,z2,z3,z4,z6]),(1,[z13,z0,z2,z3,z162,z6]),(0,[z8,z0,z18,z2,z3,z4,z90])],[(0,[z0,z1,z2,z44,z3,z4,z6]),(0,[z56,z8,z0,z2,z3,z4,z6]),(0,[z112,z8,z0,z2,z3,z4,z31])],[(0,[z0,z1,z2,z544,z3,z4,z6]),(0,[z60,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z4,z580,z6]),(0,[z581,z8,z0,z2,z3,z4,z6])],[(0,[z34,z8,z0,z2,z3,z4,z6]),(0,[z582,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z583,z6])],[(0,[z8,z0,z2,z3,z176,z4,z31]),(0,[z8,z0,z2,z3,z4,z6,z584]),(0,[z8,z2,z19,z3,z176,z4,z6])]],
   [[(0,[z71,z8,z0,z2,z3,z334,z6]),(0,[z8,z64,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z83,z176,z4,z6]),(1,[z8,z0,z2,z3,z4,z326]),(0,[z585,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z20,z320]),(0,[z586,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z587,z2,z3,z4,z6]),(0,[z8,z0,z2,z75,z3,z4,z11]),(0,[z588,z8,z0,z2,z3,z4,z6]),(0,[z269,z8,z0,z2,z55,z3,z4]),(0,[z8,z358,z0,z2,z3,z4,z6])],[(0,[z186,z13,z0,z2,z3,z4,z6]),(0,[z96,z8,z0,z2,z3,z4,z283]),(0,[z117,z8,z0,z2,z3,z4,z11]),(0,[z8,z0,z587,z2,z3,z176,z4]),(0,[z62,z32,z0,z2,z3,z4,z6]),(0,[z8,z0,z589,z2,z3,z4,z6])],[(0,[z375,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z590,z4,z6]),(1,[z8,z0,z116,z2,z3,z4])],[(0,[z123,z8,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z539,z4,z6]),(0,[z39,z8,z0,z2,z3,z4,z9]),(1,[z8,z0,z2,z149,z4,z6])],[(0,[z327,z0,z167,z2,z3,z4,z6])],[(0,[z206,z8,z0,z2,z3,z4,z31])],[(0,[z591,z8,z0,z2,z3,z4,z6]),(0,[z40,z8,z0,z2,z3,z4,z360]),(0,[z8,z0,z2,z592,z3,z4,z6]),(0,[z593,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z4,z82])],[(0,[z8,z0,z2,z594,z3,z4,z6]),(0,[z8,z0,z202,z2,z3,z4,z6]),(0,[z8,z0,z595,z2,z3,z4,z6])],[(0,[z596,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z76,z4]),(0,[z597,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z9,z598]),(0,[z599,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z600,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z11]),(0,[z434,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z11,z6]),(0,[z10,z8,z0,z2,z3,z224,z6])],[(0,[z8,z0,z1,z2,z3,z4,z6]),(0,[z343,z8,z0,z2,z44,z3,z4]),(0,[z36,z8,z0,z2,z3,z4,z47])],[(0,[z23,z8,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z601,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z568])],[(0,[z0,z1,z2,z3,z4,z90,z6]),(0,[z8,z0,z2,z3,z52,z4,z6]),(0,[z8,z602,z0,z2,z3,z4,z6]),(0,[z7,z8,z0,z2,z3,z4,z6])],[]],
   [[(0,[z0,z1,z2,z3,z95,z4,z6]),(0,[z8,z0,z2,z3,z52,z82,z6]),(0,[z8,z0,z2,z3,z603,z4,z6]),(0,[z62,z8,z0,z2,z3,z4,z20]),(0,[z62,z8,z2,z3,z4,z6,z9])],[(0,[z71,z8,z426,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z604,z6])],[(0,[z8,z0,z1,z2,z3,z4,z222]),(0,[z71,z13,z0,z2,z3,z4,z6]),(0,[z71,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z605,z4,z6]),(0,[z606,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z104,z6]),(0,[z8,z0,z2,z3,z4,z607,z6])],[(0,[z8,z0,z2,z3,z133,z52,z6]),(0,[z86,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z300,z55,z3,z4])],[(0,[z96,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z120,z2,z3,z4,z31])],[(0,[z8,z0,z2,z3,z4,z130,z6]),(0,[z8,z0,z2,z608,z3,z4,z6]),(0,[z78,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z609,z6])],[],[(0,[z610,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z611,z6]),(0,[z36,z8,z0,z2,z3,z52,z4]),(0,[z36,z8,z0,z2,z3,z98,z4])],[(0,[z34,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z44,z3,z4,z6]),(0,[z8,z0,z612,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z613,z6]),(0,[z36,z8,z0,z2,z3,z95,z4]),(0,[z8,z0,z2,z3,z95,z6,z47]),(0,[z8,z0,z614,z2,z3,z4,z6])],[(0,[z615,z8,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z176,z4,z6]),(0,[z8,z0,z2,z54,z3,z4,z20]),(0,[z51,z8,z0,z2,z3,z4,z20]),(0,[z78,z64,z0,z2,z3,z4,z6]),(0,[z14,z8,z0,z2,z3,z95,z4])],[(0,[z616,z8,z0,z2,z3,z4,z6]),(0,[z23,z8,z0,z2,z44,z4,z6]),(0,[z8,z0,z65,z3,z4,z82,z6]),(0,[z60,z325,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z81,z4,z9]),(0,[z8,z0,z2,z3,z4,z617,z6]),(0,[z138,z318,z0,z2,z3,z4,z6]),(0,[z138,z8,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z618,z4,z6]),(0,[z8,z0,z2,z3,z4,z210,z6]),(0,[z8,z0,z333,z2,z3,z4,z6])],[(0,[z8,z0,z619,z2,z3,z4,z6]),(0,[z620,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z65,z3,z28,z4,z6]),(0,[z138,z8,z0,z2,z3,z82,z6])],[(0,[z8,z0,z2,z3,z105,z4,z6]),(0,[z13,z36,z8,z0,z2,z3,z4]),(0,[z56,z0,z2,z3,z4,z104,z6]),(0,[z8,z0,z2,z3,z4,z20,z6]),(0,[z180,z0,z2,z3,z28,z4,z6]),(1,[z8,z0,z2,z55,z3,z4]),(0,[z265,z0,z2,z3,z98,z4,z6])],[(0,[z621,z8,z0,z2,z3,z4,z6])]],
   [[(0,[z96,z8,z0,z2,z3,z4,z31]),(0,[z96,z8,z2,z3,z176,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z555]),(0,[z117,z8,z0,z2,z3,z4,z568]),(0,[z8,z64,z0,z2,z3,z4,z381])],[(0,[z8,z0,z2,z3,z249,z4,z6]),(0,[z34,z8,z0,z182,z3,z4,z6]),(0,[z8,z0,z182,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z4,z6,z24]),(0,[z8,z0,z2,z3,z4,z622,z6]),(0,[z8,z623,z0,z2,z3,z4,z6]),(0,[z8,z350,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z5,z31]),(0,[z8,z0,z2,z624,z3,z4,z6])],[(0,[z625,z8,z0,z2,z3,z4,z6]),(0,[z569,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z114,z20]),(0,[z8,z64,z2,z3,z4,z5,z6]),(0,[z43,z8,z30,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z289,z6])],[(0,[z319,z8,z0,z2,z19,z3,z4]),(0,[z8,z0,z2,z55,z3,z28,z4])],[(0,[z123,z8,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z82,z11]),(0,[z8,z0,z18,z3,z4,z6,z68])],[(0,[z13,z8,z0,z2,z3,z162,z6]),(0,[z34,z0,z2,z44,z3,z4,z6]),(0,[z8,z0,z18,z2,z3,z4,z9]),(0,[z626,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z409]),(0,[z8,z0,z2,z55,z3,z3,z4]),(0,[z26,z36,z8,z0,z2,z3,z4])],[(0,[z627,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z159,z3,z4,z6]),(0,[z628,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z4,z68]),(0,[z8,z0,z629,z2,z3,z4,z6])],[(0,[z7,z0,z1,z2,z3,z4,z6]),(0,[z8,z457,z0,z2,z3,z4,z6]),(0,[z56,z0,z2,z3,z4,z20,z6]),(0,[z8,z0,z128,z2,z3,z4,z20]),(0,[z7,z8,z0,z2,z103,z4,z6])],[(0,[z8,z0,z182,z3,z28,z4,z6]),(0,[z8,z0,z2,z523,z3,z4,z6]),(0,[z8,z0,z2,z3,z572,z4,z6])],[(1,[z0,z1,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z175,z6])],[(0,[z60,z8,z0,z2,z19,z4,z6]),(0,[z630,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z631,z4,z6]),(0,[z319,z8,z0,z2,z3,z4,z9]),(1,[z0,z167,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z52,z37,z6]),(1,[z7,z8,z0,z3,z4,z90]),(0,[z8,z0,z2,z3,z4,z632,z6])],[(1,[z8,z401,z2,z3,z4,z6]),(0,[z633,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z52,z224,z6]),(0,[z8,z0,z2,z3,z133,z4,z31]),(0,[z8,z0,z2,z3,z37,z4,z20])],[(0,[z8,z0,z2,z3,z634,z4,z6]),(0,[z8,z0,z2,z3,z301,z28,z4]),(0,[z36,z8,z0,z116,z2,z3,z4])]],
   [[],[(0,[z0,z1,z2,z3,z4,z11,z6]),(0,[z635,z8,z0,z2,z3,z4,z6])],[(0,[z13,z123,z0,z2,z3,z4,z6]),(0,[z0,z1,z1,z2,z3,z4,z6]),(1,[z13,z1,z2,z3,z4,z6]),(0,[z40,z8,z0,z2,z3,z4,z6]),(0,[z636,z8,z0,z2,z3,z4,z6]),(0,[z637,z8,z0,z2,z3,z4,z6])],[(0,[z638,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z4,z31]),(0,[z639,z8,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z52,z4,z6]),(0,[z8,z0,z2,z3,z76,z4,z31]),(0,[z8,z0,z2,z3,z4,z640,z6]),(0,[z112,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z89,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z508,z6]),(0,[z62,z36,z8,z0,z2,z3,z4])],[(0,[z266,z13,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z83,z76,z4,z6])],[(0,[z138,z0,z1,z2,z3,z4,z6]),(0,[z445,z8,z0,z2,z3,z4,z6]),(0,[z71,z36,z8,z0,z2,z3,z4])],[(0,[z123,z8,z0,z2,z3,z4,z515]),(0,[z8,z1,z2,z3,z81,z4,z6]),(0,[z8,z0,z641,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z176,z4,z6]),(0,[z43,z8,z0,z2,z3,z4,z289]),(0,[z8,z0,z2,z3,z4,z642,z6]),(0,[z86,z8,z0,z2,z28,z4,z6])],[(0,[z8,z0,z2,z3,z4,z6,z285]),(0,[z43,z8,z0,z2,z3,z52,z6]),(0,[z8,z64,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z174,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z104,z6]),(0,[z8,z0,z2,z3,z618,z4,z6]),(0,[z34,z8,z0,z2,z3,z4,z405]),(0,[z8,z273,z0,z2,z3,z4,z20]),(1,[z8,z0,z2,z55,z83,z4])],[(0,[z8,z0,z345,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z643,z4,z6]),(0,[z138,z8,z0,z2,z3,z37,z6])],[(0,[z8,z644,z0,z2,z3,z4,z6]),(1,[z112,z0,z2,z3,z4,z31]),(0,[z450,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z645,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z316,z9])],[(0,[z13,z0,z2,z75,z3,z4,z6]),(0,[z8,z327,z0,z2,z3,z4,z31]),(0,[z8,z30,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z158,z20]),(0,[z8,z0,z2,z3,z4,z201,z6]),(1,[z325,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z646,z3,z4,z6])],[(0,[z8,z0,z2,z83,z3,z4,z31]),(1,[z8,z0,z2,z3,z139,z4])],[(0,[z8,z0,z2,z3,z81,z4,z11]),(0,[z8,z0,z2,z3,z4,z47,z9]),(0,[z8,z0,z2,z3,z647,z4,z6]),(0,[z8,z0,z2,z383,z3,z4,z6])],[(0,[z206,z8,z0,z2,z3,z4,z6]),(1,[z1,z2,z42,z3,z4,z6]),(0,[z648,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z649,z6]),(0,[z8,z0,z2,z3,z4,z31,z15]),(0,[z8,z64,z0,z42,z3,z4,z6]),(0,[z8,z0,z2,z3,z258,z4,z6]),(0,[z8,z0,z120,z83,z3,z4,z6])]],
   [[(1,[z8,z0,z2,z3,z334,z6]),(1,[z8,z0,z2,z229,z3,z4]),(0,[z8,z650,z0,z2,z3,z4,z6]),(0,[z8,z0,z651,z2,z3,z4,z6])],[(0,[z8,z0,z652,z2,z3,z4,z6]),(0,[z8,z0,z2,z653,z3,z4,z6])],[(0,[z13,z0,z2,z3,z4,z33,z6]),(0,[z0,z182,z2,z44,z3,z4,z6]),(1,[z8,z64,z65,z3,z4,z6]),(0,[z8,z0,z2,z144,z3,z4,z6])],[(1,[z8,z0,z439,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z224,z11]),(0,[z36,z8,z0,z2,z83,z3,z4]),(0,[z654,z8,z0,z2,z3,z4,z6]),(0,[z8,z655,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z20,z6]),(0,[z43,z8,z0,z202,z3,z4,z6]),(0,[z8,z0,z2,z3,z5,z82,z6]),(0,[z8,z0,z2,z3,z4,z9,z142]),(0,[z36,z8,z0,z2,z3,z4,z511])],[(1,[z8,z0,z2,z3,z4,z24]),(0,[z8,z30,z0,z2,z3,z4,z92]),(0,[z8,z0,z2,z3,z4,z82,z9]),(0,[z36,z8,z0,z2,z3,z435,z4])],[(0,[z8,z0,z18,z2,z3,z98,z4])],[(0,[z8,z0,z2,z3,z4,z222,z6]),(1,[z8,z0,z2,z3,z4,z513]),(0,[z8,z0,z2,z3,z28,z4,z9]),(0,[z138,z8,z0,z2,z213,z4,z6]),(0,[z8,z0,z656,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z316]),(0,[z86,z13,z0,z2,z3,z4,z6]),(0,[z8,z0,z65,z2,z3,z4,z20]),(0,[z86,z8,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z657,z6])],[(0,[z10,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z133,z4,z6]),(0,[z8,z17,z0,z2,z3,z4,z11]),(0,[z8,z0,z18,z2,z3,z4,z11]),(0,[z36,z8,z0,z2,z55,z3,z4])],[(0,[z8,z658,z0,z2,z3,z4,z6]),(0,[z7,z8,z0,z18,z3,z4,z6]),(0,[z8,z0,z2,z3,z659,z4,z6]),(1,[z8,z0,z2,z3,z4,z409]),(0,[z14,z8,z0,z2,z55,z3,z4])],[(0,[z8,z0,z2,z19,z4,z224,z6]),(0,[z62,z198,z0,z2,z3,z4,z6])],[(1,[z319,z8,z0,z2,z3,z4]),(0,[z660,z8,z0,z2,z3,z4,z6])],[(0,[z40,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z44,z3,z4,z104,z6]),(1,[z0,z346,z2,z3,z4,z6]),(0,[z8,z0,z120,z2,z3,z4,z6])],[(0,[z661,z8,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z76,z4,z6]),(0,[z112,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z98,z4,z20])]],
   [[(0,[z36,z8,z64,z0,z2,z3,z4]),(0,[z662,z8,z0,z2,z3,z4,z6])],[(1,[z8,z426,z2,z3,z4,z6]),(0,[z8,z0,z2,z110,z3,z4,z6])],[(0,[z8,z0,z2,z42,z3,z4,z31]),(0,[z43,z8,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z663,z3,z4,z6])],[(0,[z8,z0,z664,z2,z3,z4,z6]),(0,[z8,z0,z2,z665,z3,z4,z6]),(0,[z8,z327,z2,z3,z4,z11,z6]),(0,[z86,z8,z0,z2,z83,z4,z6])],[(0,[z13,z56,z0,z2,z3,z4,z6]),(0,[z40,z0,z2,z3,z4,z104,z6]),(0,[z0,z2,z3,z4,z104,z6,z31]),(0,[z8,z0,z120,z42,z3,z4,z6]),(0,[z666,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z667]),(0,[z504,z8,z0,z2,z3,z4,z6]),(0,[z668,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z178,z6]),(0,[z40,z8,z0,z182,z3,z4,z6]),(0,[z8,z0,z182,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z669,z4,z6]),(0,[z7,z8,z0,z2,z3,z4,z90])],[(0,[z71,z8,z0,z214,z3,z4,z6]),(0,[z39,z8,z0,z2,z55,z3,z4]),(1,[z491,z8,z0,z2,z3,z4]),(0,[z8,z670,z0,z2,z3,z4,z6])],[(0,[z478,z8,z0,z2,z3,z4,z6]),(1,[z27,z8,z0,z2,z3,z4])],[(0,[z0,z1,z2,z671,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z672]),(0,[z389,z30,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z4,z224])],[(0,[z673,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z145]),(0,[z674,z8,z0,z2,z3,z4,z6])],[(0,[z206,z0,z1,z2,z3,z4,z6]),(0,[z56,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z5,z6]),(0,[z8,z0,z2,z3,z4,z675,z6]),(0,[z8,z0,z2,z3,z248,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z676])],[(0,[z34,z8,z0,z54,z3,z4,z6]),(1,[z8,z0,z540,z2,z3,z4]),(0,[z62,z8,z0,z2,z3,z4,z31])],[(1,[z8,z0,z2,z3,z4,z285]),(0,[z8,z0,z2,z3,z677,z4,z6]),(0,[z8,z0,z2,z3,z4,z11,z473])],[(0,[z36,z123,z8,z0,z2,z3,z4]),(1,[z13,z0,z2,z3,z4,z31])],[(0,[z678,z8,z0,z2,z3,z4,z6]),(0,[z23,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z679,z4,z6]),(0,[z254,z8,z0,z2,z3,z4,z6])],[(0,[z13,z0,z2,z3,z4,z82,z6]),(0,[z13,z40,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z680,z3,z4,z6]),(0,[z8,z0,z2,z75,z19,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z21]),(1,[z8,z0,z2,z55,z28,z4]),(0,[z681,z8,z0,z2,z3,z4,z6])]],
   [[(0,[z86,z8,z0,z3,z28,z4,z6]),(0,[z8,z0,z2,z55,z3,z4,z114])],[(0,[z13,z0,z2,z3,z28,z4,z6]),(0,[z34,z8,z457,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z5,z224,z6]),(0,[z8,z0,z2,z3,z4,z21,z9])],[(0,[z8,z0,z2,z3,z4,z224,z9])],[(0,[z8,z0,z2,z682,z3,z4,z6]),(0,[z683,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z684,z4,z6])],[(0,[z8,z0,z685,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z316])],[(0,[z13,z51,z0,z2,z3,z4,z6]),(1,[z436,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z513]),(0,[z8,z0,z2,z3,z133,z4,z6])],[(0,[z356,z13,z0,z2,z3,z4,z6]),(0,[z293,z8,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z55,z4,z6,z316])],[],[(0,[z22,z8,z0,z2,z3,z4,z6]),(0,[z686,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z3,z4,z6]),(0,[z8,z17,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z271,z4,z6]),(0,[z8,z0,z2,z3,z4,z132,z6])],[(1,[z123,z1,z2,z3,z4,z6]),(0,[z43,z8,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z492,z4,z6]),(0,[z491,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z28,z4,z11]),(1,[z36,z8,z0,z2,z55,z4])],[(0,[z8,z0,z2,z55,z3,z4,z104]),(0,[z8,z0,z2,z55,z3,z4,z6])],[(0,[z8,z0,z2,z3,z76,z4,z6]),(0,[z8,z0,z687,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z176,z4]),(0,[z8,z0,z2,z159,z3,z176,z4]),(0,[z86,z36,z8,z0,z2,z3,z4]),(0,[z36,z8,z0,z120,z2,z3,z4]),(0,[z427,z8,z0,z2,z55,z3,z4]),(0,[z8,z688,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z42,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z222,z6]),(0,[z8,z30,z0,z2,z3,z52,z6]),(0,[z8,z0,z2,z55,z3,z321,z4])],[(0,[z8,z0,z2,z3,z4,z114,z31]),(0,[z231,z8,z0,z2,z3,z4,z6])],[(0,[z8,z0,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z689,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z580,z9]),(0,[z8,z0,z2,z3,z690,z4,z6]),(0,[z8,z0,z2,z75,z83,z4,z6])]],
   [[(0,[z13,z10,z0,z2,z3,z4,z6]),(0,[z8,z0,z120,z182,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z20,z474]),(0,[z36,z8,z0,z2,z3,z4,z316])],[(0,[z8,z0,z2,z19,z28,z4,z6]),(0,[z287,z8,z0,z2,z3,z4,z6])],[(0,[z0,z1,z120,z2,z3,z4,z6]),(0,[z96,z0,z1,z2,z3,z4,z6]),(0,[z96,z8,z2,z42,z3,z4,z6]),(0,[z8,z0,z2,z691,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z4,z5]),(0,[z30,z0,z346,z2,z3,z4,z6])],[(0,[z60,z13,z0,z2,z3,z4,z6]),(0,[z500,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z128,z2,z3,z4,z31]),(0,[z60,z8,z0,z2,z3,z4,z20]),(0,[z117,z8,z0,z2,z55,z3,z4]),(0,[z8,z327,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z95,z4,z90]),(0,[z442,z8,z0,z2,z55,z3,z4])],[(0,[z64,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z671,z3,z4,z6]),(0,[z8,z0,z2,z692,z3,z4,z6]),(0,[z8,z0,z2,z693,z3,z4,z6]),(0,[z694,z8,z0,z2,z3,z4,z6]),(0,[z43,z8,z2,z3,z4,z5,z6]),(0,[z8,z0,z2,z83,z3,z4,z6]),(1,[z8,z451,z2,z3,z4,z6]),(0,[z8,z0,z2,z695,z3,z4,z6])],[(0,[z123,z8,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z133,z81,z6]),(0,[z8,z0,z2,z3,z301,z4,z6])],[(0,[z696,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z357,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z697,z6]),(0,[z8,z0,z2,z359,z3,z4,z6]),(0,[z8,z698,z0,z2,z3,z4,z6])],[(0,[z13,z0,z2,z3,z81,z4,z6]),(0,[z13,z0,z2,z3,z4,z6,z9]),(0,[z13,z96,z0,z2,z3,z4,z6]),(1,[z8,z0,z587,z2,z3,z4])],[(0,[z8,z0,z422,z2,z3,z4,z6]),(0,[z34,z8,z0,z2,z480,z4,z6]),(0,[z34,z8,z0,z2,z3,z539,z6]),(0,[z8,z0,z2,z699,z3,z4,z6]),(0,[z8,z0,z2,z3,z37,z4,z31])],[(1,[z13,z0,z2,z3,z105,z6]),(0,[z8,z0,z540,z2,z3,z4,z6]),(0,[z8,z0,z700,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z6,z598]),(0,[z36,z8,z0,z2,z3,z81,z4]),(0,[z8,z0,z2,z3,z701,z4,z6])],[(0,[z702,z8,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z146,z3,z4,z6]),(1,[z8,z0,z2,z3,z4,z373])],[(1,[z0,z1,z2,z55,z3,z4]),(1,[z8,z0,z2,z3,z4,z387]),(0,[z8,z0,z303,z2,z3,z4,z6])],[(0,[z13,z0,z2,z3,z4,z224,z6]),(0,[z8,z0,z2,z3,z703,z4,z6]),(1,[z8,z0,z2,z3,z4,z145]),(0,[z8,z0,z2,z3,z4,z704,z6]),(0,[z8,z0,z2,z3,z4,z305,z6]),(0,[z8,z0,z2,z3,z4,z9,z126]),(0,[z8,z0,z2,z3,z4,z90,z11]),(0,[z180,z8,z0,z2,z3,z4,z6])],[(0,[z71,z51,z0,z2,z3,z4,z6]),(0,[z14,z8,z0,z2,z3,z4,z20]),(0,[z705,z8,z0,z2,z3,z4,z6]),(0,[z138,z8,z0,z2,z3,z4,z412]),(0,[z8,z0,z2,z55,z3,z4,z466])],[(0,[z706,z8,z0,z2,z3,z4,z6]),(0,[z51,z40,z0,z2,z3,z4,z6]),(0,[z36,z56,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z6,z406]),(0,[z413,z8,z0,z2,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z60,z13,z2,z176,z4,z6]),(0,[z36,z8,z0,z2,z3,z178]),(0,[z8,z0,z2,z3,z4,z707]),(0,[z8,z0,z2,z3,z4,z708]),(0,[z8,z0,z2,z3,z4,z709])],[(0,[z8,z0,z2,z710,z4,z6]),(0,[z8,z0,z2,z3,z711,z4]),(0,[z8,z0,z2,z3,z712,z4])],[(0,[z8,z0,z2,z480,z4,z31]),(0,[z8,z0,z2,z3,z539,z31]),(0,[z0,z2,z3,z572,z104,z31]),(1,[z8,z0,z3,z4,z713])],[(0,[z36,z0,z89,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z714])],[(0,[z8,z0,z2,z3,z165,z508]),(0,[z715,z0,z2,z3,z4,z6])],[(0,[z8,z345,z2,z480,z4,z6]),(0,[z8,z345,z2,z3,z539,z6]),(0,[z396,z0,z2,z3,z4,z716]),(0,[z8,z0,z2,z3,z717,z6]),(0,[z8,z0,z2,z55,z226,z4])],[(0,[z441,z1,z2,z3,z4,z31]),(0,[z13,z0,z2,z3,z4,z718]),(0,[z0,z2,z3,z4,z719,z31])],[(0,[z1,z2,z3,z81,z82,z6]),(0,[z0,z2,z3,z4,z6,z720]),(0,[z8,z0,z2,z721,z4,z6])],[(0,[z8,z0,z2,z722,z4,z6]),(0,[z396,z0,z2,z163,z4,z6]),(0,[z8,z0,z2,z723,z4,z6]),(0,[z567,z8,z42,z3,z4,z6])],[(0,[z13,z0,z2,z3,z4,z724]),(0,[z8,z0,z2,z3,z4,z725]),(0,[z8,z0,z2,z4,z726,z9])],[(0,[z8,z2,z3,z139,z4,z5]),(0,[z427,z0,z2,z3,z321,z4])],[(0,[z8,z0,z2,z3,z215,z31]),(0,[z727,z0,z2,z3,z4,z6])],[(0,[z8,z0,z554,z3,z4,z68])],[(0,[z0,z167,z2,z3,z4,z20]),(0,[z13,z0,z728,z3,z4,z6]),(0,[z71,z230,z2,z3,z4,z6]),(0,[z119,z51,z2,z3,z52,z6]),(0,[z8,z30,z2,z3,z81,z326])],[(0,[z8,z0,z202,z3,z4,z11]),(0,[z8,z595,z2,z3,z4,z9])],[(0,[z22,z0,z2,z3,z4,z31]),(0,[z8,z401,z2,z3,z4,z20])],[(0,[z0,z1,z2,z144,z3,z4]),(0,[z8,z0,z2,z3,z4,z473]),(0,[z8,z0,z2,z3,z4,z729]),(0,[z61,z0,z2,z3,z4,z9]),(0,[z8,z2,z3,z4,z11,z9])],[(0,[z8,z0,z2,z3,z4,z730]),(0,[z8,z0,z128,z3,z428,z6]),(0,[z8,z0,z2,z3,z4,z731]),(0,[z732,z0,z2,z3,z4,z6])],[],[(0,[z13,z1,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z733]),(0,[z10,z29,z8,z0,z2,z224])],[(0,[z0,z1,z2,z174,z4,z6]),(0,[z0,z2,z54,z3,z162,z6]),(0,[z8,z0,z2,z734,z3,z4]),(0,[z8,z0,z2,z3,z4,z735]),(0,[z8,z0,z736,z3,z4,z6]),(0,[z737,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z405]),(0,[z8,z0,z2,z3,z4,z738]),(0,[z8,z0,z2,z3,z4,z739])],[(0,[z40,z0,z182,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z740]),(0,[z0,z741,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z742])],[],[(0,[z8,z743,z2,z3,z4,z6]),(0,[z8,z0,z531,z3,z4,z31]),(0,[z0,z2,z3,z4,z274,z9])],[(0,[z8,z0,z2,z3,z4,z744]),(0,[z745,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z746,z4,z6]),(0,[z8,z0,z2,z3,z257,z481]),(0,[z276,z0,z2,z3,z4,z9])],[(0,[z13,z0,z2,z55,z83,z4]),(0,[z8,z747,z2,z3,z4,z6]),(0,[z748,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z55,z566,z4])],[(0,[z8,z0,z2,z749,z4,z6]),(0,[z8,z0,z2,z3,z750,z4]),(0,[z8,z0,z751,z55,z3,z4])],[(0,[z193,z1,z42,z3,z4,z6]),(0,[z1,z2,z3,z4,z521,z6]),(0,[z8,z0,z2,z3,z4,z752]),(0,[z325,z0,z2,z3,z4,z20])],[(0,[z1,z2,z522,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z753]),(0,[z8,z0,z2,z367,z215,z6])],[(0,[z13,z287,z0,z2,z3,z4]),(1,[z8,z42,z3,z217,z6]),(0,[z8,z0,z2,z3,z4,z754])]],
   [[(0,[z1,z2,z42,z3,z4,z20]),(0,[z0,z2,z3,z4,z755,z9]),(0,[z36,z8,z451,z2,z3,z4])],[(0,[z0,z756,z2,z3,z4,z6]),(0,[z13,z0,z2,z229,z3,z4]),(0,[z8,z0,z2,z3,z334,z20]),(0,[z0,z2,z3,z757,z104,z6]),(0,[z8,z0,z2,z3,z4,z758]),(0,[z8,z0,z2,z121,z4,z6])],[(0,[z8,z457,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z105,z285]),(0,[z8,z0,z2,z3,z4,z468]),(0,[z318,z0,z2,z3,z4,z412]),(0,[z8,z0,z2,z3,z4,z412])],[(0,[z13,z96,z2,z3,z4,z285]),(0,[z8,z0,z2,z759,z3,z4]),(0,[z8,z0,z2,z760,z4,z6])],[(0,[z1,z2,z3,z4,z252,z6]),(0,[z36,z8,z0,z2,z3,z162])],[(0,[z1,z2,z3,z81,z224,z6]),(0,[z13,z414,z2,z3,z4,z6]),(0,[z40,z0,z2,z3,z178,z6]),(0,[z43,z0,z2,z3,z104,z31]),(0,[z761,z8,z0,z2,z3,z4]),(0,[z762,z233,z2,z3,z4,z6])],[(0,[z375,z0,z2,z3,z162,z6]),(0,[z13,z0,z2,z763,z3,z4]),(0,[z78,z64,z65,z3,z4,z6])],[(0,[z13,z0,z2,z3,z38,z4]),(0,[z8,z0,z2,z3,z4,z764]),(0,[z13,z0,z2,z3,z162,z31]),(0,[z253,z8,z0,z2,z3,z572])],[(0,[z13,z0,z2,z3,z765,z6]),(0,[z13,z0,z2,z3,z4,z513]),(0,[z13,z96,z2,z55,z3,z4]),(0,[z8,z0,z766,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z767]),(0,[z8,z0,z2,z3,z4,z768]),(0,[z138,z318,z0,z3,z82,z6])],[(0,[z328,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z769,z6]),(0,[z8,z0,z2,z3,z4,z770]),(0,[z8,z451,z3,z4,z82,z6]),(0,[z8,z0,z451,z3,z82,z6]),(0,[z0,z771,z2,z3,z4,z6])],[(0,[z338,z0,z2,z3,z4,z20])],[(0,[z39,z0,z2,z3,z162,z6]),(0,[z117,z8,z772,z3,z4,z6]),(0,[z346,z2,z42,z3,z4,z6]),(0,[z138,z36,z8,z0,z3,z82])],[(0,[z0,z2,z3,z4,z274,z47])],[(0,[z8,z0,z2,z3,z4,z773]),(0,[z8,z774,z2,z3,z4,z6]),(0,[z8,z0,z2,z775,z4,z6]),(0,[z0,z89,z2,z3,z4,z381]),(0,[z411,z0,z2,z3,z4,z397])],[(0,[z119,z8,z2,z3,z4,z776]),(0,[z85,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z777,z121,z4]),(0,[z8,z650,z0,z28,z4,z6])],[(0,[z426,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z778,z4,z20]),(0,[z180,z0,z2,z55,z3,z4])],[(0,[z0,z1,z2,z3,z4,z779]),(0,[z389,z0,z2,z3,z104,z6]),(0,[z8,z0,z2,z3,z4,z780])],[(0,[z8,z0,z2,z50,z75,z4]),(0,[z8,z0,z2,z149,z4,z31]),(0,[z10,z8,z0,z2,z224,z9])],[(0,[z0,z1,z2,z163,z4,z6]),(0,[z0,z1,z2,z3,z4,z397]),(0,[z8,z0,z2,z480,z4,z405]),(0,[z8,z426,z2,z3,z4,z20]),(0,[z781,z0,z2,z3,z4,z6]),(0,[z8,z782,z2,z55,z3,z4]),(0,[z36,z8,z0,z2,z3,z783])],[(0,[z13,z0,z2,z3,z4,z20]),(0,[z36,z325,z0,z2,z3,z4]),(0,[z8,z0,z2,z784,z3,z4])],[(0,[z60,z8,z2,z176,z4,z481]),(0,[z127,z0,z202,z3,z4,z6]),(0,[z36,z8,z0,z2,z3,z785])],[(0,[z32,z0,z2,z55,z3,z4])],[(0,[z8,z0,z786,z3,z4,z6]),(0,[z0,z787,z2,z3,z4,z6])],[(0,[z788,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z789]),(0,[z7,z8,z0,z359,z3,z4])],[(0,[z790,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z105,z11]),(0,[z8,z0,z2,z3,z791,z6]),(0,[z117,z8,z42,z3,z4,z524])],[(0,[z431,z1,z2,z3,z4,z6]),(0,[z13,z96,z36,z2,z3,z4]),(0,[z8,z64,z125,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z508]),(0,[z198,z0,z2,z55,z3,z4])],[(0,[z356,z0,z2,z3,z162,z6]),(0,[z0,z2,z3,z792,z4,z6]),(0,[z0,z2,z3,z4,z274,z11]),(0,[z532,z8,z0,z2,z55,z4]),(0,[z36,z8,z0,z793,z3,z4])],[(0,[z0,z1,z2,z121,z4,z6]),(0,[z0,z422,z2,z3,z618,z6]),(0,[z8,z451,z2,z3,z4,z373])],[(0,[z0,z1,z2,z3,z4,z412]),(0,[z13,z102,z0,z2,z3,z4]),(0,[z0,z2,z3,z4,z20,z473]),(0,[z8,z0,z2,z794,z163,z4]),(0,[z166,z8,z0,z28,z4,z6]),(0,[z795,z8,z0,z2,z3,z4])],[(0,[z8,z0,z3,z4,z713,z6])],[(1,[z1,z116,z2,z3,z4]),(0,[z796,z8,z0,z2,z3,z4]),(0,[z8,z345,z2,z3,z4,z9]),(0,[z797,z0,z2,z3,z4,z6]),(0,[z36,z8,z0,z2,z3,z165]),(0,[z436,z0,z2,z3,z4,z798]),(0,[z138,z8,z0,z3,z82,z6]),(0,[z8,z0,z2,z55,z429,z4])]],
   [[(0,[z101,z0,z2,z3,z4,z20]),(0,[z8,z30,z439,z3,z4,z6])],[(0,[z36,z1,z116,z2,z3,z4]),(0,[z411,z96,z2,z3,z4,z6]),(0,[z186,z230,z2,z3,z4,z6]),(0,[z36,z8,z0,z2,z144,z4])],[(0,[z8,z0,z2,z799,z4,z6]),(0,[z0,z2,z3,z4,z33,z285]),(0,[z8,z0,z2,z800,z4,z6]),(0,[z8,z0,z2,z3,z4,z801]),(0,[z8,z0,z18,z3,z4,z713])],[(0,[z8,z0,z214,z55,z3,z4]),(0,[z802,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z803]),(0,[z8,z0,z2,z804,z4,z6]),(0,[z805,z8,z0,z2,z163,z4]),(0,[z8,z0,z2,z4,z806,z6])],[(0,[z0,z807,z2,z3,z4,z6]),(0,[z78,z0,z2,z55,z3,z4]),(0,[z8,z651,z2,z3,z4,z9])],[],[(0,[z436,z0,z2,z3,z4,z20]),(0,[z8,z0,z808,z2,z3,z4]),(0,[z227,z0,z2,z55,z3,z4]),(0,[z809,z0,z2,z3,z4,z6])],[(0,[z8,z1,z116,z2,z3,z4]),(0,[z8,z0,z357,z3,z4,z11])],[(0,[z8,z17,z2,z19,z4,z11])],[(0,[z8,z0,z2,z35,z4,z6]),(0,[z36,z23,z0,z2,z44,z4]),(0,[z36,z276,z0,z2,z3,z4])],[(0,[z123,z1,z2,z3,z4,z20]),(0,[z71,z0,z156,z2,z3,z4]),(0,[z0,z2,z146,z3,z321,z4]),(0,[z8,z233,z2,z55,z3,z4])],[(0,[z8,z0,z2,z3,z4,z810])],[(0,[z51,z0,z2,z3,z52,z20]),(0,[z811,z0,z2,z3,z4,z6]),(0,[z8,z0,z531,z3,z257,z6]),(0,[z0,z2,z3,z74,z4,z9])],[(0,[z8,z0,z2,z3,z178,z31]),(0,[z332,z8,z2,z176,z4,z6]),(0,[z8,z812,z2,z3,z4,z6]),(0,[z180,z0,z2,z3,z4,z813]),(0,[z8,z0,z2,z213,z4,z412])],[(0,[z507,z1,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z105,z33]),(0,[z8,z0,z2,z367,z4,z9]),(0,[z8,z0,z2,z814,z3,z4])],[(0,[z815,z8,z0,z2,z3,z4])],[(0,[z36,z8,z0,z2,z3,z105]),(0,[z8,z345,z2,z3,z178,z6])],[(0,[z356,z0,z2,z3,z4,z20]),(0,[z8,z0,z816,z3,z4,z6])],[(0,[z8,z401,z214,z3,z4,z6]),(0,[z117,z8,z42,z3,z215,z6]),(0,[z8,z0,z357,z3,z4,z481])],[(0,[z8,z0,z2,z3,z4,z11]),(0,[z543,z0,z544,z3,z4,z6]),(0,[z8,z0,z2,z3,z817,z6]),(0,[z8,z818,z2,z3,z4,z6]),(0,[z71,z0,z2,z76,z4,z9]),(0,[z0,z156,z2,z3,z4,z31]),(0,[z318,z0,z2,z3,z4,z11]),(0,[z10,z8,z0,z2,z224,z11]),(0,[z36,z0,z2,z3,z4,z274])],[(0,[z660,z0,z182,z3,z4,z6]),(0,[z819,z8,z0,z2,z3,z4]),(0,[z119,z8,z2,z55,z3,z4]),(0,[z56,z0,z2,z3,z4,z720])],[(0,[z1,z2,z3,z176,z4,z222]),(0,[z13,z451,z2,z3,z4,z6]),(0,[z8,z0,z3,z820,z4,z6])],[(0,[z8,z0,z2,z3,z4,z821]),(0,[z0,z89,z2,z3,z4,z822])],[(0,[z64,z1,z2,z3,z4,z9]),(0,[z0,z167,z2,z3,z4,z31])],[(0,[z8,z0,z2,z3,z823,z6]),(0,[z43,z8,z2,z3,z243,z6])],[(0,[z8,z0,z2,z3,z4,z446]),(0,[z8,z824,z2,z3,z4,z6])],[(0,[z1,z2,z3,z176,z4,z31]),(0,[z8,z0,z2,z825,z4,z6]),(0,[z8,z0,z2,z826,z3,z4])],[(0,[z1,z2,z83,z176,z4,z6]),(0,[z34,z0,z94,z3,z4,z6]),(0,[z0,z73,z2,z3,z4,z11]),(0,[z287,z8,z0,z2,z229,z4])],[(0,[z0,z1,z2,z799,z4,z6]),(0,[z13,z0,z2,z159,z3,z4]),(0,[z13,z0,z2,z3,z4,z387]),(0,[z8,z457,z2,z3,z4,z405]),(0,[z8,z0,z128,z3,z37,z31]),(0,[z396,z0,z2,z3,z4,z524])],[(0,[z78,z0,z2,z3,z827,z6]),(0,[z8,z0,z828,z3,z4,z6])],[(0,[z1,z587,z2,z3,z176,z4]),(0,[z0,z1,z2,z3,z4,z803]),(0,[z8,z0,z2,z3,z162,z20])]],
   [[(0,[z8,z0,z829,z2,z3,z4]),(0,[z8,z0,z2,z3,z830,z6])],[(0,[z8,z0,z2,z831,z4,z6])],[(0,[z8,z0,z2,z3,z4,z832])],[(0,[z71,z0,z2,z3,z178,z6]),(0,[z34,z0,z54,z3,z4,z20]),(0,[z8,z833,z2,z3,z4,z6])],[(0,[z8,z0,z2,z834,z3,z4]),(0,[z13,z0,z2,z3,z835,z6]),(0,[z8,z0,z2,z3,z4,z836]),(0,[z8,z0,z2,z3,z4,z326]),(0,[z8,z0,z2,z3,z837,z6])],[(0,[z0,z1,z2,z35,z4,z6]),(0,[z8,z0,z214,z3,z334,z6]),(0,[z8,z0,z2,z3,z4,z838]),(0,[z8,z0,z113,z3,z4,z68]),(0,[z8,z0,z2,z3,z4,z839]),(0,[z8,z233,z2,z3,z4,z373])],[(0,[z840,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z222,z473]),(0,[z8,z0,z2,z3,z4,z841])],[(0,[z8,z0,z2,z3,z4,z842]),(0,[z36,z32,z0,z2,z3,z4]),(0,[z8,z0,z2,z843,z3,z4]),(0,[z36,z8,z0,z786,z3,z4])],[(0,[z17,z1,z2,z55,z3,z4]),(0,[z71,z8,z0,z2,z144,z4]),(0,[z60,z8,z531,z176,z4,z6]),(0,[z36,z8,z0,z202,z3,z4])],[(0,[z8,z0,z2,z844,z4,z6])],[(0,[z13,z0,z2,z3,z4,z33]),(0,[z8,z0,z2,z845,z4,z6]),(0,[z8,z0,z2,z523,z28,z4]),(0,[z64,z89,z65,z3,z4,z6]),(0,[z8,z0,z2,z3,z846,z4]),(0,[z276,z847,z2,z3,z4,z6])],[(0,[z491,z8,z0,z2,z55,z4]),(0,[z8,z0,z2,z848,z4,z6]),(0,[z8,z0,z849,z3,z4,z6]),(0,[z8,z451,z2,z49,z4,z6]),(0,[z138,z8,z0,z213,z82,z6])],[(0,[z8,z0,z2,z523,z3,z4]),(0,[z8,z0,z2,z3,z4,z850]),(0,[z8,z2,z851,z176,z4,z6]),(0,[z27,z8,z0,z2,z55,z4]),(0,[z8,z0,z2,z103,z98,z4])],[(0,[z43,z1,z2,z3,z4,z9]),(0,[z8,z0,z2,z55,z295,z4])],[(0,[z256,z8,z0,z28,z4,z6]),(0,[z8,z0,z2,z3,z4,z852])],[(0,[z0,z1,z2,z3,z4,z11]),(0,[z8,z0,z2,z853,z4,z6]),(0,[z854,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z103,z4,z11]),(0,[z265,z0,z2,z3,z98,z47])],[(0,[z43,z36,z1,z2,z3,z4])],[(0,[z8,z0,z2,z834,z4,z31]),(0,[z855,z0,z2,z3,z4,z6]),(0,[z27,z8,z0,z2,z149,z4])],[(0,[z8,z0,z2,z856,z4,z6])],[(0,[z13,z0,z2,z3,z4,z58]),(0,[z0,z2,z55,z3,z74,z4])],[(0,[z857,z8,z0,z2,z3,z4]),(0,[z858,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z777,z3,z4]),(0,[z8,z0,z2,z229,z4,z406])],[(0,[z8,z0,z859,z2,z3,z4]),(0,[z860,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z28,z4,z108])],[(0,[z8,z426,z214,z3,z4,z6])],[(0,[z13,z0,z214,z3,z4,z6]),(0,[z8,z0,z2,z3,z861,z4]),(0,[z8,z0,z2,z3,z4,z862]),(0,[z396,z0,z2,z3,z215,z6]),(0,[z0,z863,z2,z3,z4,z6])],[(0,[z375,z0,z2,z249,z4,z6]),(0,[z436,z0,z2,z3,z52,z6])],[(0,[z8,z0,z864,z3,z4,z6]),(0,[z8,z2,z772,z3,z4,z6]),(0,[z8,z2,z3,z851,z4,z6]),(0,[z865,z0,z2,z3,z4,z6]),(1,[z847,z2,z3,z4,z6])],[(0,[z1,z2,z3,z105,z4,z6]),(0,[z0,z1,z2,z3,z4,z481]),(0,[z0,z1,z2,z3,z4,z246]),(0,[z127,z0,z2,z3,z4,z6]),(0,[z8,z866,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z867])],[(0,[z56,z0,z2,z3,z4,z21]),(0,[z8,z0,z2,z3,z4,z868])],[(0,[z376,z0,z2,z3,z104,z6]),(0,[z86,z8,z0,z28,z4,z20])],[(0,[z30,z1,z2,z3,z81,z6]),(0,[z0,z1,z2,z3,z4,z132]),(0,[z1,z2,z3,z4,z622,z6]),(0,[z13,z0,z2,z3,z869,z6]),(0,[z8,z0,z2,z3,z870,z6]),(0,[z8,z30,z2,z3,z139,z4]),(0,[z871,z0,z2,z3,z4,z6])],[(0,[z8,z0,z872,z2,z3,z4]),(0,[z265,z0,z2,z3,z4,z6]),(0,[z873,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z834,z3,z4]),(0,[z13,z0,z2,z3,z4,z92]),(0,[z13,z233,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z874]),(0,[z8,z0,z2,z851,z4,z6]),(0,[z8,z0,z202,z55,z3,z4]),(0,[z8,z0,z2,z55,z121,z4]),(0,[z43,z8,z2,z3,z5,z9])]],
   [[(0,[z96,z8,z2,z3,z4,z320]),(0,[z875,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z213,z4,z11])],[(0,[z56,z0,z2,z3,z4,z33]),(0,[z117,z8,z42,z3,z4,z568]),(0,[z876,z0,z2,z3,z4,z6]),(0,[z504,z8,z0,z2,z3,z435])],[(0,[z8,z0,z2,z877,z3,z4]),(0,[z96,z8,z2,z3,z105,z6]),(0,[z8,z0,z2,z878,z3,z4]),(0,[z8,z879,z2,z55,z3,z4])],[(0,[z8,z0,z2,z3,z4,z880]),(0,[z0,z2,z691,z3,z104,z6]),(1,[z8,z0,z2,z4,z881])],[(0,[z266,z1,z2,z3,z4,z6]),(0,[z267,z1,z2,z3,z4,z6]),(0,[z43,z1,z2,z3,z5,z6]),(0,[z0,z882,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z883]),(0,[z8,z0,z2,z35,z4,z405]),(0,[z36,z8,z0,z2,z4,z881])],[(0,[z8,z0,z2,z3,z4,z515]),(0,[z13,z0,z2,z3,z4,z108])],[(0,[z0,z1,z2,z3,z4,z524]),(0,[z0,z1,z2,z523,z3,z4]),(0,[z8,z1,z439,z3,z4,z6]),(0,[z40,z0,z182,z55,z3,z4]),(0,[z8,z0,z2,z884,z49,z4])],[(0,[z13,z96,z2,z3,z162,z6])],[(0,[z117,z1,z42,z3,z4,z6]),(0,[z8,z0,z2,z163,z4,z9]),(0,[z885,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z471,z47])],[(0,[z0,z2,z3,z4,z162,z31])],[],[(0,[z8,z0,z2,z886,z3,z4]),(0,[z101,z233,z2,z3,z4,z6])],[(0,[z34,z0,z54,z3,z4,z387]),(0,[z51,z0,z2,z3,z334,z6])],[(0,[z887,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z888]),(0,[z8,z0,z2,z174,z4,z11]),(0,[z0,z2,z3,z4,z175,z11]),(0,[z8,z0,z2,z4,z881,z6])],[(0,[z13,z1,z2,z3,z4,z126]),(0,[z889,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z890])],[(0,[z0,z1,z859,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z891]),(0,[z36,z8,z0,z439,z3,z4]),(0,[z8,z0,z2,z3,z4,z892]),(0,[z36,z8,z0,z2,z149,z4])],[(0,[z60,z1,z2,z176,z4,z6]),(0,[z151,z8,z0,z2,z55,z4]),(0,[z8,z0,z2,z3,z4,z893]),(0,[z8,z0,z2,z3,z4,z894]),(0,[z8,z0,z2,z83,z4,z108])],[(0,[z436,z0,z2,z3,z4,z31])],[(0,[z1,z2,z3,z4,z642,z6]),(0,[z895,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z121,z4,z9]),(0,[z62,z8,z2,z3,z4,z896])],[(0,[z8,z233,z2,z49,z4,z6])],[(0,[z61,z0,z2,z3,z4,z20])],[(0,[z0,z1,z2,z55,z4,z316]),(0,[z8,z0,z2,z3,z162,z33]),(0,[z267,z8,z2,z3,z5,z6])],[(0,[z8,z0,z2,z3,z4,z897]),(0,[z51,z0,z2,z50,z3,z4]),(0,[z8,z0,z439,z3,z4,z289]),(0,[z8,z2,z3,z139,z4,z11]),(0,[z8,z0,z128,z3,z898,z6])],[(0,[z0,z1,z2,z3,z539,z6])],[(0,[z8,z0,z2,z3,z899,z4])],[(0,[z0,z2,z3,z4,z279,z31])],[(0,[z557,z8,z42,z3,z4,z6]),(0,[z900,z8,z0,z2,z3,z4])],[(0,[z1,z2,z42,z3,z4,z126]),(0,[z901,z8,z0,z2,z480,z4]),(0,[z8,z0,z2,z3,z4,z902])],[(0,[z8,z0,z2,z3,z903,z6]),(0,[z8,z0,z2,z3,z4,z904]),(0,[z325,z0,z2,z3,z257,z6]),(0,[z8,z0,z2,z3,z4,z905]),(0,[z276,z0,z2,z3,z4,z906])],[(0,[z51,z426,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z776]),(0,[z7,z0,z2,z3,z4,z274])],[(0,[z907,z0,z2,z3,z4,z6]),(0,[z8,z0,z172,z3,z37,z6]),(0,[z112,z0,z2,z3,z4,z31]),(0,[z762,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z881])]],
   [[(0,[z8,z0,z2,z908,z4,z6]),(0,[z909,z8,z0,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z515]),(0,[z13,z0,z2,z3,z4,z910]),(1,[z0,z2,z3,z162,z31]),(0,[z0,z2,z3,z4,z911,z6])],[(0,[z13,z30,z2,z3,z81,z6]),(0,[z912,z8,z0,z2,z3,z4]),(0,[z43,z8,z2,z55,z3,z5]),(0,[z913,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z914]),(0,[z915,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z916])],[],[(0,[z543,z1,z42,z3,z4,z6]),(0,[z8,z0,z2,z229,z3,z4]),(0,[z411,z0,z2,z3,z4,z888]),(0,[z8,z116,z2,z19,z3,z4])],[(0,[z396,z0,z2,z3,z4,z568]),(0,[z325,z0,z2,z3,z4,z917]),(0,[z8,z2,z3,z4,z11,z896]),(0,[z8,z0,z2,z918,z4,z6])],[(0,[z0,z1,z2,z3,z4,z232]),(0,[z180,z0,z2,z3,z4,z20]),(0,[z8,z64,z65,z3,z4,z6])],[(0,[z8,z0,z54,z35,z4,z6]),(0,[z8,z0,z2,z3,z4,z919]),(0,[z8,z0,z2,z50,z4,z316]),(0,[z8,z0,z439,z3,z4,z6]),(0,[z434,z8,z116,z2,z3,z4])],[],[(0,[z8,z0,z2,z3,z4,z920]),(0,[z8,z0,z2,z921,z4,z31]),(0,[z922,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z923]),(0,[z8,z0,z120,z55,z83,z4])],[(0,[z8,z0,z2,z3,z4,z924])],[(0,[z8,z0,z2,z3,z765,z6]),(0,[z8,z0,z2,z3,z791,z9]),(0,[z180,z925,z2,z3,z4,z6]),(0,[z8,z0,z926,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z927]),(0,[z8,z0,z2,z163,z4,z11])],[(0,[z8,z457,z2,z35,z4,z6]),(0,[z8,z401,z2,z3,z137,z6]),(0,[z8,z0,z2,z928,z3,z4]),(0,[z8,z64,z772,z3,z4,z6])],[(0,[z0,z1,z531,z3,z4,z6]),(0,[z8,z929,z2,z3,z4,z6]),(0,[z8,z0,z2,z19,z257,z6])],[(0,[z13,z0,z2,z3,z4,z126]),(0,[z8,z0,z2,z3,z4,z930]),(0,[z8,z233,z2,z3,z4,z931]),(0,[z36,z8,z0,z932,z3,z4])],[(0,[z8,z0,z2,z3,z4,z933]),(0,[z8,z0,z2,z934,z4,z6]),(0,[z8,z0,z2,z3,z344,z555]),(0,[z8,z327,z2,z3,z4,z252])],[(0,[z198,z0,z2,z3,z4,z20]),(0,[z138,z8,z0,z3,z82,z9]),(0,[z935,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z498,z4,z20]),(0,[z936,z0,z2,z3,z4,z6])],[(0,[z13,z0,z202,z3,z4,z6]),(0,[z546,z0,z2,z3,z4,z31]),(0,[z8,z0,z333,z55,z83,z4])],[(0,[z8,z0,z2,z3,z937,z6]),(0,[z8,z0,z2,z3,z4,z568]),(0,[z127,z0,z2,z174,z4,z6])],[(0,[z8,z0,z2,z480,z539,z6])],[(0,[z396,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z121,z4,z11])],[(0,[z8,z457,z2,z3,z4,z11]),(0,[z0,z182,z110,z3,z4,z6]),(0,[z39,z0,z2,z3,z104,z153]),(0,[z0,z89,z2,z3,z4,z9]),(0,[z8,z0,z439,z3,z81,z6])],[(0,[z8,z0,z2,z3,z4,z938]),(1,[z0,z2,z3,z4,z720]),(0,[z8,z0,z2,z939,z3,z4]),(0,[z8,z0,z2,z760,z4,z11])],[(0,[z56,z0,z2,z3,z162,z6]),(0,[z8,z0,z2,z3,z4,z940]),(0,[z8,z0,z357,z55,z3,z4])],[(0,[z8,z0,z941,z3,z4,z6]),(0,[z1,z2,z3,z679,z4,z6]),(0,[z1,z2,z3,z81,z4,z9]),(0,[z8,z0,z2,z942,z3,z4])],[(0,[z34,z36,z0,z54,z3,z4]),(0,[z8,z0,z2,z3,z943,z6]),(0,[z8,z0,z2,z3,z944,z4]),(0,[z180,z945,z2,z3,z4,z6]),(0,[z269,z8,z0,z2,z3,z466])],[(0,[z8,z0,z2,z3,z4,z946]),(0,[z0,z346,z2,z3,z4,z31])],[(0,[z0,z1,z2,z834,z4,z126]),(0,[z8,z0,z2,z3,z4,z947]),(0,[z8,z0,z2,z3,z4,z948]),(0,[z64,z346,z2,z3,z4,z6]),(0,[z8,z0,z949,z3,z4,z6])],[(0,[z13,z1,z2,z3,z105,z6]),(0,[z8,z0,z77,z3,z4,z68]),(0,[z227,z0,z2,z3,z4,z20]),(0,[z950,z0,z2,z3,z4,z6])],[(0,[z507,z8,z0,z2,z224,z6]),(0,[z945,z2,z3,z28,z4,z6])]],
   [[(0,[z8,z0,z2,z3,z4,z285])],[(0,[z8,z0,z2,z3,z4,z720]),(0,[z8,z65,z772,z3,z4,z6]),(0,[z8,z0,z2,z951,z4,z9]),(0,[z8,z0,z952,z3,z4,z6])],[(0,[z13,z0,z2,z3,z4,z953]),(0,[z8,z0,z2,z3,z4,z954]),(0,[z8,z233,z2,z3,z4,z20])],[(0,[z13,z0,z2,z55,z3,z162]),(0,[z71,z0,z540,z2,z76,z4]),(0,[z8,z155,z2,z3,z4,z9]),(0,[z8,z0,z2,z55,z28,z4]),(0,[z955,z0,z2,z3,z4,z6])],[(0,[z8,z1,z2,z3,z139,z4]),(0,[z8,z345,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z956])],[(0,[z8,z0,z2,z55,z3,z4]),(0,[z0,z957,z2,z3,z4,z6]),(0,[z318,z0,z2,z55,z3,z4])],[(0,[z8,z426,z110,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z958]),(0,[z8,z0,z2,z959,z3,z4])],[(0,[z123,z1,z2,z3,z4,z126]),(0,[z0,z1,z2,z149,z4,z6]),(0,[z0,z156,z2,z44,z3,z4])],[(0,[z1,z2,z159,z3,z176,z4]),(0,[z8,z518,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z960])],[(0,[z60,z8,z2,z851,z4,z6]),(0,[z8,z0,z2,z3,z4,z961])],[(0,[z51,z0,z2,z3,z4,z145]),(0,[z332,z8,z42,z3,z4,z6]),(0,[z8,z0,z42,z55,z28,z4]),(0,[z8,z0,z2,z55,z490,z4])],[],[(0,[z8,z0,z2,z3,z962,z4]),(0,[z0,z2,z3,z37,z104,z31])],[(0,[z0,z73,z2,z55,z3,z4])],[(0,[z0,z1,z2,z963,z4,z6]),(0,[z8,z30,z2,z3,z279,z6]),(0,[z0,z370,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z964,z6])],[(0,[z0,z1,z2,z3,z4,z568]),(0,[z36,z1,z2,z3,z81,z4]),(0,[z8,z0,z2,z3,z258,z47]),(0,[z8,z0,z965,z2,z3,z4])],[(0,[z8,z0,z2,z3,z4,z966]),(0,[z8,z426,z2,z3,z137,z6])],[(0,[z0,z2,z967,z3,z4,z6]),(0,[z8,z0,z2,z3,z968,z9])],[(0,[z13,z0,z2,z3,z4,z252]),(0,[z0,z2,z3,z74,z4,z20]),(0,[z43,z346,z2,z3,z4,z6]),(0,[z0,z2,z3,z969,z4,z175])],[(0,[z36,z17,z1,z2,z3,z4]),(0,[z8,z0,z970,z3,z4,z6]),(0,[z8,z0,z2,z814,z213,z4])],[(0,[z8,z0,z2,z3,z4,z971]),(0,[z8,z972,z2,z3,z4,z6]),(0,[z8,z0,z2,z367,z4,z20]),(0,[z8,z0,z2,z3,z973,z4]),(0,[z138,z8,z0,z3,z82,z11]),(0,[z8,z0,z2,z974,z28,z4]),(0,[z8,z975,z2,z3,z4,z6]),(0,[z7,z8,z0,z3,z4,z90]),(0,[z0,z2,z3,z492,z4,z274])],[(0,[z8,z401,z2,z3,z4,z6]),(0,[z254,z0,z2,z3,z4,z20])],[],[(0,[z325,z0,z357,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z976]),(0,[z802,z0,z2,z3,z4,z11]),(0,[z0,z977,z2,z3,z4,z6])],[(0,[z13,z1,z2,z3,z4,z6]),(0,[z71,z0,z2,z76,z4,z20]),(0,[z85,z0,z2,z3,z4,z978]),(0,[z8,z451,z2,z3,z4,z6]),(0,[z318,z451,z2,z3,z4,z6])],[],[(0,[z8,z0,z2,z3,z4,z979])],[(0,[z78,z1,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z4,z320]),(0,[z8,z0,z2,z3,z4,z980])],[(0,[z8,z0,z2,z981,z3,z4]),(0,[z0,z982,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z983]),(0,[z8,z0,z984,z3,z4,z6])],[(0,[z13,z0,z2,z3,z105,z6]),(0,[z1,z2,z3,z4,z649,z6]),(0,[z8,z0,z2,z3,z827,z6])],[(0,[z361,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z35,z4,z11]),(0,[z8,z0,z985,z2,z3,z4]),(0,[z318,z0,z2,z3,z4,z373]),(0,[z8,z0,z2,z3,z4,z373])]],
   [[(0,[z0,z1,z2,z55,z3,z4]),(0,[z293,z0,z2,z3,z4,z473]),(0,[z795,z8,z0,z2,z49,z4])],[(0,[z491,z8,z0,z2,z76,z4]),(0,[z8,z0,z439,z174,z4,z6])],[],[(0,[z13,z7,z0,z3,z4,z90])],[(0,[z8,z0,z2,z986,z3,z4]),(0,[z8,z451,z2,z3,z4,z31]),(0,[z8,z30,z2,z3,z679,z6]),(0,[z8,z0,z2,z3,z139,z4]),(0,[z8,z0,z2,z3,z4,z813])],[(0,[z8,z230,z2,z3,z4,z9])],[(0,[z1,z2,z42,z3,z4,z6]),(0,[z151,z1,z2,z176,z4,z6]),(0,[z0,z2,z3,z104,z82,z31])],[(0,[z43,z1,z2,z3,z4,z513]),(0,[z8,z0,z2,z3,z4,z21]),(0,[z8,z0,z2,z3,z835,z6]),(0,[z8,z0,z2,z3,z334,z6]),(0,[z8,z2,z3,z277,z4,z11]),(0,[z8,z209,z2,z3,z4,z11])],[(0,[z8,z0,z2,z987,z480,z4]),(0,[z8,z0,z2,z3,z4,z988]),(0,[z8,z0,z2,z3,z4,z989]),(0,[z0,z2,z3,z4,z6,z990])],[(0,[z13,z0,z2,z3,z4,z289]),(0,[z13,z327,z2,z3,z4,z11]),(0,[z8,z991,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z992]),(0,[z13,z96,z2,z3,z4,z31]),(0,[z29,z8,z0,z2,z3,z4])],[(0,[z8,z0,z3,z4,z898,z6])],[(0,[z8,z0,z2,z3,z4,z24]),(0,[z8,z64,z384,z3,z4,z6]),(0,[z127,z0,z2,z3,z4,z9]),(0,[z8,z0,z303,z3,z4,z223])],[(0,[z8,z0,z2,z3,z4,z33]),(0,[z13,z0,z357,z3,z4,z6]),(0,[z0,z2,z3,z4,z20,z285]),(0,[z993,z0,z2,z3,z4,z6])],[(0,[z0,z1,z970,z3,z4,z6]),(0,[z13,z17,z2,z19,z4,z6]),(0,[z13,z0,z2,z146,z3,z4]),(0,[z8,z345,z2,z3,z4,z387]),(0,[z0,z414,z2,z3,z4,z31]),(0,[z60,z8,z0,z2,z50,z4]),(0,[z0,z2,z3,z4,z20,z720]),(0,[z8,z0,z2,z994,z4,z6]),(0,[z8,z0,z2,z55,z292,z4]),(0,[z8,z0,z2,z3,z995,z6]),(0,[z185,z8,z0,z3,z282,z4])],[(0,[z0,z1,z2,z3,z4,z971]),(0,[z8,z0,z2,z3,z539,z9]),(0,[z7,z8,z0,z103,z4,z90])],[(0,[z13,z0,z2,z3,z301,z4]),(0,[z8,z0,z2,z3,z4,z996]),(0,[z343,z8,z0,z2,z4,z456]),(0,[z265,z0,z2,z3,z4,z9])],[(0,[z8,z0,z2,z50,z3,z4]),(0,[z620,z8,z0,z2,z224,z6]),(0,[z8,z0,z2,z3,z4,z409])],[(0,[z1,z2,z665,z3,z4,z6]),(0,[z43,z1,z2,z3,z4,z20]),(0,[z13,z0,z18,z3,z4,z68]),(0,[z436,z0,z2,z3,z105,z6]),(0,[z51,z0,z2,z3,z4,z173]),(0,[z8,z0,z2,z3,z4,z997]),(0,[z32,z0,z2,z3,z4,z222]),(0,[z8,z0,z2,z321,z28,z4]),(0,[z196,z8,z0,z2,z3,z511])],[(0,[z13,z0,z2,z3,z998,z6]),(0,[z8,z0,z2,z3,z4,z999]),(0,[z319,z8,z0,z2,z3,z4])],[],[(0,[z36,z8,z0,z2,z3,z334]),(0,[z8,z0,z2,z778,z4,z6]),(0,[z8,z0,z2,z3,z4,z1000])],[(0,[z13,z0,z2,z3,z1001,z6]),(0,[z8,z0,z2,z3,z257,z20]),(0,[z8,z0,z2,z3,z1002,z4])],[(0,[z32,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z1003])],[(0,[z8,z426,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z215,z9]),(0,[z8,z451,z2,z3,z37,z6]),(0,[z36,z8,z0,z2,z191,z4])],[(0,[z13,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z1004,z6]),(0,[z8,z565,z2,z3,z4,z11]),(0,[z1005,z0,z2,z3,z4,z6]),(0,[z43,z8,z2,z3,z5,z513])],[(0,[z8,z0,z100,z3,z4,z188]),(0,[z8,z0,z2,z3,z4,z1006])],[(0,[z13,z27,z0,z2,z3,z4]),(0,[z13,z0,z2,z3,z321,z4]),(0,[z8,z0,z214,z3,z4,z72])],[(1,[z8,z772,z3,z4,z6])],[(0,[z181,z1,z2,z3,z4,z6]),(0,[z119,z8,z2,z3,z52,z6]),(0,[z8,z0,z2,z1007,z4,z9])],[(0,[z401,z1,z2,z3,z4,z6]),(0,[z40,z0,z182,z3,z4,z20])],[(0,[z13,z0,z2,z3,z4,z222]),(0,[z0,z1,z2,z3,z139,z4]),(0,[z8,z0,z2,z1008,z4,z6]),(0,[z8,z2,z42,z3,z139,z4]),(0,[z78,z0,z2,z3,z4,z261])]],
   [[(0,[z8,z0,z2,z3,z869,z6]),(0,[z1009,z8,z0,z2,z3,z4])],[(0,[z13,z0,z2,z3,z1010,z6]),(0,[z8,z0,z2,z3,z4,z1011])],[(0,[z390,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z334,z6]),(0,[z8,z0,z2,z3,z4,z1012])],[(0,[z1,z116,z2,z3,z4,z6]),(0,[z1013,z8,z0,z2,z3,z4])],[(0,[z8,z0,z2,z3,z4,z1014]),(0,[z0,z2,z94,z3,z162,z6]),(0,[z8,z0,z2,z3,z1015,z4]),(0,[z0,z2,z3,z104,z224,z31]),(0,[z43,z8,z2,z3,z5,z20])],[(0,[z8,z0,z214,z3,z4,z31]),(0,[z8,z0,z531,z3,z4,z9]),(0,[z411,z0,z2,z3,z1016,z6]),(0,[z8,z0,z2,z1017,z4,z6]),(0,[z1018,z8,z0,z2,z3,z4])],[(0,[z101,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z83,z321,z4]),(0,[z138,z8,z0,z3,z58,z82])],[(0,[z0,z1,z2,z3,z4,z24]),(0,[z296,z0,z2,z3,z104,z6]),(0,[z39,z0,z2,z3,z104,z6]),(0,[z78,z0,z2,z3,z4,z31])],[(0,[z1,z42,z3,z4,z82,z6]),(0,[z36,z8,z0,z952,z3,z4])],[(0,[z0,z2,z3,z4,z33,z31]),(0,[z8,z0,z2,z3,z1019,z6]),(0,[z117,z8,z42,z3,z4,z20]),(0,[z8,z0,z439,z121,z4,z6])],[(0,[z8,z0,z1020,z3,z4,z6]),(0,[z8,z0,z110,z3,z4,z20]),(0,[z8,z0,z1021,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1022])],[(0,[z8,z0,z2,z3,z4,z1023]),(0,[z8,z0,z1024,z3,z4,z6]),(0,[z8,z0,z1025,z2,z3,z4]),(0,[z8,z0,z2,z213,z4,z373])],[(0,[z0,z1,z2,z3,z4,z409]),(0,[z0,z1,z2,z50,z3,z4]),(0,[z13,z0,z2,z1026,z3,z4])],[(0,[z8,z233,z2,z3,z4,z31]),(0,[z8,z0,z2,z121,z4,z513]),(0,[z8,z1027,z2,z3,z4,z6])],[(0,[z1,z2,z3,z139,z4,z6]),(0,[z8,z0,z2,z1028,z3,z4]),(0,[z40,z0,z182,z3,z4,z173]),(0,[z8,z0,z2,z1029,z3,z4]),(0,[z8,z0,z531,z3,z4,z508]),(0,[z8,z0,z2,z49,z4,z6]),(0,[z318,z0,z2,z49,z4,z6]),(0,[z8,z0,z2,z1030,z3,z4])],[(0,[z127,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z1031])],[(0,[z13,z96,z2,z3,z4,z283]),(0,[z230,z2,z44,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1032])],[(0,[z123,z1,z2,z3,z4,z6]),(0,[z60,z8,z2,z176,z4,z20]),(0,[z8,z0,z2,z3,z4,z1033])],[],[(0,[z13,z0,z2,z3,z4,z192]),(0,[z1034,z8,z0,z2,z3,z4]),(0,[z51,z0,z2,z3,z52,z6]),(0,[z8,z0,z1035,z2,z3,z4]),(0,[z336,z0,z2,z3,z52,z6]),(0,[z265,z0,z2,z3,z4,z11])],[(0,[z8,z0,z2,z3,z4,z1036]),(0,[z13,z0,z2,z3,z162,z9]),(0,[z13,z0,z2,z103,z4,z6]),(0,[z8,z0,z2,z3,z137,z20])],[],[(0,[z36,z123,z1,z2,z3,z4]),(0,[z56,z0,z2,z3,z4,z222]),(0,[z8,z17,z2,z177,z4,z6]),(0,[z1037,z8,z0,z2,z3,z4]),(0,[z1038,z0,z2,z3,z4,z6])],[(0,[z23,z8,z0,z2,z144,z4]),(0,[z119,z8,z2,z3,z4,z31])],[(0,[z36,z8,z0,z110,z3,z4])],[(0,[z1039,z8,z0,z2,z3,z6])],[(0,[z543,z0,z54,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1040]),(0,[z1041,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z359,z55,z4])],[(0,[z1042,z8,z0,z2,z3,z4]),(0,[z1043,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z4,z281])],[(0,[z1,z2,z3,z4,z11,z9]),(0,[z96,z436,z2,z3,z4,z6]),(0,[z8,z0,z2,z1044,z4,z6]),(0,[z119,z8,z2,z3,z4,z130]),(0,[z287,z8,z0,z2,z55,z4]),(0,[z319,z8,z358,z2,z3,z4])],[(0,[z1,z2,z3,z37,z81,z6]),(0,[z71,z0,z214,z76,z4,z6]),(0,[z278,z0,z2,z3,z4,z31]),(0,[z417,z8,z0,z3,z4,z201]),(0,[z86,z8,z0,z55,z28,z4])],[(0,[z8,z0,z2,z149,z4,z9]),(0,[z8,z451,z2,z3,z82,z6])],[(0,[z0,z1,z2,z3,z4,z1014]),(0,[z1045,z0,z2,z3,z4,z6]),(0,[z8,z0,z587,z2,z3,z4]),(0,[z1046,z0,z2,z3,z4,z6]),(0,[z8,z30,z2,z55,z3,z81]),(0,[z8,z0,z2,z3,z806,z6])]],
   [[(0,[z8,z0,z54,z55,z28,z4]),(0,[z56,z0,z2,z3,z4,z130]),(0,[z8,z440,z65,z3,z4,z6]),(0,[z8,z2,z3,z4,z262,z11])],[(0,[z8,z0,z2,z3,z105,z20]),(0,[z233,z1047,z2,z3,z4,z6])],[(0,[z13,z319,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z1048,z6]),(0,[z0,z2,z3,z4,z175,z989])],[(0,[z408,z8,z0,z2,z3,z95])],[(0,[z8,z0,z2,z3,z4,z910]),(0,[z8,z0,z2,z3,z4,z145])],[(0,[z8,z0,z2,z3,z162,z6]),(0,[z17,z1,z2,z3,z4,z222]),(0,[z0,z1,z1020,z3,z4,z6]),(0,[z0,z1,z2,z3,z1049,z4]),(0,[z13,z0,z2,z213,z4,z6]),(0,[z101,z0,z2,z3,z37,z6])],[(0,[z8,z0,z1050,z3,z4,z6])],[(0,[z1,z2,z3,z121,z4,z6]),(0,[z0,z2,z3,z4,z1051,z6]),(0,[z8,z0,z2,z55,z4,z640]),(0,[z8,z1052,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z1053,z6]),(0,[z8,z457,z2,z55,z3,z4]),(0,[z389,z0,z2,z3,z4,z20])],[(0,[z34,z0,z54,z3,z4,z6]),(0,[z8,z0,z182,z55,z28,z4]),(0,[z8,z2,z3,z4,z67,z9]),(0,[z8,z0,z2,z3,z1054,z4]),(0,[z8,z0,z2,z3,z4,z931])],[(0,[z17,z1,z2,z3,z4,z31]),(0,[z0,z2,z624,z3,z4,z20])],[(0,[z8,z0,z2,z3,z1055,z6]),(0,[z8,z0,z2,z3,z4,z1056]),(0,[z0,z2,z3,z4,z175,z409])],[(1,[z1,z2,z3,z4,z252]),(0,[z549,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z1057,z4,z6]),(0,[z8,z0,z2,z3,z4,z1058]),(0,[z8,z0,z2,z3,z4,z153]),(0,[z1059,z8,z0,z2,z3,z4]),(0,[z8,z0,z439,z3,z104,z6]),(0,[z62,z8,z2,z3,z4,z320]),(0,[z8,z0,z820,z28,z4,z6]),(0,[z8,z0,z2,z3,z4,z1060])],[(0,[z199,z1,z2,z3,z81,z6]),(0,[z8,z0,z2,z3,z4,z1061]),(0,[z8,z0,z2,z3,z4,z1062]),(0,[z51,z0,z2,z3,z4,z31]),(0,[z336,z0,z2,z3,z4,z31]),(0,[z396,z0,z2,z3,z4,z20])],[(0,[z60,z8,z2,z3,z139,z4])],[(0,[z0,z1,z2,z3,z4,z1036]),(0,[z8,z0,z2,z3,z1063,z6]),(0,[z36,z8,z230,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1064])],[(0,[z8,z0,z2,z3,z4,z1065]),(0,[z8,z30,z2,z3,z81,z31]),(0,[z8,z0,z357,z3,z4,z20]),(0,[z1066,z8,z0,z2,z367,z4])],[(0,[z0,z2,z3,z4,z21,z126]),(0,[z8,z1067,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1068])],[(0,[z101,z0,z2,z213,z4,z6]),(0,[z8,z0,z2,z3,z4,z1069])],[(0,[z13,z0,z2,z174,z4,z6]),(0,[z0,z2,z3,z334,z104,z6])],[(0,[z8,z0,z2,z1070,z3,z4]),(0,[z13,z0,z2,z3,z4,z405]),(0,[z8,z0,z2,z3,z4,z798]),(0,[z8,z0,z2,z3,z4,z1071])],[(0,[z8,z1,z2,z3,z4,z252])],[(1,[z1,z2,z3,z4,z320]),(0,[z39,z230,z2,z3,z4,z6]),(0,[z8,z0,z1072,z2,z3,z4])],[(0,[z8,z0,z2,z1073,z4,z6]),(0,[z491,z8,z0,z2,z4,z114])],[(0,[z1074,z8,z0,z2,z3,z4]),(1,[z1,z2,z3,z105,z6]),(0,[z8,z0,z2,z3,z1075,z6]),(0,[z8,z0,z2,z3,z1076,z4]),(0,[z27,z8,z0,z2,z4,z114]),(0,[z781,z0,z2,z55,z3,z4])],[(0,[z8,z0,z3,z898,z82,z6])],[(0,[z0,z1,z587,z2,z3,z4]),(0,[z180,z0,z110,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1077]),(0,[z8,z0,z2,z3,z1078,z6])],[(0,[z8,z0,z2,z3,z178,z9]),(0,[z8,z0,z2,z3,z4,z210]),(0,[z85,z0,z2,z3,z217,z6]),(0,[z8,z64,z65,z3,z4,z11])],[(0,[z8,z0,z439,z3,z4,z11]),(0,[z1079,z0,z2,z3,z4,z6]),(0,[z8,z451,z2,z3,z4,z412]),(0,[z8,z0,z2,z3,z1080,z4])],[],[(0,[z8,z0,z2,z3,z217,z6]),(0,[z8,z0,z2,z159,z83,z4])],[(0,[z0,z1,z2,z3,z4,z145]),(0,[z1,z2,z3,z81,z4,z20])]],
   [[(0,[z0,z1,z2,z3,z162,z6])],[(0,[z8,z0,z202,z3,z4,z31])],[(0,[z0,z2,z3,z52,z162,z6]),(0,[z8,z509,z65,z3,z4,z6]),(0,[z516,z8,z0,z3,z82,z6]),(0,[z319,z8,z0,z2,z4,z284]),(0,[z415,z8,z0,z2,z3,z271]),(0,[z86,z8,z0,z28,z4,z6]),(0,[z138,z8,z451,z3,z82,z6])],[],[(0,[z151,z0,z1,z2,z55,z4]),(0,[z0,z2,z3,z4,z519,z126]),(0,[z1081,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1082]),(0,[z0,z73,z2,z3,z4,z20]),(0,[z86,z0,z74,z28,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1083]),(0,[z8,z0,z42,z3,z217,z6]),(0,[z0,z167,z2,z3,z4,z9])],[(0,[z96,z8,z116,z2,z3,z4]),(0,[z8,z0,z2,z3,z165,z6])],[(0,[z1084,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z176,z257,z6]),(0,[z101,z0,z2,z3,z4,z707])],[(0,[z1,z2,z3,z176,z4,z9]),(0,[z8,z0,z2,z55,z480,z4]),(0,[z8,z0,z2,z1085,z3,z4])],[(0,[z40,z0,z182,z3,z4,z31]),(0,[z36,z318,z0,z2,z3,z4]),(0,[z8,z0,z2,z55,z213,z4])],[(0,[z8,z0,z2,z3,z4,z1086]),(0,[z13,z2,z3,z4,z11,z9]),(0,[z13,z14,z0,z2,z3,z95]),(0,[z13,z0,z2,z3,z4,z473]),(0,[z346,z2,z3,z81,z4,z6]),(0,[z8,z1087,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z38,z4]),(0,[z8,z0,z2,z3,z4,z1088]),(0,[z10,z8,z0,z2,z55,z224])],[(0,[z8,z0,z2,z3,z4,z173])],[(0,[z1089,z0,z2,z3,z4,z6])],[],[(0,[z61,z0,z357,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1090]),(0,[z8,z0,z2,z55,z75,z133]),(0,[z1091,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z1092,z4])],[(0,[z1093,z1,z2,z3,z4,z6]),(0,[z43,z1094,z2,z3,z4,z6]),(0,[z13,z0,z2,z163,z4,z6]),(0,[z0,z2,z3,z4,z280,z31]),(0,[z8,z0,z2,z1095,z4,z6]),(0,[z8,z945,z2,z3,z4,z6])],[(0,[z411,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z1096])],[(0,[z8,z0,z2,z3,z4,z1097])],[(0,[z1,z2,z75,z176,z4,z6]),(0,[z30,z346,z2,z3,z81,z6]),(0,[z1098,z8,z0,z2,z3,z4])],[(0,[z8,z0,z2,z3,z4,z252]),(0,[z8,z0,z1099,z3,z4,z6]),(0,[z8,z0,z2,z3,z137,z72]),(0,[z325,z0,z2,z3,z4,z9]),(0,[z36,z8,z0,z984,z3,z4]),(0,[z36,z1100,z0,z2,z3,z4])],[(0,[z1101,z8,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z20]),(0,[z1102,z0,z2,z3,z4,z6]),(0,[z8,z0,z1103,z3,z4,z6]),(0,[z36,z8,z0,z2,z4,z114])],[(0,[z8,z0,z2,z3,z4,z1104]),(0,[z8,z0,z2,z3,z4,z1105])],[(0,[z8,z0,z2,z1106,z4,z6]),(0,[z64,z1,z2,z3,z4,z126]),(0,[z8,z0,z2,z1107,z3,z4]),(0,[z8,z0,z2,z1108,z4,z6]),(0,[z8,z2,z42,z3,z217,z6])],[(0,[z8,z0,z2,z3,z4,z1109]),(0,[z8,z0,z2,z3,z4,z1110]),(0,[z8,z0,z1111,z2,z3,z4])],[(0,[z61,z0,z2,z3,z4,z6]),(0,[z13,z0,z2,z121,z4,z6]),(0,[z276,z0,z2,z3,z4,z1112]),(0,[z0,z1113,z2,z3,z4,z6])],[(0,[z13,z0,z2,z3,z4,z412]),(0,[z13,z457,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1114]),(0,[z190,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z367,z217,z6])],[(0,[z8,z0,z2,z3,z4,z1115])],[(0,[z1,z2,z3,z277,z4,z6]),(0,[z374,z0,z2,z3,z4,z31]),(0,[z325,z0,z2,z3,z4,z508]),(0,[z8,z0,z2,z834,z4,z9]),(0,[z8,z0,z2,z3,z4,z1116])],[(0,[z8,z0,z2,z1117,z3,z4]),(0,[z8,z0,z2,z4,z726,z31]),(0,[z8,z0,z2,z3,z4,z1118]),(0,[z8,z0,z1119,z2,z3,z4]),(0,[z8,z602,z2,z3,z4,z11]),(0,[z138,z8,z0,z3,z82,z373])]],
   [[(0,[z1,z2,z3,z4,z279,z6]),(0,[z40,z0,z2,z3,z321,z4]),(0,[z0,z1120,z2,z3,z4,z6])],[(0,[z13,z0,z2,z3,z4,z764]),(0,[z8,z0,z2,z3,z1121,z4]),(0,[z8,z0,z2,z55,z103,z4]),(0,[z0,z1122,z2,z3,z4,z6])],[(0,[z506,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1123]),(0,[z8,z0,z65,z55,z28,z4]),(0,[z127,z0,z439,z3,z4,z6])],[(0,[z509,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1124]),(0,[z1125,z8,z0,z2,z3,z4])],[(0,[z34,z0,z54,z3,z4,z405]),(0,[z276,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z159,z28,z4]),(0,[z1126,z276,z2,z3,z4,z6])],[(0,[z0,z1127,z2,z3,z4,z6])],[(0,[z365,z1,z2,z3,z4,z6]),(0,[z36,z8,z345,z2,z3,z4]),(0,[z8,z0,z2,z3,z1128,z4]),(0,[z8,z0,z2,z3,z4,z1129]),(0,[z127,z0,z2,z3,z4,z513])],[(0,[z0,z1,z2,z3,z4,z173]),(0,[z8,z0,z1130,z2,z3,z4]),(0,[z8,z0,z2,z3,z1131,z4])],[(0,[z78,z96,z2,z3,z4,z6]),(0,[z8,z0,z2,z213,z4,z20]),(0,[z8,z0,z2,z144,z4,z316]),(0,[z0,z167,z2,z3,z4,z11]),(0,[z8,z0,z2,z55,z49,z4]),(0,[z0,z2,z55,z3,z4,z175])],[(0,[z13,z36,z0,z2,z55,z4]),(0,[z101,z0,z2,z3,z4,z412])],[(0,[z8,z401,z2,z3,z4,z11]),(0,[z8,z230,z2,z3,z4,z20])],[(0,[z112,z0,z2,z3,z4,z473]),(0,[z8,z0,z2,z3,z4,z1132]),(0,[z8,z0,z2,z1133,z3,z4]),(0,[z287,z8,z0,z2,z3,z4]),(0,[z0,z2,z3,z4,z755,z6])],[(0,[z8,z0,z2,z3,z105,z31]),(0,[z180,z0,z2,z3,z4,z6])],[(0,[z518,z1,z2,z3,z4,z6]),(0,[z71,z0,z110,z76,z4,z6]),(0,[z1134,z8,z0,z2,z3,z4]),(0,[z327,z167,z2,z3,z4,z11])],[(0,[z13,z1,z2,z3,z4,z11]),(0,[z43,z1,z2,z3,z4,z126]),(0,[z0,z2,z3,z4,z274,z31]),(0,[z0,z89,z2,z3,z4,z1135]),(0,[z8,z0,z1136,z2,z3,z4])],[(0,[z199,z0,z2,z3,z519,z6]),(0,[z8,z0,z2,z3,z4,z1137]),(0,[z8,z782,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1138])],[(0,[z8,z0,z2,z3,z4,z1139]),(0,[z8,z401,z2,z3,z4,z446]),(0,[z8,z0,z1140,z2,z3,z4])],[(0,[z8,z0,z2,z49,z4,z412])],[(0,[z43,z1,z202,z3,z4,z6]),(0,[z0,z2,z3,z4,z720,z31]),(0,[z514,z8,z0,z28,z4,z6]),(0,[z8,z0,z2,z3,z4,z1141]),(0,[z8,z0,z80,z3,z4,z68]),(0,[z36,z0,z2,z3,z4,z1142])],[(0,[z13,z0,z2,z3,z105,z11]),(0,[z13,z0,z2,z3,z791,z6]),(0,[z36,z61,z0,z2,z3,z4])],[(0,[z13,z0,z2,z3,z4,z508]),(0,[z8,z0,z2,z480,z4,z20]),(0,[z389,z0,z2,z3,z4,z92]),(0,[z227,z327,z2,z3,z4,z11])],[(0,[z0,z2,z54,z3,z178,z6]),(1,[z8,z2,z3,z1143,z6]),(0,[z8,z0,z2,z3,z4,z1144])],[(0,[z1,z2,z3,z4,z6,z320]),(0,[z51,z0,z110,z3,z4,z6]),(0,[z51,z0,z2,z3,z52,z468]),(0,[z0,z2,z3,z4,z175,z20]),(0,[z8,z0,z2,z3,z4,z1145])],[(0,[z198,z0,z2,z3,z4,z6]),(0,[z17,z1,z2,z3,z4,z397]),(0,[z71,z0,z2,z76,z137,z6]),(0,[z8,z0,z2,z3,z4,z1146]),(0,[z8,z0,z2,z1147,z4,z6])],[(0,[z0,z2,z3,z344,z104,z31]),(0,[z396,z0,z2,z3,z4,z31]),(0,[z325,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z1148,z4])],[(0,[z85,z0,z2,z3,z4,z6]),(0,[z445,z0,z2,z3,z105,z6]),(0,[z8,z0,z2,z3,z4,z1149]),(0,[z8,z0,z2,z4,z881,z316])],[(0,[z8,z0,z2,z55,z3,z137]),(0,[z0,z2,z3,z4,z1150,z6])],[(0,[z1,z2,z42,z3,z4,z11]),(0,[z8,z0,z357,z3,z4,z31]),(0,[z8,z0,z1151,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1152])],[(0,[z8,z0,z2,z3,z334,z11])],[(0,[z0,z1,z2,z3,z4,z1123]),(0,[z8,z0,z1,z2,z834,z4]),(0,[z1153,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z72]),(0,[z8,z0,z2,z3,z215,z20]),(0,[z8,z0,z2,z3,z4,z1154])],[(0,[z10,z36,z8,z0,z2,z224])],[(0,[z8,z0,z2,z3,z4,z1155]),(0,[z8,z0,z2,z3,z4,z261]),(0,[z436,z0,z2,z3,z4,z9])]],
   [[(0,[z595,z1,z2,z3,z4,z6]),(0,[z127,z0,z2,z55,z3,z4]),(0,[z0,z2,z3,z4,z1156,z6])],[(0,[z0,z1,z2,z159,z3,z4]),(0,[z8,z0,z2,z1157,z4,z6]),(0,[z8,z772,z42,z3,z4,z6]),(0,[z8,z0,z357,z176,z4,z6])],[(0,[z8,z0,z1158,z3,z4,z6]),(0,[z8,z0,z2,z3,z334,z446]),(0,[z8,z1159,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z20,z252]),(0,[z93,z8,z0,z80,z3,z4])],[(0,[z123,z1,z2,z3,z4,z9])],[(0,[z227,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z1010,z6]),(0,[z13,z0,z2,z35,z4,z6]),(0,[z8,z0,z2,z3,z4,z1160]),(0,[z43,z8,z202,z3,z5,z6]),(0,[z8,z0,z2,z3,z248,z107]),(0,[z1161,z8,z0,z2,z3,z4]),(0,[z265,z0,z2,z55,z3,z4])],[(0,[z96,z8,z439,z3,z4,z6]),(0,[z8,z0,z2,z3,z416,z474])],[(0,[z8,z0,z2,z3,z4,z1162]),(0,[z8,z0,z2,z55,z3,z257]),(0,[z1163,z8,z0,z2,z3,z4])],[(0,[z8,z0,z2,z3,z4,z31]),(0,[z7,z0,z1,z3,z4,z90]),(0,[z1164,z0,z2,z3,z4,z6]),(0,[z8,z1165,z2,z3,z4,z6]),(0,[z318,z0,z2,z3,z4,z31]),(0,[z10,z8,z0,z2,z224,z31])],[],[(0,[z343,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1166]),(0,[z8,z0,z2,z3,z4,z1167])],[(0,[z8,z345,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z1168,z4]),(0,[z0,z882,z2,z55,z3,z4])],[(0,[z8,z0,z2,z3,z4,z1169])],[(0,[z350,z1,z2,z3,z4,z6]),(0,[z34,z457,z54,z3,z4,z6]),(0,[z8,z0,z2,z3,z1170,z6]),(0,[z8,z1171,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z130]),(0,[z8,z0,z2,z3,z4,z1172]),(0,[z0,z945,z2,z3,z4,z6])],[(0,[z8,z426,z2,z3,z4,z11]),(0,[z1173,z8,z0,z2,z3,z4]),(0,[z36,z8,z0,z2,z154,z4])],[(0,[z13,z0,z2,z3,z4,z11]),(0,[z138,z8,z0,z49,z82,z6])],[(0,[z8,z0,z2,z1026,z3,z4]),(0,[z0,z73,z2,z3,z4,z31])],[(0,[z293,z0,z2,z3,z4,z285]),(0,[z8,z0,z2,z3,z4,z1174])],[(0,[z60,z8,z2,z176,z257,z6]),(0,[z8,z698,z2,z3,z4,z11])],[(0,[z8,z0,z2,z3,z4,z1175]),(0,[z8,z0,z2,z3,z1176,z4])],[(0,[z8,z0,z2,z3,z4,z1177]),(0,[z8,z426,z2,z3,z4,z446]),(0,[z8,z0,z2,z55,z3,z215])],[(0,[z8,z0,z425,z2,z55,z4]),(0,[z8,z0,z2,z55,z35,z4]),(0,[z8,z0,z2,z3,z1178,z4]),(0,[z8,z0,z2,z3,z4,z1179]),(0,[z180,z0,z2,z3,z4,z1180])],[(0,[z8,z0,z2,z3,z4,z1181]),(0,[z13,z0,z2,z825,z4,z6]),(0,[z8,z1182,z2,z3,z4,z6])],[(0,[z8,z0,z2,z163,z217,z6]),(0,[z8,z0,z2,z3,z4,z1183])],[(0,[z0,z2,z3,z4,z104,z126]),(0,[z85,z0,z2,z367,z4,z6]),(0,[z389,z30,z2,z3,z81,z6]),(0,[z8,z0,z2,z3,z4,z1184]),(0,[z8,z0,z2,z103,z4,z68])],[(0,[z0,z1,z2,z3,z4,z72]),(0,[z0,z2,z3,z74,z4,z6]),(0,[z36,z8,z0,z214,z3,z4]),(0,[z51,z0,z2,z3,z757,z6]),(0,[z61,z0,z2,z3,z4,z1185]),(0,[z60,z8,z2,z55,z176,z4])],[(0,[z13,z0,z2,z3,z4,z481]),(0,[z13,z0,z2,z3,z4,z246]),(0,[z1186,z8,z0,z2,z3,z4])],[(0,[z40,z0,z182,z3,z4,z360]),(0,[z8,z0,z2,z3,z1187,z4]),(0,[z696,z8,z2,z3,z4,z9]),(0,[z8,z0,z2,z367,z4,z6]),(0,[z1188,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1189])],[(0,[z1190,z8,z0,z2,z3,z4]),(0,[z101,z0,z2,z3,z4,z11])],[],[(0,[z29,z0,z1,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1191])],[(0,[z13,z565,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z539,z387]),(0,[z71,z0,z2,z3,z321,z4])],[(0,[z71,z0,z2,z76,z4,z6]),(0,[z1192,z0,z2,z3,z4,z6])]],
   [[(0,[z8,z0,z2,z3,z1193,z6]),(0,[z8,z0,z2,z3,z4,z1194])],[(0,[z254,z0,z2,z3,z4,z222])],[(0,[z0,z1,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z1195]),(0,[z8,z0,z2,z103,z4,z31]),(0,[z8,z0,z2,z3,z1196,z6])],[(0,[z64,z1,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z162,z285]),(0,[z8,z0,z2,z3,z4,z1197]),(0,[z8,z0,z2,z49,z4,z11])],[(0,[z8,z0,z1198,z2,z3,z4])],[(0,[z1199,z8,z0,z2,z3,z4])],[(0,[z123,z1,z2,z3,z4,z11]),(0,[z319,z0,z1,z2,z3,z4]),(0,[z13,z0,z2,z3,z4,z524]),(0,[z13,z0,z2,z523,z3,z4])],[(0,[z1,z2,z3,z393,z4,z6]),(0,[z0,z1,z2,z3,z4,z130]),(0,[z8,z17,z0,z2,z50,z4]),(0,[z8,z0,z2,z3,z4,z1200])],[(0,[z43,z1,z2,z3,z4,z289]),(0,[z0,z182,z44,z28,z4,z6]),(0,[z8,z0,z110,z3,z137,z6]),(0,[z51,z0,z2,z3,z52,z11])],[(0,[z64,z1,z2,z3,z4,z222]),(0,[z8,z0,z2,z3,z4,z1201]),(0,[z8,z0,z2,z3,z4,z1202]),(0,[z526,z0,z2,z3,z4,z20]),(0,[z0,z346,z2,z3,z4,z9])],[(0,[z64,z1,z42,z3,z4,z6]),(0,[z36,z8,z0,z2,z208,z4])],[(0,[z13,z96,z2,z3,z4,z232]),(0,[z0,z2,z3,z4,z222,z252])],[(0,[z1,z2,z400,z3,z4,z6]),(1,[z230,z2,z3,z4,z31]),(0,[z0,z2,z3,z4,z130,z31]),(0,[z8,z64,z65,z55,z3,z4]),(0,[z219,z8,z0,z2,z224,z6]),(0,[z1203,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z283]),(0,[z43,z1,z2,z3,z618,z6]),(0,[z13,z335,z2,z3,z4,z6]),(0,[z8,z0,z439,z55,z3,z4]),(0,[z8,z2,z3,z4,z1204,z6]),(0,[z101,z0,z2,z3,z4,z841])],[(0,[z1205,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1206])],[(0,[z43,z8,z2,z3,z649,z6]),(0,[z36,z8,z0,z2,z4,z284])],[(0,[z186,z1,z2,z3,z4,z6]),(0,[z358,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1207]),(0,[z8,z0,z357,z3,z257,z6]),(0,[z8,z0,z2,z1208,z3,z4]),(0,[z1209,z0,z2,z3,z4,z6])],[(0,[z1210,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1211]),(0,[z8,z0,z926,z55,z3,z4])],[(0,[z51,z0,z2,z3,z104,z31]),(0,[z8,z0,z2,z144,z3,z4])],[(0,[z8,z0,z2,z3,z4,z1212]),(0,[z8,z0,z2,z3,z4,z1213]),(0,[z8,z0,z2,z213,z4,z31]),(0,[z1214,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1215]),(0,[z34,z0,z54,z35,z4,z6]),(0,[z0,z2,z3,z4,z20,z31]),(0,[z180,z0,z2,z3,z1216,z6]),(0,[z8,z1217,z2,z3,z4,z6]),(0,[z8,z929,z2,z55,z3,z4])],[(0,[z0,z1,z2,z367,z4,z6]),(1,[z1,z2,z121,z4,z6]),(0,[z13,z0,z2,z55,z4,z316]),(0,[z8,z0,z2,z3,z4,z1218])],[(0,[z8,z0,z1219,z3,z4,z6]),(0,[z1220,z8,z0,z2,z3,z4])],[],[(0,[z13,z36,z0,z2,z3,z4]),(0,[z43,z1,z2,z3,z4,z6]),(0,[z8,z1221,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1222]),(0,[z661,z0,z2,z3,z4,z31]),(0,[z1223,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z1224,z6]),(0,[z907,z451,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z162,z11]),(0,[z119,z36,z8,z2,z3,z4]),(0,[z43,z8,z2,z3,z5,z289]),(0,[z8,z2,z3,z4,z1143,z6]),(0,[z8,z0,z2,z1225,z4,z6]),(0,[z8,z0,z55,z83,z282,z4]),(0,[z8,z1226,z2,z3,z4,z6])],[(0,[z1227,z64,z2,z3,z4,z6]),(0,[z1,z2,z3,z81,z4,z126]),(0,[z8,z457,z2,z3,z4,z1104]),(0,[z1228,z8,z0,z2,z3,z4])],[(0,[z602,z1,z2,z3,z4,z6]),(0,[z8,z42,z3,z4,z217,z6]),(0,[z8,z0,z2,z3,z257,z6]),(0,[z1229,z8,z2,z3,z4,z6]),(0,[z138,z101,z0,z3,z82,z6])],[],[(0,[z43,z1,z2,z3,z4,z222]),(0,[z8,z1,z2,z121,z4,z6]),(0,[z34,z0,z54,z3,z4,z11]),(0,[z8,z2,z19,z3,z139,z4]),(0,[z102,z8,z0,z2,z3,z4])],[(0,[z13,z0,z2,z3,z4,z883]),(0,[z8,z0,z1230,z2,z3,z4])]],
   [[(0,[z13,z0,z2,z3,z4,z515]),(0,[z8,z0,z2,z3,z178,z20]),(0,[z8,z0,z2,z3,z4,z1231])],[(0,[z8,z0,z2,z174,z4,z31]),(0,[z0,z2,z3,z4,z175,z31]),(0,[z8,z233,z2,z3,z4,z1232]),(0,[z0,z2,z3,z4,z1233,z6])],[(0,[z199,z0,z2,z3,z104,z6]),(0,[z8,z0,z2,z3,z4,z1234]),(0,[z8,z0,z2,z3,z4,z1235])],[(0,[z8,z0,z2,z3,z4,z1236])],[(0,[z56,z230,z2,z3,z4,z6])],[(0,[z8,z345,z2,z3,z4,z405]),(0,[z8,z0,z2,z3,z4,z1237]),(0,[z1238,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1239]),(0,[z8,z0,z2,z55,z4,z464])],[],[(0,[z1,z2,z439,z3,z4,z6]),(0,[z8,z0,z2,z3,z1240,z6]),(0,[z8,z0,z2,z1241,z4,z6]),(0,[z8,z0,z2,z1242,z4,z6])],[(0,[z43,z1,z2,z3,z81,z6]),(0,[z0,z1,z2,z3,z4,z283]),(0,[z8,z0,z1243,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1244]),(0,[z180,z0,z54,z3,z4,z6]),(0,[z8,z17,z2,z19,z4,z397]),(0,[z8,z2,z3,z4,z339,z9]),(0,[z8,z0,z2,z3,z1245,z6])],[(0,[z43,z8,z2,z3,z5,z6]),(0,[z683,z8,z0,z2,z224,z6]),(0,[z0,z1246,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z340]),(0,[z211,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z443,z4,z6]),(0,[z60,z8,z357,z176,z4,z6])],[(0,[z36,z8,z457,z2,z3,z4]),(0,[z1247,z8,z0,z2,z3,z4]),(0,[z36,z8,z0,z2,z3,z870])],[(0,[z1,z2,z3,z176,z4,z20]),(0,[z8,z2,z3,z4,z252,z9]),(0,[z8,z0,z2,z3,z4,z1248])],[(0,[z255,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z121,z4,z289])],[(0,[z623,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z146,z83,z4]),(0,[z8,z0,z128,z3,z37,z20]),(0,[z117,z8,z42,z3,z4,z6])],[(0,[z13,z0,z2,z3,z162,z33]),(0,[z8,z0,z110,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1249]),(0,[z8,z0,z2,z3,z4,z716]),(0,[z8,z0,z18,z3,z4,z188]),(0,[z85,z0,z2,z163,z4,z6])],[(0,[z8,z0,z2,z3,z4,z779]),(0,[z1250,z8,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1251]),(0,[z86,z36,z8,z0,z28,z4])],[(0,[z8,z0,z2,z3,z217,z11])],[(0,[z0,z1,z2,z3,z1224,z6]),(0,[z8,z0,z2,z163,z4,z6]),(0,[z8,z0,z2,z3,z4,z397]),(0,[z639,z8,z2,z3,z4,z9])],[],[(0,[z901,z8,z0,z2,z3,z4]),(0,[z8,z0,z793,z3,z4,z6]),(0,[z8,z0,z2,z3,z1252,z4]),(0,[z61,z0,z2,z3,z4,z508])],[(0,[z0,z1,z2,z3,z257,z6]),(0,[z13,z96,z2,z3,z4,z9]),(0,[z230,z2,z54,z3,z4,z6]),(0,[z60,z8,z2,z176,z4,z6]),(0,[z86,z8,z0,z28,z4,z11])],[(0,[z8,z0,z2,z3,z4,z1253]),(0,[z1254,z0,z2,z3,z4,z6]),(0,[z8,z136,z2,z3,z4,z9])],[(0,[z8,z422,z2,z3,z81,z6]),(0,[z1255,z0,z2,z3,z4,z6]),(0,[z1256,z0,z2,z3,z4,z6])],[(0,[z1,z2,z3,z460,z4,z6]),(0,[z13,z1,z2,z3,z4,z285]),(0,[z1257,z8,z0,z2,z3,z4]),(0,[z1258,z0,z2,z3,z4,z6]),(0,[z43,z8,z2,z3,z1143,z6]),(0,[z8,z0,z2,z3,z1259,z9])],[(0,[z8,z0,z2,z3,z1260,z4]),(0,[z8,z401,z2,z55,z3,z4]),(0,[z8,z0,z2,z1261,z3,z4]),(0,[z8,z0,z1262,z2,z3,z4]),(0,[z450,z8,z0,z2,z3,z95]),(0,[z8,z0,z42,z163,z4,z6]),(0,[z8,z0,z2,z55,z3,z217]),(0,[z8,z0,z2,z3,z165,z11]),(0,[z1263,z8,z0,z2,z3,z4])],[(0,[z0,z1,z1264,z2,z3,z4]),(0,[z0,z73,z2,z3,z4,z397])],[(0,[z1,z2,z3,z463,z4,z6]),(0,[z0,z2,z3,z4,z222,z31]),(0,[z8,z0,z2,z1028,z35,z4]),(0,[z266,z426,z2,z3,z4,z6]),(0,[z8,z0,z65,z3,z217,z6]),(0,[z211,z8,z2,z3,z5,z6])],[(0,[z180,z0,z2,z3,z4,z9]),(0,[z8,z358,z2,z3,z4,z9])],[(0,[z13,z1,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z1265,z6]),(0,[z36,z436,z0,z2,z3,z4]),(0,[z8,z451,z2,z55,z3,z4]),(0,[z8,z0,z1266,z3,z4,z6])]],
   [[(0,[z13,z64,z65,z3,z4,z6]),(0,[z8,z0,z2,z1267,z4,z6]),(0,[z119,z8,z2,z3,z4,z1268]),(0,[z8,z0,z2,z55,z603,z4]),(0,[z8,z0,z2,z3,z1269,z6]),(0,[z389,z0,z2,z3,z4,z1270]),(0,[z8,z0,z2,z3,z898,z6]),(0,[z8,z0,z2,z3,z4,z1271])],[(0,[z13,z0,z439,z3,z4,z6]),(0,[z343,z0,z2,z3,z4,z104])],[(0,[z0,z1,z2,z3,z1240,z6]),(0,[z698,z1,z2,z3,z4,z6]),(0,[z391,z8,z0,z28,z4,z6]),(0,[z36,z8,z0,z2,z367,z4]),(0,[z516,z8,z42,z3,z4,z6]),(0,[z1272,z0,z2,z3,z4,z6])],[(0,[z36,z8,z0,z2,z480,z4]),(1,[z8,z2,z3,z4,z896]),(0,[z8,z2,z3,z4,z896,z9]),(0,[z8,z0,z18,z3,z4,z223])],[(0,[z36,z8,z0,z2,z213,z4])],[(0,[z1273,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z1274,z4,z6]),(0,[z8,z0,z1275,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z340]),(0,[z1276,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z165,z481])],[(0,[z273,z1,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z1277])],[(0,[z8,z1278,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z1279,z4])],[(0,[z0,z2,z44,z3,z321,z4]),(0,[z276,z0,z2,z3,z104,z6]),(0,[z8,z0,z2,z121,z4,z31]),(0,[z198,z0,z2,z3,z4,z9])],[(0,[z43,z1,z2,z3,z519,z6]),(0,[z543,z8,z42,z3,z4,z6]),(0,[z8,z457,z2,z3,z4,z31]),(0,[z1042,z8,z0,z2,z35,z4]),(0,[z8,z0,z2,z3,z178,z387]),(0,[z8,z0,z2,z1280,z3,z4]),(0,[z8,z0,z2,z3,z4,z381]),(0,[z60,z61,z2,z176,z4,z6])],[(0,[z0,z1,z110,z3,z4,z6]),(0,[z8,z0,z2,z3,z217,z524])],[(0,[z1,z2,z42,z55,z3,z4]),(0,[z1,z2,z55,z3,z139,z4]),(0,[z1,z2,z3,z4,z252,z31]),(0,[z180,z0,z2,z44,z4,z6]),(0,[z343,z8,z0,z2,z50,z4]),(0,[z8,z0,z2,z3,z4,z1281])],[(0,[z8,z350,z2,z3,z4,z11])],[(0,[z389,z0,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z4,z568]),(0,[z8,z0,z2,z121,z81,z6])],[(0,[z1282,z8,z2,z3,z4,z6]),(0,[z8,z0,z2,z1283,z4,z6]),(0,[z8,z991,z2,z55,z3,z4])],[(0,[z0,z2,z3,z4,z675,z31]),(0,[z8,z0,z2,z1284,z4,z6]),(0,[z1285,z0,z2,z3,z4,z6]),(0,[z61,z0,z2,z3,z4,z11]),(0,[z1286,z0,z2,z3,z4,z6])],[(0,[z36,z8,z426,z2,z3,z4])],[(0,[z43,z1,z2,z174,z4,z6]),(0,[z8,z401,z2,z3,z4,z980]),(0,[z8,z0,z214,z3,z4,z9]),(0,[z8,z0,z2,z3,z757,z6]),(0,[z60,z8,z587,z2,z176,z4]),(0,[z1287,z8,z0,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z360]),(0,[z1288,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1289]),(0,[z8,z0,z2,z1290,z4,z6])],[(0,[z287,z8,z0,z2,z176,z4])],[(0,[z86,z0,z1,z28,z4,z6]),(0,[z0,z1,z2,z3,z137,z6]),(0,[z8,z0,z2,z1291,z3,z4]),(0,[z436,z0,z439,z3,z4,z6]),(0,[z0,z2,z3,z4,z1292,z6]),(0,[z8,z0,z2,z3,z4,z1293])],[(0,[z227,z0,z2,z3,z4,z9])],[(0,[z1081,z0,z1,z2,z3,z4]),(0,[z180,z0,z2,z35,z4,z6]),(0,[z8,z0,z2,z55,z4,z184]),(0,[z8,z0,z1294,z3,z4,z6]),(0,[z36,z8,z0,z2,z4,z613])],[(0,[z8,z0,z1295,z3,z4,z6])],[(0,[z8,z0,z2,z55,z3,z105]),(0,[z8,z1296,z2,z3,z4,z6]),(0,[z436,z0,z2,z3,z4,z513]),(0,[z276,z0,z2,z3,z4,z11])],[(0,[z13,z0,z2,z3,z4,z285]),(0,[z8,z0,z2,z1297,z4,z6]),(0,[z8,z233,z2,z3,z4,z9])],[(0,[z61,z0,z2,z3,z4,z481]),(0,[z8,z0,z3,z4,z713,z68])],[(0,[z8,z0,z2,z3,z1298,z6]),(0,[z259,z8,z0,z28,z4,z6])],[(0,[z22,z0,z2,z3,z4,z126]),(0,[z1,z2,z3,z420,z4,z6]),(0,[z13,z0,z2,z55,z28,z4]),(0,[z8,z401,z2,z3,z334,z6]),(0,[z8,z0,z2,z3,z1299,z6])],[(0,[z1,z2,z55,z3,z81,z4]),(0,[z8,z426,z2,z55,z3,z4])],[(0,[z13,z0,z2,z55,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z320]),(0,[z0,z2,z3,z492,z4,z31])],[(0,[z180,z0,z2,z3,z4,z11])],[(0,[z0,z1,z2,z3,z105,z6]),(0,[z0,z89,z2,z3,z4,z6]),(0,[z345,z2,z44,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1300]),(0,[z1301,z0,z2,z3,z4,z9]),(0,[z36,z8,z0,z2,z49,z4]),(0,[z93,z8,z0,z2,z103,z4]),(0,[z0,z1302,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z1303,z6])],[(0,[z670,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1304]),(0,[z119,z8,z2,z3,z4,z9]),(0,[z43,z8,z2,z174,z5,z6])],[(0,[z1273,z0,z2,z3,z4,z6]),(0,[z1,z2,z3,z81,z4,z6]),(0,[z0,z1,z2,z3,z4,z381]),(0,[z8,z0,z2,z3,z4,z1305]),(0,[z34,z426,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z162,z285]),(0,[z8,z0,z2,z3,z4,z1306]),(0,[z8,z0,z2,z3,z1307,z6]),(0,[z8,z0,z2,z3,z4,z1308]),(0,[z36,z8,z0,z357,z3,z4]),(0,[z8,z327,z116,z2,z3,z4])],[(0,[z13,z1,z2,z3,z4,z33]),(0,[z138,z8,z0,z3,z82,z31]),(0,[z43,z36,z8,z2,z3,z5])],[(0,[z8,z0,z1309,z3,z4,z6])],[(0,[z119,z1,z2,z3,z4,z6]),(0,[z308,z8,z0,z3,z4,z158])],[(0,[z36,z0,z1,z2,z4,z114]),(0,[z491,z8,z0,z2,z44,z4]),(0,[z8,z0,z2,z3,z4,z1310]),(0,[z8,z0,z2,z3,z344,z47]),(0,[z8,z0,z2,z3,z4,z1311])],[],[(0,[z13,z241,z2,z3,z4,z6]),(0,[z8,z0,z2,z1312,z4,z6]),(0,[z8,z0,z2,z951,z4,z6]),(0,[z198,z0,z2,z3,z4,z11]),(0,[z101,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z4,z1313])],[(0,[z411,z17,z2,z19,z4,z6]),(0,[z8,z361,z2,z19,z4,z6])],[(0,[z0,z1,z2,z3,z98,z47]),(0,[z396,z2,z42,z3,z4,z6]),(0,[z85,z0,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z1314]),(0,[z8,z0,z3,z37,z898,z6])],[(0,[z0,z422,z2,z3,z4,z31]),(0,[z13,z796,z0,z2,z3,z4]),(0,[z13,z401,z2,z3,z4,z6]),(0,[z0,z2,z3,z52,z757,z6])],[(0,[z8,z0,z2,z3,z4,z1315])],[(0,[z0,z1,z357,z3,z4,z6]),(0,[z1316,z8,z0,z2,z3,z4])],[(0,[z8,z0,z2,z35,z4,z31]),(0,[z8,z0,z2,z3,z4,z1317]),(0,[z8,z0,z2,z3,z258,z205]),(0,[z0,z2,z3,z4,z1318,z6])],[(0,[z8,z1027,z2,z55,z3,z4])],[(0,[z8,z0,z2,z3,z4,z822]),(0,[z8,z0,z2,z3,z4,z1319])],[(0,[z8,z345,z2,z35,z4,z6]),(0,[z36,z8,z0,z2,z3,z137]),(0,[z8,z0,z2,z3,z4,z1320]),(0,[z8,z1321,z2,z3,z4,z6])],[(0,[z0,z1,z18,z3,z4,z68]),(0,[z118,z0,z94,z3,z4,z6]),(0,[z8,z169,z2,z3,z4,z11])],[(0,[z123,z1,z2,z55,z3,z4]),(0,[z17,z1,z2,z3,z4,z9]),(0,[z319,z8,z0,z2,z144,z4])],[(0,[z411,z0,z2,z3,z4,z6])],[(0,[z13,z0,z2,z3,z4,z373]),(0,[z227,z0,z2,z3,z4,z11])],[(0,[z43,z1,z2,z121,z4,z6]),(0,[z39,z36,z0,z2,z3,z104]),(0,[z8,z0,z531,z3,z165,z6])],[(0,[z1322,z8,z0,z2,z3,z4]),(0,[z112,z0,z2,z3,z4,z285]),(0,[z8,z0,z214,z3,z4,z446]),(0,[z138,z8,z0,z3,z898,z6])],[(0,[z112,z0,z2,z3,z4,z720]),(0,[z655,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z1323]),(0,[z8,z0,z2,z3,z968,z6]),(0,[z8,z0,z2,z3,z4,z481]),(0,[z8,z0,z2,z1324,z4,z6]),(0,[z8,z0,z2,z3,z4,z246]),(0,[z1038,z0,z2,z55,z3,z4])],[(1,[z0,z2,z3,z162,z285]),(0,[z8,z30,z2,z3,z81,z9]),(0,[z1325,z0,z2,z3,z4,z6])],[(0,[z287,z0,z1,z2,z3,z4]),(0,[z13,z0,z2,z3,z139,z4]),(0,[z0,z18,z2,z3,z4,z274])],[(0,[z8,z345,z2,z3,z4,z11]),(0,[z71,z0,z2,z800,z4,z6]),(0,[z8,z0,z2,z3,z4,z132]),(1,[z8,z0,z3,z898,z6])]],
   [[(0,[z8,z426,z2,z3,z334,z6]),(0,[z8,z0,z2,z3,z4,z1326]),(0,[z1327,z0,z2,z3,z4,z6]),(0,[z14,z8,z0,z2,z3,z218]),(0,[z101,z451,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z435,z47])],[(0,[z13,z0,z2,z3,z334,z6]),(0,[z13,z0,z2,z3,z4,z21]),(0,[z36,z8,z0,z2,z3,z257]),(0,[z8,z0,z2,z103,z4,z90])],[(0,[z8,z0,z2,z987,z3,z4]),(0,[z431,z0,z2,z3,z4,z31]),(0,[z1328,z0,z2,z3,z4,z6]),(0,[z8,z0,z772,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1329]),(0,[z8,z64,z65,z3,z4,z20])],[(0,[z13,z0,z2,z3,z4,z992]),(0,[z8,z0,z439,z3,z4,z20])],[(0,[z8,z1330,z2,z3,z4,z6]),(0,[z8,z0,z1331,z3,z4,z6]),(0,[z8,z0,z113,z3,z4,z142])],[(0,[z8,z0,z2,z3,z162,z285]),(0,[z13,z0,z2,z3,z4,z24]),(0,[z85,z0,z2,z3,z4,z524]),(0,[z101,z0,z2,z3,z4,z373])],[(0,[z8,z0,z2,z3,z4,z1332]),(0,[z62,z13,z2,z3,z4,z9]),(0,[z71,z0,z2,z35,z4,z6]),(0,[z8,z0,z2,z3,z4,z1333]),(0,[z8,z0,z2,z3,z1334,z6]),(0,[z8,z0,z2,z3,z4,z1335]),(0,[z127,z0,z2,z3,z4,z289]),(0,[z8,z0,z2,z3,z4,z1336]),(0,[z343,z413,z0,z2,z3,z4])],[(0,[z681,z8,z2,z3,z4,z9])],[(0,[z0,z2,z3,z162,z6,z285]),(0,[z8,z0,z2,z3,z4,z1337]),(0,[z8,z0,z2,z1338,z4,z6]),(0,[z36,z8,z0,z2,z179,z4]),(0,[z8,z0,z2,z3,z4,z524]),(0,[z8,z0,z2,z83,z139,z4]),(0,[z1339,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1340]),(0,[z8,z0,z2,z3,z4,z1341])],[(0,[z13,z0,z2,z3,z4,z409]),(0,[z13,z0,z2,z50,z3,z4]),(0,[z0,z335,z2,z3,z4,z20]),(0,[z180,z36,z0,z2,z3,z4])],[(0,[z1,z2,z94,z3,z4,z6]),(0,[z151,z8,z2,z176,z4,z6]),(0,[z8,z457,z2,z3,z4,z1244]),(0,[z8,z0,z2,z3,z4,z1342]),(0,[z36,z0,z73,z2,z3,z4]),(0,[z43,z8,z2,z121,z5,z6]),(0,[z8,z0,z1050,z55,z3,z4])],[(0,[z8,z0,z1343,z3,z4,z6]),(0,[z8,z0,z2,z3,z1344,z4]),(0,[z0,z2,z3,z74,z4,z11]),(0,[z8,z0,z2,z820,z4,z6]),(0,[z0,z2,z3,z1345,z4,z6]),(0,[z8,z0,z2,z55,z4,z881])],[(0,[z8,z0,z2,z3,z4,z1346]),(0,[z0,z346,z2,z3,z4,z20]),(0,[z36,z8,z0,z2,z3,z215]),(0,[z8,z0,z2,z3,z257,z9]),(0,[z8,z0,z2,z3,z4,z1347]),(0,[z8,z0,z202,z3,z4,z9]),(0,[z1348,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z49,z4,z373]),(0,[z1349,z0,z2,z3,z4,z6]),(0,[z0,z1350,z2,z3,z4,z6])],[(0,[z10,z0,z1,z2,z224,z6]),(0,[z13,z1210,z0,z2,z3,z4]),(0,[z34,z0,z54,z55,z3,z4]),(0,[z0,z2,z3,z4,z575,z31]),(0,[z8,z0,z2,z367,z4,z11])],[(0,[z8,z230,z2,z3,z4,z6]),(0,[z8,z0,z2,z1351,z3,z4]),(0,[z1352,z8,z0,z2,z3,z4]),(0,[z8,z1353,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z1334])],[],[(0,[z13,z426,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z104,z473]),(0,[z8,z0,z2,z845,z4,z31]),(0,[z117,z85,z42,z3,z4,z6]),(0,[z36,z8,z0,z2,z695,z4])],[(0,[z8,z0,z2,z3,z4,z1354]),(0,[z96,z8,z2,z3,z4,z252]),(0,[z495,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z217,z568]),(0,[z8,z0,z2,z3,z4,z1355])],[(0,[z71,z0,z2,z76,z4,z11]),(0,[z8,z30,z2,z3,z1143,z6])],[(0,[z8,z0,z2,z3,z4,z1356])],[(0,[z1,z2,z176,z28,z4,z6]),(0,[z8,z1357,z2,z3,z4,z6]),(1,[z0,z967,z3,z4,z6]),(0,[z40,z0,z182,z3,z4,z9]),(0,[z426,z2,z3,z4,z104,z6]),(0,[z8,z0,z2,z3,z4,z1358]),(0,[z8,z0,z2,z3,z4,z1359])],[(0,[z8,z0,z2,z3,z257,z508])],[(0,[z345,z1,z2,z3,z4,z6]),(0,[z64,z1,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z1360]),(0,[z0,z1361,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z149,z4]),(0,[z8,z0,z2,z55,z4,z316])],[(0,[z441,z8,z2,z3,z4,z9])],[(0,[z8,z0,z2,z480,z4,z6]),(0,[z8,z0,z2,z3,z539,z6]),(0,[z71,z0,z2,z76,z4,z446])],[(0,[z1,z2,z3,z559,z4,z6]),(1,[z1,z439,z3,z4,z6]),(0,[z396,z64,z2,z3,z4,z6]),(0,[z8,z0,z2,z144,z176,z4]),(0,[z0,z2,z3,z301,z74,z4]),(0,[z8,z0,z2,z3,z4,z1232]),(0,[z8,z0,z2,z3,z4,z1362])],[(0,[z343,z0,z1,z2,z3,z4]),(0,[z1363,z0,z2,z3,z4,z6])],[(0,[z43,z1,z2,z3,z104,z6]),(0,[z8,z0,z2,z3,z4,z1364]),(0,[z8,z0,z2,z55,z663,z4]),(0,[z8,z0,z2,z3,z4,z1365]),(0,[z8,z350,z2,z229,z3,z4])],[(0,[z0,z1366,z2,z3,z4,z6]),(0,[z203,z1,z2,z3,z4,z6]),(0,[z441,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z1367,z6])],[(0,[z13,z1,z2,z3,z162,z6]),(0,[z8,z0,z967,z3,z4,z6]),(0,[z8,z0,z1368,z3,z4,z6])]],
   [[(0,[z0,z182,z3,z552,z4,z6]),(0,[z85,z0,z2,z3,z215,z6]),(0,[z8,z0,z2,z3,z4,z1369]),(0,[z356,z0,z2,z3,z4,z21])],[(0,[z8,z0,z2,z50,z44,z4]),(0,[z0,z2,z3,z4,z474,z31]),(0,[z117,z8,z42,z3,z4,z9]),(0,[z17,z73,z2,z19,z4,z6]),(0,[z8,z0,z2,z3,z4,z1370])],[(0,[z8,z0,z1371,z3,z4,z6]),(0,[z8,z0,z110,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z1372]),(0,[z127,z0,z2,z3,z4,z31]),(0,[z581,z0,z2,z3,z4,z31])],[(0,[z51,z0,z2,z3,z4,z446]),(0,[z8,z0,z2,z3,z215,z6]),(0,[z227,z36,z0,z2,z3,z4]),(0,[z36,z8,z0,z2,z3,z964])],[(0,[z478,z0,z2,z3,z162,z6]),(0,[z8,z0,z2,z974,z55,z4]),(0,[z8,z0,z2,z55,z646,z4]),(0,[z847,z2,z3,z133,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1373]),(0,[z0,z2,z3,z4,z134,z31]),(0,[z1374,z8,z0,z2,z3,z4]),(0,[z1375,z0,z2,z3,z4,z6])],[(0,[z356,z0,z2,z3,z4,z33]),(0,[z265,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z1376,z3,z4]),(0,[z36,z127,z0,z2,z3,z4]),(0,[z0,z167,z2,z3,z4,z126])],[(0,[z8,z0,z2,z367,z4,z524])],[(0,[z8,z0,z2,z3,z4,z232]),(0,[z13,z0,z2,z49,z4,z6]),(0,[z1377,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z1007,z4,z6]),(0,[z1378,z0,z2,z3,z4,z6])],[(0,[z1,z2,z3,z176,z4,z126]),(0,[z0,z1,z2,z213,z4,z6]),(0,[z60,z8,z2,z176,z4,z9]),(0,[z43,z436,z2,z3,z5,z6]),(0,[z8,z0,z2,z3,z4,z1379])],[(0,[z8,z0,z2,z3,z1216,z6]),(0,[z8,z0,z2,z3,z4,z1380]),(0,[z1381,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1351,z3,z4]),(0,[z265,z0,z2,z3,z4,z130]),(0,[z8,z0,z77,z3,z4,z15]),(0,[z8,z0,z1382,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1383]),(0,[z8,z0,z2,z3,z137,z9]),(0,[z8,z0,z2,z55,z174,z4])],[(0,[z43,z1,z2,z3,z4,z11]),(1,[z8,z439,z3,z5,z6])],[(0,[z239,z0,z2,z3,z104,z6])],[(0,[z117,z36,z8,z42,z3,z4]),(0,[z8,z0,z2,z3,z4,z1384])],[(0,[z8,z0,z110,z44,z4,z6]),(0,[z8,z0,z2,z3,z4,z1268]),(0,[z8,z0,z531,z3,z4,z6]),(0,[z1385,z8,z0,z2,z3,z4])],[(0,[z8,z0,z2,z3,z257,z11]),(0,[z8,z0,z2,z3,z4,z1386])],[(0,[z1,z2,z176,z4,z224,z6]),(0,[z60,z8,z2,z176,z4,z508]),(0,[z8,z0,z2,z55,z4,z406]),(0,[z8,z0,z2,z1387,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1388]),(0,[z8,z0,z2,z3,z4,z1389])],[(0,[z17,z1,z2,z19,z4,z6]),(0,[z0,z157,z2,z3,z4,z31]),(0,[z0,z2,z3,z95,z4,z274])],[(0,[z0,z1,z2,z480,z4,z6]),(0,[z8,z0,z439,z3,z52,z6]),(0,[z101,z0,z2,z49,z4,z6]),(0,[z0,z1047,z2,z3,z4,z6])],[(0,[z13,z343,z0,z2,z3,z4]),(0,[z1390,z8,z0,z2,z3,z4]),(0,[z8,z451,z2,z3,z4,z20])],[(0,[z1391,z8,z0,z2,z3,z4]),(0,[z293,z0,z2,z3,z4,z31])],[],[(0,[z13,z0,z587,z2,z3,z4]),(0,[z8,z0,z2,z3,z105,z9]),(0,[z8,z0,z2,z3,z4,z1392])],[(0,[z415,z8,z0,z2,z3,z95]),(0,[z8,z0,z2,z3,z4,z1393])],[(0,[z36,z64,z1,z2,z3,z4]),(0,[z13,z0,z2,z3,z105,z20])],[(0,[z13,z96,z2,z3,z4,z20])],[(0,[z136,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z20,z320]),(0,[z8,z0,z2,z55,z260,z4])],[(0,[z0,z1,z2,z3,z215,z6]),(0,[z13,z0,z2,z3,z4,z145]),(0,[z0,z1394,z2,z3,z4,z6]),(0,[z61,z17,z2,z3,z4,z6])],[(0,[z13,z0,z2,z3,z162,z6]),(0,[z8,z0,z2,z834,z4,z126]),(0,[z8,z0,z2,z3,z4,z1395]),(0,[z43,z8,z2,z3,z5,z11]),(0,[z138,z8,z0,z3,z82,z412])]],
   [[(0,[z1,z2,z3,z590,z4,z6]),(0,[z8,z0,z2,z3,z4,z1396]),(0,[z1397,z8,z0,z2,z3,z4]),(0,[z389,z0,z2,z3,z4,z9]),(0,[z62,z198,z2,z3,z4,z9]),(0,[z0,z2,z3,z4,z1398,z6]),(0,[z8,z0,z2,z300,z3,z46])],[(0,[z8,z0,z1399,z2,z3,z4]),(0,[z39,z0,z2,z55,z3,z104]),(0,[z7,z8,z0,z3,z4,z304]),(0,[z61,z0,z2,z55,z3,z4])],[(0,[z13,z0,z2,z3,z1053,z6])],[(0,[z8,z0,z2,z3,z1400,z6]),(0,[z8,z0,z2,z121,z104,z6])],[(0,[z117,z8,z42,z3,z4,z11]),(0,[z8,z327,z2,z3,z4,z896]),(0,[z8,z0,z2,z1401,z4,z6]),(0,[z1402,z0,z2,z3,z4,z6])],[(0,[z0,z1403,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z1055,z6]),(0,[z8,z0,z110,z3,z4,z11]),(0,[z8,z0,z2,z1404,z3,z4]),(0,[z8,z0,z2,z3,z4,z1405]),(0,[z396,z0,z2,z3,z4,z9])],[(0,[z13,z0,z2,z3,z4,z153]),(0,[z8,z64,z65,z3,z4,z261]),(0,[z8,z0,z2,z3,z1406,z6]),(0,[z8,z0,z2,z3,z4,z1407])],[(0,[z8,z0,z2,z1408,z4,z6]),(0,[z8,z0,z2,z3,z4,z1409]),(0,[z36,z8,z0,z2,z3,z1063])],[(0,[z13,z485,z2,z3,z4,z6]),(0,[z138,z13,z0,z3,z82,z6]),(0,[z8,z0,z357,z3,z4,z9])],[(0,[z32,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z1410]),(0,[z8,z0,z2,z149,z4,z6]),(0,[z1411,z0,z2,z3,z4,z6])],[(0,[z13,z0,z2,z3,z4,z1065]),(0,[z119,z51,z2,z3,z4,z31]),(0,[z325,z0,z2,z3,z165,z6]),(0,[z276,z0,z2,z55,z3,z4])],[(0,[z0,z2,z44,z3,z178,z6]),(0,[z8,z0,z110,z3,z4,z446]),(0,[z8,z0,z2,z3,z4,z1412]),(0,[z36,z8,z0,z2,z594,z4]),(0,[z1066,z8,z0,z2,z3,z4])],[(0,[z39,z0,z2,z3,z104,z145]),(0,[z60,z8,z2,z176,z4,z11]),(0,[z0,z346,z2,z3,z4,z1413])],[(0,[z8,z0,z182,z35,z4,z6]),(0,[z491,z8,z0,z2,z146,z4]),(0,[z1414,z8,z0,z2,z3,z4]),(0,[z1415,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z473]),(0,[z13,z0,z2,z1070,z3,z4]),(0,[z8,z0,z1416,z3,z4,z6]),(0,[z8,z0,z156,z2,z3,z4]),(0,[z0,z2,z3,z212,z4,z31]),(0,[z8,z64,z65,z3,z4,z31]),(0,[z85,z0,z2,z3,z4,z568]),(0,[z1417,z0,z2,z3,z4,z6]),(0,[z62,z8,z2,z3,z139,z4])],[(0,[z8,z0,z2,z3,z137,z11]),(0,[z8,z0,z439,z3,z4,z31]),(0,[z1100,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z963,z4,z6]),(0,[z553,z0,z54,z3,z4,z6]),(0,[z71,z0,z2,z523,z76,z4]),(0,[z1418,z0,z2,z3,z4,z6]),(0,[z1419,z0,z2,z3,z4,z6]),(0,[z180,z0,z2,z55,z28,z4])],[(0,[z102,z0,z1,z2,z3,z4]),(0,[z0,z2,z3,z105,z104,z6]),(0,[z8,z0,z357,z3,z4,z508])],[(0,[z0,z2,z44,z35,z4,z6]),(0,[z8,z688,z2,z3,z4,z11])],[(0,[z8,z0,z65,z163,z4,z6]),(0,[z1420,z0,z2,z3,z4,z6]),(0,[z299,z8,z0,z2,z3,z218])],[(0,[z8,z0,z2,z3,z4,z9]),(0,[z1093,z17,z2,z3,z4,z6]),(0,[z318,z0,z2,z3,z4,z9])],[(0,[z13,z0,z2,z3,z4,z210]),(0,[z8,z0,z2,z3,z539,z405]),(0,[z8,z0,z2,z1421,z3,z4]),(0,[z8,z0,z2,z3,z137,z446])],[(0,[z0,z230,z2,z3,z4,z31]),(0,[z36,z8,z0,z2,z3,z217])],[(0,[z8,z0,z214,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z1422]),(0,[z8,z0,z2,z3,z4,z1423]),(0,[z8,z0,z2,z3,z4,z1424])],[(1,[z1,z2,z3,z139,z4]),(0,[z13,z0,z2,z3,z217,z6]),(0,[z8,z0,z2,z934,z4,z31]),(0,[z211,z8,z0,z3,z82,z6])],[(0,[z13,z491,z0,z2,z3,z4]),(0,[z78,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z969,z4]),(0,[z8,z2,z3,z1143,z5,z6])],[(0,[z8,z0,z1425,z2,z3,z4]),(0,[z0,z346,z2,z3,z4,z92]),(0,[z1126,z8,z2,z3,z4,z6])],[(0,[z478,z1,z2,z3,z4,z6]),(0,[z8,z273,z2,z3,z4,z222]),(0,[z8,z0,z1426,z3,z4,z6]),(0,[z231,z8,z0,z3,z4,z580])],[(0,[z8,z0,z2,z3,z1427,z6]),(0,[z0,z2,z3,z4,z104,z446]),(0,[z0,z73,z2,z3,z4,z9]),(0,[z8,z0,z128,z55,z3,z37])],[(0,[z1,z2,z3,z249,z4,z6]),(0,[z13,z696,z2,z3,z4,z6]),(0,[z8,z0,z2,z794,z3,z4]),(0,[z8,z0,z2,z3,z4,z1428])],[(1,[z8,z0,z2,z834,z4]),(0,[z1429,z0,z2,z3,z4,z6])],[(0,[z85,z0,z2,z55,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z468]),(0,[z8,z0,z2,z3,z4,z1430]),(0,[z13,z0,z2,z3,z165,z6]),(0,[z127,z0,z2,z3,z4,z1239])],[(0,[z0,z2,z3,z133,z104,z31]),(0,[z8,z0,z2,z163,z4,z524])],[(0,[z71,z36,z0,z2,z76,z4]),(0,[z14,z8,z0,z2,z3,z534])],[(0,[z389,z0,z2,z3,z4,z11])],[(0,[z39,z0,z2,z3,z104,z20]),(0,[z36,z8,z0,z2,z4,z456]),(0,[z805,z8,z0,z2,z3,z4]),(0,[z436,z0,z202,z3,z4,z6])],[(0,[z227,z0,z2,z3,z4,z285]),(0,[z0,z2,z44,z286,z4,z6]),(0,[z8,z0,z2,z55,z163,z4])],[(0,[z1,z2,z3,z4,z222,z320]),(0,[z13,z0,z2,z3,z4,z173]),(0,[z8,z0,z2,z3,z178,z6]),(0,[z8,z0,z2,z3,z4,z1431]),(0,[z1432,z0,z2,z3,z4,z6])],[(0,[z8,z345,z2,z3,z4,z946]),(0,[z8,z0,z2,z523,z83,z4]),(0,[z0,z2,z3,z4,z320,z126]),(0,[z86,z8,z0,z820,z4,z6]),(0,[z1433,z0,z2,z3,z4,z6])],[(0,[z396,z0,z2,z3,z4,z11]),(0,[z36,z0,z167,z2,z3,z4])],[(0,[z0,z1,z156,z2,z3,z4]),(0,[z8,z0,z2,z1434,z3,z4]),(0,[z119,z8,z2,z3,z4,z20]),(0,[z36,z8,z1435,z2,z3,z4]),(0,[z36,z8,z0,z2,z4,z313]),(0,[z8,z0,z2,z3,z1303,z47])],[(0,[z71,z0,z2,z410,z4,z6]),(0,[z8,z0,z2,z3,z4,z1436]),(0,[z411,z0,z2,z3,z4,z9]),(0,[z0,z2,z3,z4,z1292,z11])],[(0,[z0,z1,z2,z3,z4,z773]),(0,[z8,z0,z2,z49,z4,z20])],[(0,[z8,z0,z2,z3,z1437,z6]),(0,[z276,z0,z2,z3,z334,z6])],[(0,[z112,z0,z2,z3,z4,z126]),(0,[z56,z0,z2,z3,z4,z20]),(0,[z8,z0,z1438,z2,z3,z4]),(0,[z8,z1439,z2,z3,z4,z6])],[(0,[z8,z0,z2,z55,z3,z539]),(0,[z8,z230,z2,z3,z4,z752])],[(0,[z0,z1,z2,z3,z4,z9]),(0,[z0,z2,z3,z1440,z4,z6]),(0,[z426,z2,z3,z76,z4,z6]),(0,[z8,z0,z2,z367,z4,z568]),(0,[z1441,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z103,z4,z9])],[(0,[z0,z167,z2,z3,z4,z6]),(0,[z13,z29,z0,z2,z3,z4]),(0,[z8,z345,z2,z55,z3,z4]),(0,[z343,z0,z156,z2,z3,z4])],[(0,[z8,z0,z2,z3,z4,z1442]),(0,[z8,z0,z2,z3,z4,z1443]),(0,[z7,z8,z0,z3,z4,z713])],[(0,[z350,z1,z2,z55,z3,z4])],[(0,[z1,z2,z3,z176,z4,z6]),(0,[z13,z0,z2,z1107,z3,z4]),(0,[z13,z96,z2,z3,z4,z33]),(0,[z8,z401,z2,z3,z4,z72]),(0,[z8,z230,z2,z3,z4,z468]),(0,[z8,z0,z2,z3,z4,z1444]),(0,[z389,z0,z2,z3,z4,z326]),(0,[z8,z0,z2,z974,z3,z4])],[(0,[z7,z8,z0,z3,z4,z580])],[(0,[z478,z0,z148,z3,z4,z6]),(0,[z445,z0,z2,z3,z4,z285]),(0,[z8,z0,z128,z3,z37,z6]),(0,[z8,z0,z2,z1445,z3,z4])],[(0,[z8,z0,z2,z3,z4,z1446]),(0,[z276,z0,z2,z3,z4,z409])],[(0,[z51,z0,z2,z3,z4,z719]),(0,[z0,z89,z2,z3,z4,z11])],[(0,[z0,z1,z2,z3,z4,z508]),(0,[z51,z0,z2,z3,z551,z6]),(0,[z8,z0,z2,z3,z98,z107]),(0,[z1447,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1448])],[(0,[z8,z0,z2,z3,z4,z1449]),(0,[z0,z2,z50,z3,z4,z104]),(0,[z8,z0,z2,z3,z4,z1450]),(0,[z127,z0,z2,z121,z4,z6]),(0,[z26,z8,z0,z359,z3,z4])],[(0,[z1,z2,z3,z81,z4,z11]),(0,[z8,z0,z2,z1451,z4,z6]),(0,[z8,z0,z2,z3,z4,z1452]),(0,[z8,z0,z2,z3,z1453,z6]),(0,[z0,z2,z3,z4,z1454,z6]),(0,[z14,z8,z0,z2,z3,z95])],[(0,[z0,z1,z2,z3,z4,z1430]),(0,[z8,z1455,z2,z3,z4,z6]),(0,[z8,z0,z2,z163,z215,z6]),(0,[z1456,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z1143,z6])],[(0,[z13,z1,z2,z3,z4,z222]),(0,[z1,z651,z2,z3,z4,z6]),(0,[z17,z1,z2,z3,z4,z20]),(0,[z8,z0,z1457,z2,z3,z4])],[(0,[z1,z2,z653,z3,z4,z6]),(0,[z8,z457,z2,z480,z4,z6]),(0,[z8,z457,z2,z3,z539,z6]),(0,[z8,z401,z2,z3,z4,z31]),(0,[z8,z0,z2,z55,z3,z334]),(0,[z0,z1458,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z483,z20]),(0,[z8,z0,z2,z3,z4,z1459]),(0,[z8,z0,z2,z3,z4,z1460]),(0,[z0,z2,z3,z1461,z74,z4])],[(0,[z1462,z8,z0,z2,z3,z4])]],
   [[(0,[z325,z0,z2,z3,z4,z6]),(0,[z43,z1,z439,z3,z4,z6]),(0,[z553,z8,z0,z3,z82,z6]),(0,[z8,z0,z2,z213,z4,z9])],[(0,[z13,z1,z2,z3,z4,z31]),(0,[z0,z1,z2,z3,z178,z6]),(0,[z0,z1463,z2,z3,z4,z6])],[(0,[z8,z30,z2,z3,z81,z20]),(0,[z0,z2,z3,z1464,z4,z6])],[(0,[z13,z119,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1465]),(0,[z8,z0,z2,z3,z4,z1466]),(0,[z8,z0,z2,z146,z4,z184])],[(0,[z8,z0,z2,z3,z1303,z98])],[(0,[z198,z0,z2,z3,z4,z33]),(0,[z8,z0,z2,z3,z334,z72]),(0,[z8,z0,z357,z19,z4,z6]),(0,[z8,z0,z55,z83,z28,z4]),(0,[z1192,z0,z2,z55,z3,z4])],[(0,[z233,z1,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z105,z31]),(0,[z8,z0,z2,z3,z4,z1467]),(0,[z0,z2,z3,z4,z31,z320]),(0,[z8,z0,z2,z3,z1468,z4]),(0,[z1469,z0,z2,z3,z4,z6]),(0,[z8,z451,z2,z3,z4,z1172])],[(0,[z8,z0,z2,z3,z4,z1470])],[(0,[z263,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z1471,z4,z6]),(0,[z78,z0,z2,z3,z4,z1132]),(0,[z8,z0,z2,z3,z4,z1472]),(0,[z8,z0,z202,z3,z4,z513])],[(0,[z1,z2,z42,z3,z4,z222]),(0,[z64,z1,z2,z55,z3,z4]),(0,[z8,z0,z2,z834,z4,z6]),(0,[z51,z0,z2,z3,z4,z285]),(0,[z478,z345,z2,z3,z4,z6])],[(0,[z436,z1,z2,z3,z4,z6]),(0,[z1473,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1474]),(0,[z10,z8,z0,z2,z108,z224])],[(0,[z43,z8,z2,z3,z461,z6]),(0,[z325,z0,z2,z3,z4,z31]),(0,[z8,z0,z116,z2,z3,z4]),(0,[z0,z73,z2,z3,z4,z1466])],[(0,[z8,z0,z2,z480,z4,z9]),(0,[z8,z0,z2,z3,z1016,z6]),(0,[z8,z116,z2,z3,z4,z9])],[(0,[z484,z1,z2,z3,z4,z6]),(0,[z273,z1,z2,z3,z4,z6]),(0,[z411,z0,z2,z3,z4,z11]),(0,[z389,z36,z0,z2,z3,z4])],[(0,[z1,z2,z42,z3,z4,z31]),(0,[z8,z0,z2,z174,z4,z9]),(0,[z0,z2,z3,z4,z175,z9]),(0,[z404,z0,z156,z2,z3,z4])],[(0,[z138,z0,z1,z3,z82,z6]),(0,[z8,z0,z2,z3,z334,z31])],[(0,[z8,z0,z2,z3,z4,z1475]),(0,[z1,z120,z42,z3,z4,z6]),(0,[z0,z1,z128,z3,z37,z6]),(0,[z8,z0,z2,z3,z4,z1476]),(0,[z0,z2,z54,z3,z321,z4]),(0,[z1477,z8,z0,z2,z3,z4]),(0,[z112,z0,z2,z3,z4,z252]),(0,[z8,z42,z3,z5,z82,z6]),(0,[z43,z127,z2,z3,z5,z6]),(0,[z36,z8,z30,z2,z3,z81]),(0,[z138,z102,z8,z0,z3,z82])],[(0,[z1478,z0,z2,z3,z4,z6]),(0,[z1479,z8,z0,z2,z3,z4]),(0,[z547,z0,z2,z3,z4,z31]),(0,[z0,z2,z3,z4,z1480,z6])],[(0,[z328,z0,z2,z3,z4,z222]),(0,[z43,z8,z439,z3,z5,z6]),(0,[z8,z0,z2,z55,z3,z1406])],[(0,[z8,z0,z2,z3,z4,z1481]),(0,[z8,z0,z202,z3,z4,z20]),(0,[z491,z8,z0,z2,z4,z288]),(0,[z8,z0,z2,z1482,z4,z6])],[(0,[z8,z0,z2,z1073,z4,z20]),(0,[z8,z0,z2,z3,z1483,z4])],[(0,[z71,z401,z2,z76,z4,z6]),(0,[z39,z0,z2,z3,z757,z6])],[(0,[z8,z426,z2,z3,z4,z72]),(0,[z51,z0,z2,z55,z3,z52]),(0,[z8,z0,z2,z3,z4,z1484])],[(0,[z327,z1,z2,z3,z4,z11]),(0,[z13,z0,z2,z3,z4,z72])],[(0,[z62,z1,z2,z3,z4,z9]),(0,[z1,z2,z3,z677,z4,z6]),(0,[z0,z1,z2,z3,z4,z446]),(0,[z0,z1485,z2,z3,z4,z6]),(0,[z8,z451,z2,z3,z4,z1486])],[(0,[z1487,z0,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z4,z261])],[(0,[z0,z2,z3,z800,z4,z6]),(0,[z436,z0,z2,z3,z4,z289])],[(0,[z8,z0,z2,z3,z4,z1488]),(0,[z1,z2,z680,z3,z4,z6]),(0,[z567,z1,z2,z3,z4,z6]),(0,[z36,z51,z0,z2,z3,z52]),(0,[z8,z0,z2,z3,z217,z20])],[(0,[z96,z8,z2,z121,z4,z6]),(0,[z8,z0,z2,z3,z1489,z4]),(0,[z0,z1490,z2,z3,z4,z6])],[(0,[z0,z193,z182,z3,z4,z6]),(0,[z8,z426,z2,z3,z4,z1160])],[(0,[z43,z1,z2,z55,z3,z4]),(0,[z151,z0,z2,z535,z4,z6]),(0,[z1491,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z480,z178,z6]),(0,[z411,z0,z2,z3,z4,z1472])],[(0,[z13,z36,z0,z2,z3,z162]),(0,[z13,z437,z2,z3,z4,z6]),(0,[z8,z0,z540,z2,z3,z4]),(0,[z8,z0,z2,z229,z83,z4]),(0,[z14,z8,z0,z2,z3,z511])]],
   [[(0,[z8,z426,z2,z3,z4,z31])],[(0,[z13,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z178,z405]),(0,[z8,z0,z2,z3,z1492,z4]),(0,[z8,z0,z2,z1493,z3,z4])],[(0,[z0,z1,z2,z3,z4,z326]),(0,[z8,z0,z2,z3,z1494,z4]),(0,[z1495,z0,z2,z3,z4,z6]),(0,[z8,z0,z1496,z2,z3,z4])],[(0,[z569,z8,z2,z3,z4,z252]),(0,[z8,z0,z2,z3,z165,z20])],[(0,[z0,z1,z2,z834,z4,z6]),(0,[z1316,z0,z1,z2,z3,z4]),(0,[z13,z345,z2,z3,z4,z6]),(0,[z40,z0,z2,z3,z162,z6])],[(0,[z8,z0,z2,z35,z539,z6]),(0,[z8,z230,z2,z3,z4,z11]),(0,[z1497,z0,z2,z3,z4,z6]),(0,[z8,z847,z2,z3,z4,z6])],[(0,[z0,z1,z116,z2,z3,z4]),(0,[z13,z0,z2,z3,z4,z130]),(0,[z8,z0,z2,z3,z4,z1498])],[(0,[z8,z0,z2,z3,z1499,z6]),(0,[z8,z0,z2,z3,z1049,z4]),(0,[z71,z0,z2,z76,z334,z6]),(0,[z8,z0,z2,z55,z699,z4]),(0,[z8,z0,z2,z1008,z4,z31])],[(0,[z8,z0,z2,z3,z4,z1500]),(0,[z1501,z0,z2,z3,z4,z6])],[(0,[z345,z2,z54,z3,z4,z6]),(0,[z71,z0,z2,z55,z76,z4]),(0,[z8,z0,z2,z163,z4,z568]),(0,[z8,z2,z3,z4,z99,z11]),(0,[z8,z0,z18,z3,z282,z4])],[(0,[z436,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z1502,z4,z6]),(0,[z0,z73,z2,z3,z4,z874]),(0,[z8,z0,z2,z3,z4,z1503])],[(0,[z615,z1,z2,z3,z4,z6]),(0,[z1,z2,z689,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1476])],[(0,[z8,z0,z2,z3,z4,z718]),(0,[z13,z0,z2,z3,z4,z1175]),(0,[z0,z110,z3,z4,z104,z6]),(0,[z8,z0,z2,z1504,z3,z4])],[(0,[z567,z8,z2,z3,z5,z6]),(0,[z585,z8,z0,z2,z55,z4])],[(0,[z8,z2,z3,z4,z252,z126]),(0,[z8,z0,z2,z3,z4,z1505]),(0,[z101,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z1506]),(0,[z36,z8,z0,z2,z55,z4])],[(0,[z8,z0,z2,z3,z4,z1507]),(0,[z8,z0,z2,z3,z4,z724]),(0,[z8,z0,z2,z480,z4,z11]),(0,[z8,z0,z2,z3,z539,z11]),(0,[z140,z8,z0,z28,z4,z6]),(0,[z39,z0,z2,z3,z104,z31])],[(0,[z36,z0,z1120,z2,z3,z4]),(0,[z8,z0,z2,z3,z95,z1303])],[(0,[z8,z0,z2,z3,z4,z1508]),(0,[z8,z0,z2,z3,z4,z1509]),(0,[z8,z1510,z2,z3,z4,z6]),(0,[z8,z64,z65,z3,z4,z381]),(0,[z8,z355,z2,z3,z81,z6])],[(0,[z1,z2,z3,z133,z81,z6]),(0,[z86,z27,z8,z0,z28,z4])],[(0,[z8,z0,z728,z3,z4,z6]),(0,[z8,z0,z1511,z2,z3,z4])],[(0,[z123,z1,z2,z3,z4,z222]),(0,[z13,z0,z2,z367,z4,z6]),(0,[z1512,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z50,z76,z4]),(0,[z117,z8,z42,z55,z3,z4]),(0,[z93,z8,z0,z2,z55,z4]),(0,[z276,z0,z2,z3,z38,z4]),(0,[z0,z2,z55,z3,z4,z274])],[(0,[z8,z0,z110,z55,z3,z4]),(0,[z23,z0,z2,z44,z4,z31]),(0,[z8,z0,z2,z49,z4,z31]),(0,[z1513,z0,z2,z3,z4,z6])],[(0,[z440,z1,z2,z3,z4,z6]),(0,[z8,z457,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z1514]),(0,[z161,z8,z2,z176,z4,z6]),(0,[z411,z36,z0,z2,z3,z4]),(0,[z36,z8,z0,z2,z121,z4]),(0,[z36,z8,z233,z2,z3,z4])],[(0,[z1515,z8,z0,z2,z3,z4]),(0,[z71,z426,z2,z76,z4,z6]),(0,[z8,z0,z2,z3,z215,z11]),(0,[z8,z0,z2,z3,z1516,z6]),(0,[z8,z0,z2,z55,z4,z168])],[(0,[z123,z1,z2,z3,z4,z31]),(0,[z112,z0,z2,z3,z321,z4])],[(0,[z0,z1,z540,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1517]),(0,[z30,z0,z2,z3,z104,z31])],[(0,[z51,z0,z2,z3,z52,z31]),(0,[z1518,z8,z0,z2,z3,z4]),(0,[z8,z0,z347,z3,z37,z6]),(0,[z8,z0,z2,z55,z4,z268])],[(0,[z8,z0,z2,z3,z4,z1519]),(0,[z343,z51,z0,z2,z3,z4]),(0,[z8,z0,z1520,z2,z3,z4]),(0,[z8,z0,z2,z4,z114,z881])],[(0,[z34,z0,z110,z3,z4,z6]),(0,[z8,z0,z2,z55,z529,z4]),(0,[z8,z0,z2,z3,z1521,z6]),(0,[z325,z0,z2,z3,z4,z1522]),(0,[z8,z70,z2,z3,z4,z9]),(0,[z36,z101,z0,z2,z3,z4]),(0,[z1523,z0,z2,z3,z4,z6])],[(0,[z396,z0,z2,z3,z4,z924]),(0,[z1524,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z1525,z4,z6]),(0,[z1526,z0,z2,z3,z4,z6])],[]],
   [[(0,[z1527,z8,z0,z2,z3,z4]),(0,[z51,z0,z2,z3,z52,z130]),(0,[z1528,z8,z0,z2,z3,z4]),(0,[z0,z2,z3,z4,z274,z20]),(0,[z8,z0,z2,z55,z83,z4]),(0,[z668,z8,z0,z28,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1529]),(0,[z8,z0,z2,z921,z4,z6]),(0,[z8,z0,z2,z3,z4,z1530]),(0,[z276,z0,z2,z3,z4,z20])],[(0,[z0,z2,z3,z4,z104,z285]),(0,[z61,z0,z2,z3,z165,z6]),(0,[z1531,z0,z2,z3,z4,z6])],[(0,[z13,z1322,z0,z2,z3,z4])],[(0,[z500,z8,z2,z3,z4,z320])],[(0,[z8,z0,z2,z3,z4,z1532]),(0,[z8,z0,z531,z3,z4,z11]),(0,[z8,z0,z2,z229,z28,z4])],[(0,[z8,z401,z110,z3,z4,z6])],[(0,[z13,z0,z2,z3,z4,z283]),(0,[z36,z8,z0,z2,z174,z4]),(0,[z36,z0,z2,z3,z4,z175])],[(0,[z8,z0,z2,z3,z105,z285])],[(0,[z8,z457,z2,z3,z178,z6])],[(0,[z13,z0,z2,z3,z4,z1207]),(0,[z1533,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1534])],[(0,[z13,z36,z0,z2,z3,z105]),(0,[z13,z0,z2,z144,z3,z4]),(0,[z8,z0,z2,z763,z3,z4]),(0,[z8,z2,z3,z4,z676,z9])],[(0,[z17,z1,z2,z176,z4,z6]),(0,[z8,z0,z2,z3,z162,z31]),(0,[z8,z0,z2,z3,z4,z1535]),(0,[z60,z325,z2,z176,z4,z6]),(0,[z8,z0,z2,z121,z5,z6]),(0,[z8,z0,z629,z83,z4,z6]),(0,[z8,z0,z2,z3,z38,z4])],[(0,[z1,z2,z3,z59,z4,z6]),(0,[z13,z0,z2,z3,z4,z1215]),(0,[z8,z0,z2,z3,z4,z513]),(0,[z8,z30,z2,z3,z81,z92]),(0,[z8,z0,z2,z3,z1427,z9])],[(0,[z8,z0,z2,z3,z4,z1536])],[(0,[z0,z193,z275,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1537]),(0,[z0,z2,z3,z162,z6,z31]),(0,[z8,z0,z2,z3,z215,z524]),(0,[z8,z0,z531,z3,z4,z481])],[(0,[z34,z0,z54,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z719])],[(0,[z417,z8,z0,z3,z4,z90])],[(0,[z8,z0,z2,z806,z224,z6])],[(0,[z0,z346,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z162,z11]),(0,[z34,z345,z54,z3,z4,z6]),(0,[z389,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z4,z1538])],[(0,[z0,z2,z3,z1539,z4,z6]),(0,[z60,z8,z116,z2,z3,z4])],[(0,[z13,z0,z2,z3,z257,z6]),(0,[z8,z0,z2,z3,z1540,z4]),(0,[z85,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z1541]),(0,[z1286,z0,z2,z55,z3,z4])],[(0,[z8,z0,z2,z3,z4,z1542]),(0,[z8,z0,z2,z3,z4,z1543])],[(0,[z8,z0,z110,z3,z334,z6]),(0,[z8,z0,z2,z1544,z3,z4]),(0,[z8,z0,z2,z3,z4,z906])],[(0,[z8,z0,z2,z3,z4,z20]),(0,[z0,z2,z3,z4,z20,z718]),(0,[z8,z0,z1545,z3,z4,z6]),(0,[z318,z0,z2,z3,z4,z20]),(0,[z10,z8,z0,z2,z224,z20]),(0,[z8,z0,z2,z1401,z4,z11]),(0,[z8,z0,z2,z1546,z4,z6])],[(0,[z8,z0,z2,z3,z1547,z4]),(0,[z8,z0,z2,z3,z4,z1548])],[(0,[z1094,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z55,z83,z4]),(0,[z426,z182,z2,z3,z4,z6]),(0,[z1549,z8,z0,z2,z3,z4])],[],[(0,[z491,z8,z0,z2,z3,z4]),(0,[z14,z8,z0,z2,z3,z572]),(0,[z60,z36,z8,z2,z176,z4]),(0,[z1550,z0,z2,z3,z4,z6]),(0,[z8,z0,z1294,z55,z3,z4])],[(0,[z8,z0,z2,z149,z4,z11]),(0,[z8,z925,z2,z3,z4,z6]),(0,[z27,z8,z0,z2,z3,z4]),(0,[z0,z2,z3,z4,z1142,z6])],[(0,[z8,z0,z2,z35,z4,z9]),(0,[z10,z8,z0,z2,z806,z6])]],
   [[(0,[z1551,z0,z2,z3,z4,z6]),(0,[z0,z847,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z229,z3,z4]),(0,[z71,z0,z2,z3,z162,z6]),(0,[z13,z1273,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z1552,z6])],[(0,[z230,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z459,z4]),(1,[z8,z451,z3,z82,z6])],[(0,[z8,z0,z2,z3,z4,z1553]),(0,[z436,z0,z2,z174,z4,z6]),(0,[z442,z8,z2,z3,z139,z4])],[(0,[z13,z0,z2,z3,z4,z340]),(0,[z0,z1,z439,z3,z4,z6]),(0,[z230,z2,z3,z52,z4,z6]),(0,[z0,z1554,z2,z3,z4,z6]),(0,[z62,z32,z2,z3,z4,z9]),(1,[z945,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z217,z31])],[(0,[z13,z96,z2,z3,z105,z6]),(0,[z8,z0,z128,z3,z37,z9])],[(0,[z0,z89,z2,z55,z3,z4]),(0,[z101,z0,z2,z3,z82,z6])],[(0,[z0,z1,z2,z3,z4,z513]),(0,[z8,z0,z2,z3,z4,z1555]),(0,[z8,z0,z2,z1556,z3,z4]),(0,[z8,z0,z2,z3,z4,z896])],[(0,[z13,z0,z110,z3,z4,z6]),(0,[z0,z2,z3,z4,z1215,z31]),(0,[z86,z8,z0,z28,z4,z31]),(0,[z0,z2,z3,z4,z449,z31]),(0,[z8,z273,z2,z3,z4,z11])],[(0,[z1,z2,z55,z3,z176,z4]),(0,[z0,z1,z2,z3,z4,z1537]),(0,[z48,z8,z0,z3,z82,z6]),(0,[z278,z0,z2,z3,z4,z126])],[(0,[z0,z2,z115,z3,z162,z6]),(0,[z8,z0,z2,z50,z83,z4]),(0,[z8,z0,z2,z3,z4,z1557])],[(0,[z8,z1558,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1559]),(0,[z8,z0,z2,z3,z1560,z4])],[(0,[z13,z652,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z4,z397]),(0,[z8,z0,z2,z3,z165,z31]),(0,[z8,z0,z1309,z55,z3,z4])],[(0,[z8,z0,z2,z3,z4,z1561]),(0,[z13,z10,z0,z2,z224,z6]),(0,[z433,z8,z0,z2,z224,z6]),(0,[z8,z0,z1562,z2,z3,z4])],[(0,[z1,z2,z3,z141,z4,z6]),(0,[z1227,z1,z2,z3,z4,z6])],[(0,[z8,z0,z2,z35,z178,z6])],[(0,[z13,z0,z2,z3,z4,z360]),(0,[z276,z0,z2,z3,z52,z6]),(0,[z0,z346,z2,z3,z4,z1563])],[(0,[z8,z1564,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1565])],[(0,[z36,z1,z2,z42,z3,z4]),(0,[z13,z0,z2,z3,z137,z6]),(0,[z8,z0,z2,z103,z4,z20])],[(0,[z40,z0,z148,z3,z4,z6]),(0,[z8,z0,z2,z3,z105,z33]),(0,[z8,z0,z214,z3,z137,z6]),(0,[z8,z0,z2,z3,z785,z6]),(0,[z8,z0,z595,z28,z4,z6])],[(0,[z8,z0,z751,z3,z4,z6]),(0,[z8,z2,z19,z851,z4,z6])],[],[(0,[z17,z1,z2,z3,z4,z126]),(0,[z36,z0,z346,z2,z3,z4]),(0,[z1566,z8,z0,z2,z3,z4])],[(0,[z13,z0,z2,z3,z1265,z6]),(0,[z8,z0,z2,z3,z4,z1567]),(0,[z8,z0,z2,z3,z4,z1568])],[(0,[z1,z155,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z1569,z6])],[(0,[z51,z0,z2,z3,z4,z126]),(0,[z8,z0,z2,z3,z178,z11]),(0,[z8,z1321,z2,z55,z3,z4])],[(0,[z487,z8,z0,z3,z4,z304])],[(0,[z36,z8,z0,z2,z3,z4]),(0,[z123,z1,z2,z3,z4,z340]),(0,[z8,z623,z2,z19,z4,z6])],[(0,[z0,z1,z2,z3,z4,z285]),(0,[z8,z1570,z2,z3,z4,z6]),(0,[z411,z0,z2,z55,z3,z4])],[(0,[z8,z0,z2,z3,z4,z978])]],
   [[(0,[z64,z1,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z1571]),(0,[z36,z8,z0,z2,z163,z4]),(0,[z180,z0,z2,z3,z301,z4]),(0,[z14,z8,z0,z2,z3,z1303])],[(0,[z0,z1,z2,z55,z28,z4])],[(0,[z13,z96,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z387]),(0,[z61,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z50,z4,z224]),(0,[z8,z0,z2,z3,z1572,z4]),(0,[z61,z2,z3,z176,z4,z6]),(0,[z8,z0,z2,z159,z3,z4])],[(0,[z13,z0,z2,z3,z4,z381]),(0,[z8,z1573,z2,z3,z4,z6]),(0,[z0,z2,z3,z200,z104,z6]),(0,[z389,z0,z2,z3,z4,z1000])],[(0,[z8,z0,z2,z3,z1574,z6]),(0,[z8,z0,z2,z3,z1259,z6])],[],[(0,[z78,z0,z2,z3,z4,z381])],[(0,[z1,z2,z3,z176,z4,z11]),(0,[z8,z335,z2,z3,z4,z9]),(0,[z8,z0,z2,z174,z4,z513])],[(0,[z40,z345,z2,z3,z4,z6]),(0,[z36,z8,z0,z2,z3,z539]),(0,[z8,z0,z1575,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1576]),(0,[z8,z0,z128,z3,z37,z11]),(0,[z8,z0,z2,z3,z98,z479]),(0,[z8,z0,z2,z3,z1303,z4])],[(0,[z1273,z8,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1135]),(0,[z180,z27,z0,z2,z3,z4])],[(0,[z180,z0,z2,z76,z4,z6]),(0,[z276,z0,z2,z3,z4,z31]),(0,[z436,z0,z2,z121,z4,z6]),(0,[z36,z8,z1577,z2,z3,z4])],[(0,[z13,z0,z2,z3,z98,z47]),(0,[z8,z0,z2,z1578,z3,z4]),(0,[z8,z0,z1579,z2,z3,z4]),(0,[z8,z0,z2,z55,z3,z1580])],[(0,[z411,z401,z2,z3,z4,z6]),(0,[z0,z2,z3,z321,z4,z20]),(0,[z8,z0,z849,z55,z3,z4])],[(0,[z32,z0,z2,z3,z4,z6])],[(0,[z1227,z0,z2,z3,z4,z6]),(0,[z43,z8,z2,z3,z519,z6]),(0,[z8,z0,z2,z3,z4,z1581]),(0,[z1582,z8,z0,z2,z3,z4])],[(1,[z0,z1,z2,z834,z4]),(0,[z8,z0,z1583,z2,z3,z4])],[(0,[z8,z0,z2,z50,z28,z4]),(0,[z8,z0,z18,z3,z4,z536])],[(0,[z13,z0,z2,z55,z3,z105]),(0,[z8,z0,z2,z174,z4,z20]),(0,[z8,z0,z2,z1584,z3,z4]),(0,[z8,z0,z2,z3,z95,z46])],[(0,[z180,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z1585,z4]),(0,[z1586,z0,z2,z3,z4,z6])],[(0,[z0,z1587,z2,z3,z4,z6]),(0,[z8,z0,z2,z1588,z3,z4]),(0,[z8,z0,z2,z3,z4,z1589])],[(0,[z186,z0,z2,z3,z162,z6]),(0,[z8,z230,z2,z55,z3,z4]),(0,[z56,z0,z2,z3,z4,z320]),(0,[z8,z0,z2,z3,z4,z1590]),(0,[z36,z8,z0,z2,z600,z4])],[(0,[z8,z0,z2,z3,z4,z1591]),(0,[z8,z0,z2,z3,z4,z1413]),(0,[z8,z0,z2,z3,z4,z1592])],[(0,[z8,z0,z2,z3,z4,z1593]),(0,[z36,z396,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z215,z568]),(0,[z8,z0,z2,z3,z4,z1594]),(0,[z287,z8,z0,z2,z19,z4])],[(0,[z8,z0,z2,z3,z4,z58])],[(0,[z36,z358,z1,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1595]),(0,[z8,z0,z2,z3,z4,z1596]),(0,[z441,z8,z2,z3,z4,z126])],[(0,[z151,z0,z2,z76,z4,z6]),(0,[z36,z8,z0,z531,z3,z4])],[],[(0,[z0,z1,z2,z3,z4,z373]),(0,[z96,z1273,z2,z3,z4,z6]),(0,[z8,z0,z214,z3,z4,z6]),(0,[z8,z0,z2,z3,z98,z466])],[(0,[z0,z1,z2,z3,z4,z387]),(0,[z51,z0,z2,z3,z4,z252])],[(0,[z78,z0,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z4,z1305]),(0,[z198,z0,z2,z3,z4,z31]),(0,[z8,z17,z2,z851,z4,z6])]],
   [[(0,[z8,z0,z2,z3,z4,z1597]),(0,[z325,z0,z2,z3,z4,z481]),(0,[z8,z0,z2,z3,z4,z1598]),(0,[z36,z8,z0,z128,z3,z37])],[(0,[z85,z0,z2,z3,z4,z31]),(0,[z1599,z0,z2,z3,z4,z6])],[],[(0,[z0,z2,z3,z4,z21,z31]),(0,[z8,z0,z2,z3,z1600,z6])],[(0,[z8,z0,z2,z1601,z3,z4]),(0,[z36,z1258,z0,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z21]),(0,[z8,z233,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z92]),(0,[z318,z233,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z104,z145]),(0,[z318,z0,z2,z3,z4,z1602]),(0,[z8,z0,z2,z3,z4,z1602])],[(0,[z0,z1603,z2,z3,z4,z6])],[(0,[z8,z1577,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1604]),(0,[z8,z0,z2,z28,z4,z132]),(0,[z8,z451,z2,z213,z4,z6])],[(0,[z8,z0,z2,z1605,z4,z6]),(0,[z8,z0,z2,z1606,z4,z6])],[(0,[z51,z0,z2,z3,z105,z6]),(0,[z8,z0,z2,z3,z4,z1607])],[(0,[z1273,z123,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z33]),(0,[z593,z1,z2,z3,z4,z6])],[(0,[z34,z0,z967,z3,z4,z6]),(0,[z227,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z108]),(0,[z0,z1608,z2,z3,z4,z6])],[(0,[z1,z42,z3,z28,z4,z6]),(0,[z14,z0,z1,z2,z3,z95]),(0,[z8,z0,z2,z4,z726,z126]),(0,[z0,z2,z44,z3,z162,z6]),(0,[z8,z0,z2,z3,z1609,z4]),(0,[z8,z0,z2,z3,z4,z1610])],[(0,[z0,z2,z800,z76,z4,z6]),(0,[z51,z0,z2,z3,z386,z6]),(0,[z117,z8,z42,z3,z217,z6]),(0,[z1301,z0,z2,z3,z4,z6])],[(0,[z119,z8,z2,z3,z4,z6]),(0,[z436,z0,z2,z3,z104,z6]),(0,[z1611,z0,z2,z3,z4,z6]),(0,[z1612,z8,z0,z2,z3,z4])],[(0,[z8,z0,z2,z55,z237,z4])],[(0,[z8,z0,z2,z3,z4,z1613]),(0,[z8,z0,z2,z163,z4,z20])],[(0,[z1,z128,z42,z3,z4,z6]),(0,[z0,z2,z3,z105,z162,z6]),(0,[z8,z345,z2,z3,z4,z31]),(0,[z0,z967,z54,z3,z4,z6]),(0,[z1263,z8,z0,z2,z121,z4])],[(0,[z8,z0,z2,z3,z4,z1614]),(0,[z8,z0,z1615,z2,z3,z4]),(0,[z0,z2,z55,z74,z28,z4])],[(0,[z0,z1,z2,z3,z4,z58]),(0,[z71,z0,z2,z249,z4,z6]),(0,[z389,z0,z2,z3,z162,z6]),(0,[z8,z2,z229,z3,z139,z4])],[],[(0,[z0,z2,z3,z4,z519,z31]),(0,[z8,z0,z2,z1616,z3,z4]),(0,[z8,z0,z531,z55,z3,z4]),(1,[z8,z0,z2,z3,z1303])],[],[(0,[z0,z1,z214,z3,z4,z6]),(0,[z61,z0,z2,z3,z257,z6]),(0,[z8,z2,z447,z3,z4,z11])],[(0,[z13,z0,z2,z3,z4,z132]),(1,[z8,z2,z851,z4,z6]),(0,[z411,z0,z2,z3,z1600,z6])],[(0,[z8,z0,z2,z3,z4,z1617])],[(0,[z0,z2,z3,z4,z1618,z6]),(0,[z8,z0,z2,z480,z4,z387]),(0,[z8,z0,z2,z121,z4,z20]),(0,[z8,z64,z65,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z1486])],[(0,[z445,z0,z2,z3,z4,z31]),(0,[z8,z457,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z1619,z4]),(0,[z8,z0,z439,z3,z4,z9]),(0,[z180,z86,z0,z28,z4,z6])],[(0,[z71,z0,z2,z76,z4,z72]),(0,[z319,z8,z116,z2,z3,z4]),(0,[z621,z8,z0,z3,z4,z90])],[(0,[z36,z8,z401,z2,z3,z4]),(0,[z60,z8,z2,z176,z165,z6])],[(0,[z8,z0,z2,z3,z4,z1620]),(0,[z436,z0,z2,z3,z4,z11])]],
   [[(0,[z0,z1,z2,z3,z4,z92]),(0,[z0,z2,z3,z74,z4,z31]),(0,[z8,z0,z2,z3,z4,z1621])],[(0,[z1622,z8,z0,z2,z3,z4]),(0,[z8,z2,z3,z4,z371,z11])],[(0,[z17,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z367,z4,z31]),(0,[z8,z0,z2,z55,z4,z311])],[(0,[z64,z1,z2,z3,z4,z261]),(0,[z8,z0,z2,z3,z1580,z6])],[(0,[z8,z0,z2,z3,z4,z1623]),(0,[z8,z0,z2,z83,z4,z132]),(0,[z8,z0,z2,z3,z4,z1624])],[(0,[z8,z0,z2,z55,z3,z178]),(0,[z1625,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1626])],[(0,[z43,z1,z2,z3,z52,z6]),(0,[z8,z0,z2,z3,z1627,z6])],[(0,[z0,z1,z2,z3,z4,z108]),(0,[z71,z345,z2,z3,z4,z6]),(0,[z71,z0,z2,z76,z4,z31]),(0,[z51,z0,z2,z3,z321,z4]),(0,[z8,z0,z2,z1628,z4,z6])],[(0,[z0,z1,z2,z4,z726,z126]),(0,[z13,z1629,z0,z2,z3,z4]),(0,[z302,z0,z2,z3,z104,z6]),(0,[z8,z30,z2,z3,z81,z6])],[(0,[z425,z1,z2,z176,z4,z6]),(0,[z0,z182,z967,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1630]),(0,[z78,z0,z2,z3,z4,z1631]),(0,[z1632,z0,z2,z3,z4,z6]),(0,[z8,z0,z202,z3,z4,z289]),(0,[z1633,z0,z2,z3,z4,z6])],[(0,[z13,z230,z2,z3,z4,z6])],[(0,[z64,z1,z2,z3,z4,z31]),(0,[z86,z13,z0,z28,z4,z6]),(0,[z8,z0,z2,z3,z1634,z4]),(0,[z8,z0,z3,z4,z90,z713])],[(0,[z0,z1,z2,z49,z4,z6]),(0,[z1635,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1636])],[(0,[z0,z425,z1,z2,z55,z4]),(0,[z13,z0,z2,z3,z4,z1354])],[(0,[z0,z2,z3,z4,z104,z173]),(0,[z8,z0,z2,z1637,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1638]),(0,[z8,z64,z2,z3,z139,z4]),(0,[z8,z0,z2,z3,z742,z6])],[(0,[z1639,z8,z0,z2,z3,z4])],[(0,[z8,z0,z2,z3,z1640,z4]),(0,[z8,z233,z2,z213,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1641]),(0,[z8,z230,z2,z3,z4,z1011]),(0,[z396,z0,z2,z3,z217,z6]),(0,[z78,z0,z2,z3,z1642,z6]),(0,[z0,z2,z3,z1643,z4,z6])],[(0,[z0,z1094,z2,z3,z4,z6]),(0,[z8,z0,z439,z3,z5,z6]),(0,[z8,z0,z2,z3,z4,z1644]),(0,[z1645,z0,z2,z3,z4,z6])],[(0,[z13,z0,z2,z480,z4,z6]),(0,[z13,z0,z2,z3,z539,z6]),(0,[z325,z0,z531,z3,z4,z6]),(0,[z8,z0,z2,z1646,z3,z4]),(0,[z1647,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z126])],[(0,[z180,z0,z2,z3,z1245,z6]),(0,[z138,z8,z0,z55,z3,z82])],[(0,[z0,z2,z3,z4,z104,z252])],[(0,[z1,z2,z3,z4,z323,z6]),(0,[z1648,z0,z2,z3,z4,z6])],[(0,[z138,z8,z0,z3,z82,z20]),(0,[z8,z0,z202,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1649])],[(0,[z8,z0,z2,z1650,z3,z4])],[(1,[z1273,z2,z3,z4,z6]),(0,[z17,z1,z2,z3,z4,z192]),(0,[z13,z0,z1371,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1651]),(0,[z8,z0,z2,z3,z1652,z4]),(0,[z8,z879,z2,z3,z4,z6]),(0,[z1653,z0,z2,z3,z4,z6])],[(0,[z13,z0,z2,z3,z215,z6]),(0,[z8,z0,z357,z3,z165,z6]),(0,[z8,z0,z2,z144,z4,z598]),(0,[z36,z8,z0,z2,z550,z4]),(0,[z1654,z0,z2,z3,z4,z6])],[(0,[z8,z0,z1264,z2,z3,z4]),(0,[z8,z0,z2,z139,z28,z4]),(0,[z7,z8,z0,z149,z4,z90])],[(0,[z1,z2,z3,z4,z6,z339]),(0,[z96,z8,z2,z3,z139,z4]),(0,[z0,z89,z2,z3,z4,z20]),(0,[z8,z0,z2,z144,z19,z4]),(0,[z8,z0,z2,z1655,z3,z4]),(0,[z1549,z8,z0,z2,z213,z4])]],
   [[(0,[z1,z2,z3,z342,z4,z6]),(0,[z43,z1,z2,z3,z4,z31]),(0,[z8,z414,z2,z3,z4,z11]),(0,[z36,z8,z0,z2,z50,z4]),(0,[z36,z85,z0,z2,z3,z4]),(0,[z0,z2,z3,z1656,z4,z6])],[(0,[z0,z1,z2,z3,z1627,z6]),(0,[z36,z0,z1,z2,z55,z4]),(0,[z40,z0,z182,z3,z4,z6]),(0,[z8,z2,z3,z4,z11,z320]),(0,[z8,z0,z2,z3,z4,z917]),(0,[z14,z8,z0,z2,z103,z4])],[(0,[z8,z1,z2,z3,z4,z320]),(0,[z13,z0,z2,z3,z4,z232]),(0,[z8,z0,z1657,z2,z3,z4]),(0,[z36,z8,z64,z65,z3,z4]),(0,[z8,z0,z2,z3,z4,z1658]),(0,[z0,z1659,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1660]),(0,[z8,z0,z2,z1661,z174,z4]),(0,[z8,z0,z2,z3,z765,z11])],[(0,[z8,z1,z2,z3,z105,z6]),(0,[z8,z0,z2,z35,z4,z20]),(0,[z23,z426,z2,z3,z4,z6]),(0,[z51,z230,z2,z3,z52,z6]),(0,[z8,z0,z2,z3,z257,z31])],[],[(0,[z13,z0,z2,z3,z4,z1383]),(0,[z8,z457,z2,z3,z4,z387]),(0,[z8,z1662,z2,z3,z4,z6])],[(0,[z36,z8,z17,z2,z19,z4]),(0,[z8,z2,z439,z3,z5,z6])],[(0,[z8,z0,z2,z3,z4,z953]),(0,[z476,z0,z2,z3,z4,z31])],[(0,[z363,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z55,z3,z162]),(0,[z8,z0,z2,z3,z1663,z4]),(0,[z0,z2,z3,z4,z1664,z6]),(0,[z0,z346,z2,z3,z4,z11])],[(0,[z0,z1,z2,z3,z4,z1638]),(0,[z0,z1,z2,z3,z4,z153]),(0,[z13,z0,z531,z3,z4,z6]),(0,[z8,z401,z2,z3,z4,z9]),(0,[z8,z0,z2,z55,z367,z4])],[],[(0,[z8,z0,z2,z121,z52,z6]),(0,[z1432,z0,z2,z55,z3,z4])],[(0,[z1665,z8,z0,z2,z3,z4]),(0,[z1433,z0,z2,z55,z3,z4])],[(0,[z13,z1,z2,z3,z4,z9]),(0,[z8,z0,z110,z3,z4,z72]),(0,[z8,z451,z2,z3,z4,z9])],[(0,[z180,z0,z182,z3,z4,z6]),(0,[z0,z2,z3,z4,z757,z6])],[(0,[z0,z1,z2,z3,z4,z126]),(0,[z8,z0,z110,z76,z4,z6]),(0,[z27,z0,z2,z3,z74,z4]),(0,[z8,z0,z1666,z2,z3,z4]),(0,[z8,z451,z128,z3,z4,z6])],[(0,[z13,z36,z1,z2,z3,z4]),(0,[z8,z0,z2,z50,z4,z298])],[(0,[z8,z0,z2,z1667,z4,z6]),(0,[z43,z8,z2,z3,z5,z31])],[(0,[z13,z0,z2,z3,z105,z9]),(0,[z8,z0,z2,z3,z4,z1668]),(0,[z8,z0,z2,z3,z4,z1669])],[(0,[z0,z1,z202,z3,z4,z6]),(0,[z36,z8,z0,z2,z3,z1196])],[(0,[z123,z1,z2,z3,z4,z515]),(0,[z8,z0,z2,z3,z4,z360])],[(0,[z0,z1,z2,z3,z1075,z6]),(0,[z0,z1,z2,z1650,z3,z4]),(0,[z8,z0,z2,z3,z4,z1670]),(0,[z0,z167,z2,z55,z3,z4])],[(0,[z8,z0,z2,z4,z726,z6]),(0,[z8,z0,z2,z3,z137,z6]),(0,[z117,z8,z42,z3,z4,z31])],[(0,[z8,z0,z110,z3,z4,z31])],[(0,[z36,z1,z2,z3,z176,z4]),(0,[z0,z1,z2,z3,z4,z210]),(0,[z0,z346,z2,z3,z4,z326]),(0,[z1671,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1672])],[(0,[z8,z0,z2,z3,z1673,z6]),(0,[z8,z0,z2,z3,z4,z1674])],[(0,[z8,z0,z2,z3,z1675,z4]),(0,[z1,z2,z42,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z1676])],[(0,[z0,z1,z2,z3,z217,z6]),(0,[z8,z0,z2,z3,z334,z9]),(0,[z389,z0,z2,z3,z52,z6]),(0,[z8,z0,z2,z163,z4,z31]),(0,[z127,z0,z2,z3,z4,z1530]),(0,[z86,z8,z0,z301,z28,z4])],[(0,[z13,z0,z2,z3,z1400,z6]),(0,[z318,z0,z2,z3,z4,z1677]),(0,[z8,z0,z2,z3,z4,z1677]),(0,[z1526,z36,z0,z2,z3,z4])],[(0,[z8,z0,z2,z3,z1678,z6]),(0,[z8,z0,z2,z3,z4,z1679]),(0,[z51,z230,z2,z3,z4,z31])],[(0,[z13,z0,z2,z3,z4,z468]),(0,[z8,z0,z1680,z2,z3,z4]),(0,[z60,z8,z2,z176,z4,z31])]],
   [[(0,[z13,z310,z2,z3,z4,z6])],[(0,[z13,z0,z2,z1408,z4,z6]),(0,[z32,z0,z2,z3,z4,z9])],[(0,[z0,z2,z3,z4,z20,z126]),(0,[z8,z0,z2,z3,z4,z320]),(0,[z78,z457,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z137,z31])],[(0,[z13,z0,z2,z149,z4,z6]),(0,[z8,z0,z2,z1681,z4,z6])],[(0,[z8,z0,z2,z3,z105,z6]),(0,[z0,z1,z2,z3,z165,z6]),(0,[z34,z0,z54,z480,z4,z6]),(0,[z34,z0,z54,z3,z539,z6]),(0,[z8,z0,z2,z55,z3,z165])],[(0,[z36,z40,z0,z182,z3,z4]),(0,[z287,z8,z0,z2,z4,z114])],[(0,[z422,z1,z2,z3,z81,z6]),(1,[z0,z2,z3,z757,z6]),(0,[z0,z2,z3,z4,z274,z6]),(0,[z325,z0,z2,z55,z3,z4])],[(0,[z8,z0,z2,z3,z4,z1682]),(0,[z8,z0,z1683,z2,z3,z4]),(0,[z117,z396,z42,z3,z4,z6])],[(0,[z13,z0,z156,z2,z3,z4]),(0,[z450,z8,z0,z2,z3,z492]),(0,[z8,z233,z2,z3,z4,z412])],[(0,[z0,z2,z3,z4,z104,z31]),(0,[z1684,z8,z2,z3,z4,z6])],[(0,[z117,z8,z42,z367,z4,z6])],[(0,[z187,z8,z2,z3,z4,z9])],[],[(0,[z8,z426,z2,z3,z4,z9]),(0,[z0,z2,z3,z4,z109,z20])],[(0,[z13,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z1685,z4,z6]),(0,[z8,z0,z2,z35,z4,z387]),(0,[z8,z0,z2,z3,z1686,z6])],[(0,[z8,z0,z2,z3,z4,z289]),(0,[z8,z327,z2,z3,z4,z11]),(0,[z36,z0,z2,z3,z74,z4])],[(0,[z187,z1,z2,z3,z4,z6]),(0,[z396,z0,z2,z3,z4,z6]),(0,[z491,z0,z1,z2,z3,z4]),(0,[z0,z2,z3,z344,z104,z6]),(0,[z8,z0,z2,z3,z98,z47])],[(0,[z27,z0,z1,z2,z3,z4]),(0,[z8,z0,z2,z1687,z3,z4]),(0,[z0,z2,z3,z321,z4,z104]),(0,[z78,z0,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z1270]),(0,[z8,z451,z2,z3,z4,z11]),(0,[z7,z8,z0,z12,z3,z4])],[(0,[z1,z2,z3,z307,z4,z6]),(0,[z0,z1,z2,z4,z726,z6]),(0,[z0,z422,z2,z3,z52,z6]),(0,[z8,z0,z2,z146,z28,z4]),(0,[z119,z8,z2,z3,z4,z468])],[(0,[z0,z1,z2,z3,z4,z252]),(0,[z8,z0,z357,z3,z4,z6]),(0,[z8,z0,z202,z174,z4,z6]),(0,[z0,z2,z3,z98,z274,z47])],[(0,[z1093,z0,z2,z3,z4,z6]),(0,[z8,z1688,z2,z3,z4,z6]),(0,[z8,z0,z2,z146,z3,z4]),(0,[z127,z0,z2,z3,z4,z20]),(0,[z8,z0,z2,z3,z4,z1689]),(0,[z8,z17,z2,z19,z4,z6]),(0,[z8,z0,z651,z2,z224,z6])],[(0,[z411,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1690]),(0,[z1348,z8,z0,z2,z174,z4])],[(0,[z13,z0,z2,z3,z1427,z6]),(0,[z51,z0,z2,z3,z4,z473]),(0,[z389,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z301,z4]),(0,[z0,z1691,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1112])],[(0,[z13,z96,z2,z3,z4,z11]),(0,[z8,z0,z2,z3,z539,z20]),(0,[z8,z1692,z2,z3,z4,z6]),(0,[z8,z0,z2,z1693,z3,z4])],[(0,[z265,z0,z2,z3,z4,z20]),(0,[z1694,z0,z2,z3,z4,z6]),(0,[z8,z0,z18,z3,z4,z68])],[(0,[z8,z0,z2,z3,z4,z1695]),(0,[z8,z0,z2,z3,z998,z6]),(0,[z8,z0,z2,z1661,z3,z4]),(0,[z36,z8,z0,z2,z103,z4])],[(0,[z1696,z0,z2,z3,z4,z6])],[(0,[z13,z455,z2,z3,z4,z6]),(0,[z8,z0,z2,z1697,z3,z4]),(0,[z101,z0,z2,z3,z4,z9])],[(0,[z8,z0,z2,z3,z1001,z6]),(0,[z8,z401,z2,z3,z4,z1467]),(0,[z39,z0,z2,z3,z104,z9])],[(0,[z8,z2,z3,z4,z222,z320]),(0,[z1698,z8,z0,z2,z3,z4])],[],[(0,[z8,z0,z2,z3,z4,z6]),(0,[z318,z0,z2,z3,z4,z6]),(0,[z56,z0,z156,z2,z3,z4]),(0,[z8,z0,z2,z3,z835,z11]),(0,[z287,z8,z0,z2,z4,z305]),(0,[z1699,z0,z2,z3,z4,z6]),(0,[z10,z8,z0,z2,z224,z6])]],
   [[(0,[z13,z0,z2,z3,z178,z6]),(0,[z8,z0,z2,z3,z98,z474])],[(0,[z8,z0,z2,z3,z321,z4]),(0,[z0,z2,z3,z4,z1700,z6]),(0,[z8,z0,z2,z3,z4,z1701])],[(0,[z0,z89,z2,z3,z4,z261]),(0,[z36,z198,z0,z2,z3,z4]),(0,[z8,z0,z333,z383,z3,z4])],[(0,[z161,z1,z2,z3,z4,z6]),(0,[z1629,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z3,z1702,z6]),(0,[z1703,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z49,z4,z9]),(0,[z8,z0,z2,z3,z4,z713])],[(0,[z32,z0,z2,z3,z4,z11])],[(0,[z8,z0,z2,z3,z4,z222]),(0,[z8,z0,z2,z3,z4,z1329]),(0,[z597,z8,z0,z28,z4,z6])],[(0,[z0,z2,z3,z1704,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1705]),(0,[z0,z73,z2,z3,z4,z6]),(0,[z8,z0,z1706,z3,z4,z6]),(0,[z0,z2,z3,z4,z1707,z6])],[(0,[z1,z2,z3,z81,z4,z222]),(0,[z51,z0,z2,z3,z52,z9])],[(0,[z8,z64,z2,z3,z217,z6])],[(0,[z0,z1,z2,z3,z4,z289]),(0,[z0,z89,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z4,z1708]),(0,[z8,z0,z2,z3,z4,z1709])],[(0,[z0,z2,z3,z4,z222,z126])],[(0,[z8,z0,z2,z1710,z3,z4])],[(0,[z1,z2,z3,z81,z4,z31]),(0,[z8,z0,z2,z3,z1711,z4]),(0,[z8,z0,z531,z3,z4,z20]),(0,[z1712,z0,z2,z3,z4,z6]),(0,[z8,z0,z2,z144,z83,z4])],[(0,[z64,z1,z2,z3,z4,z381]),(0,[z40,z0,z247,z3,z4,z6]),(0,[z119,z436,z2,z3,z4,z6]),(0,[z396,z0,z2,z367,z4,z6]),(0,[z8,z0,z1713,z2,z3,z4]),(0,[z8,z17,z2,z19,z4,z192]),(0,[z1501,z0,z2,z55,z3,z4])],[(0,[z1,z2,z447,z3,z4,z6]),(0,[z0,z1,z2,z146,z3,z4]),(0,[z13,z0,z128,z3,z37,z6]),(0,[z8,z345,z2,z3,z4,z1304]),(0,[z40,z230,z2,z3,z4,z6]),(0,[z1714,z8,z0,z2,z3,z4])],[(0,[z36,z0,z1,z2,z3,z4]),(0,[z8,z0,z2,z3,z4,z1715]),(0,[z436,z0,z2,z55,z3,z4]),(0,[z8,z0,z2,z3,z4,z1716])],[(0,[z0,z1,z2,z3,z301,z4]),(0,[z8,z2,z3,z4,z6,z896])],[(0,[z0,z1717,z2,z3,z4,z6]),(0,[z8,z0,z214,z3,z4,z11]),(0,[z8,z0,z2,z3,z4,z1718]),(0,[z1719,z8,z0,z2,z3,z4])],[(0,[z8,z426,z2,z3,z4,z1452]),(0,[z8,z0,z1720,z3,z4,z6]),(0,[z8,z0,z2,z1029,z367,z4])],[(0,[z119,z8,z2,z3,z104,z6]),(0,[z78,z0,z2,z3,z4,z11]),(0,[z190,z0,z2,z146,z3,z4])],[(0,[z8,z0,z2,z3,z4,z1721]),(0,[z161,z8,z2,z3,z5,z6]),(0,[z8,z2,z3,z81,z1143,z6]),(0,[z8,z0,z2,z3,z4,z1722])],[(0,[z650,z0,z2,z3,z4,z31]),(0,[z8,z0,z439,z3,z4,z513]),(0,[z0,z2,z3,z1723,z4,z6])],[(0,[z457,z1,z2,z3,z4,z6]),(0,[z13,z0,z2,z3,z4,z446])],[(0,[z1724,z0,z2,z3,z4,z6])],[(0,[z8,z0,z2,z3,z4,z1725]),(0,[z8,z0,z2,z3,z4,z192]),(0,[z8,z0,z333,z3,z4,z90])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z252,z126]),(0,[z8,z0,z2,z3,z162,z9]),(0,[z8,z439,z3,z4,z5,z6]),(0,[z8,z233,z2,z3,z4,z11]),(0,[z8,z0,z2,z103,z4,z6]),(0,[z36,z715,z0,z2,z3,z4])],[(0,[z8,z0,z2,z3,z4,z1726]),(0,[z8,z0,z2,z1727,z3,z4]),(0,[z8,z0,z202,z121,z4,z6])],[(0,[z0,z1,z2,z3,z321,z4]),(0,[z13,z0,z2,z3,z162,z20])],[(0,[z0,z1,z2,z3,z4,z261]),(0,[z8,z0,z2,z3,z4,z1563]),(0,[z8,z0,z2,z3,z1461,z4]),(0,[z626,z0,z2,z3,z4,z20])],[(0,[z34,z0,z54,z3,z4,z9]),(0,[z40,z0,z967,z3,z4,z6])],[(0,[z39,z0,z2,z3,z104,z11]),(0,[z8,z0,z2,z1728,z4,z6]),(0,[z36,z8,z0,z1151,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z222]),(0,[z411,z0,z2,z3,z4,z31]),(0,[z1729,z8,z0,z2,z3,z4])],[(0,[z13,z0,z2,z3,z4,z326]),(0,[z0,z73,z2,z3,z4,z192]),(0,[z8,z0,z2,z1730,z3,z4])],[(0,[z8,z574,z2,z3,z81,z6])],[(0,[z1,z2,z470,z3,z4,z6]),(0,[z8,z0,z2,z3,z783,z6])],[(0,[z1731,z8,z0,z2,z3,z4]),(0,[z119,z8,z2,z3,z4,z11]),(0,[z628,z0,z2,z3,z4,z31]),(0,[z117,z8,z42,z163,z4,z6]),(0,[z0,z2,z3,z1732,z4,z6]),(0,[z436,z0,z2,z3,z4,z1446]),(0,[z8,z0,z2,z884,z3,z4])],[(0,[z13,z0,z116,z2,z3,z4]),(0,[z451,z1717,z2,z3,z4,z6])],[(0,[z8,z1435,z2,z3,z4,z6]),(0,[z8,z0,z2,z149,z4,z20])],[(0,[z8,z0,z932,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1180])],[(0,[z1733,z8,z0,z2,z3,z4])],[(0,[z644,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1631]),(0,[z8,z0,z2,z174,z4,z289])],[(0,[z0,z2,z3,z38,z4,z175])],[(0,[z8,z0,z2,z213,z4,z6]),(0,[z318,z0,z2,z213,z4,z6])],[(0,[z36,z8,z0,z2,z35,z4]),(0,[z61,z0,z531,z3,z4,z6])],[(0,[z451,z1,z2,z3,z4,z6]),(0,[z8,z0,z2,z3,z4,z1734])],[(0,[z1735,z8,z0,z2,z3,z4]),(0,[z8,z0,z2,z55,z3,z769])],[(0,[z0,z2,z3,z4,z538,z31]),(0,[z411,z0,z2,z3,z4,z192]),(0,[z8,z170,z2,z3,z4,z9])],[(0,[z34,z0,z54,z3,z178,z6]),(0,[z308,z8,z0,z3,z4,z90])],[],[(0,[z87,z1,z2,z3,z4,z6]),(0,[z13,z36,z0,z2,z4,z114]),(0,[z8,z0,z2,z3,z1642,z6]),(0,[z36,z265,z0,z2,z3,z4])],[(0,[z43,z13,z2,z3,z5,z6]),(0,[z413,z0,z2,z3,z4,z31]),(0,[z8,z0,z2,z3,z217,z9]),(0,[z8,z0,z2,z144,z28,z4])],[(0,[z0,z1,z2,z3,z4,z192]),(0,[z8,z0,z2,z55,z286,z4]),(0,[z8,z670,z2,z3,z4,z9])],[(0,[z0,z1,z2,z103,z4,z6]),(0,[z61,z0,z2,z3,z4,z1392]),(0,[z1736,z0,z2,z3,z4,z6])],[(0,[z230,z2,z3,z4,z6,z31]),(0,[z60,z8,z2,z159,z176,z4])],[(0,[z17,z1,z2,z3,z4,z11]),(0,[z8,z1737,z2,z3,z4,z6]),(0,[z86,z8,z0,z28,z4,z9]),(0,[z8,z0,z2,z3,z1738,z4])],[(0,[z117,z13,z42,z3,z4,z6]),(0,[z8,z230,z2,z3,z4,z31])],[(0,[z13,z0,z540,z2,z3,z4]),(0,[z0,z2,z3,z4,z175,z6]),(0,[z8,z0,z2,z174,z4,z6]),(0,[z138,z8,z233,z3,z82,z6])],[(0,[z8,z0,z2,z3,z4,z405]),(0,[z85,z0,z2,z3,z4,z1369]),(0,[z1739,z0,z2,z3,z4,z6]),(0,[z0,z346,z2,z55,z3,z4])],[(0,[z8,z0,z2,z3,z165,z9])],[(0,[z8,z0,z2,z3,z4,z1740]),(0,[z8,z0,z2,z3,z4,z1185]),(0,[z8,z0,z2,z3,z4,z1522])],[(0,[z0,z422,z2,z3,z4,z126]),(0,[z8,z0,z2,z3,z4,z1741]),(0,[z8,z230,z2,z3,z4,z130]),(0,[z8,z30,z2,z3,z81,z11]),(0,[z8,z0,z2,z55,z3,z995])],[(0,[z78,z36,z0,z2,z3,z4]),(0,[z62,z8,z2,z3,z4,z9]),(0,[z8,z0,z2,z3,z4,z1742]),(0,[z1635,z0,z2,z3,z74,z4])],[(0,[z1743,z8,z0,z2,z3,z4]),(0,[z1744,z0,z2,z3,z4,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 32 1024 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 456) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 456).take 450) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 906).take 453) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1359).take 452) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1811)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [456, 450, 453, 452] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 135).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 135).take 135).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 270).take 126).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 396).take 128).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 524).take 118).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 642).take 130).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 772).take 142).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc7 : chunkOK 5 ((bkB.flatten.drop 914).take 110).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 1024)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [135, 135, 126, 128, 118, 130, 142, 110] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_cons pc7 (windowsF_nil pcend))))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 32) (nb2 := 1024) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_36306

theorem PEqualNP.Outside.L_meta_36306 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4277074656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4277074656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36306.solve