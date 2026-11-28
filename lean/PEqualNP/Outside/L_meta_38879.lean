import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38879

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
  Nat.testBit (4276808936 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00216702c61c6316#64 ++ 0x400216702c61c631#64 ++ 0xb067ef07c63ce73f#64 ++ 0xab067ef07c63ce73#64 : BitVec 256),
   (0x008b016946c52944#64 ++ 0x8008b016946c5294#64 ++ 0xd19b13f9c7c739cf#64 ++ 0x7d19b13f9c7c739c#64 : BitVec 256),
   (0x26141814180294a9#64 ++ 0x026141814180294a#64 ++ 0xee1c1c1e3807fffe#64 ++ 0xfee1c1c1e3807fff#64 : BitVec 256),
   (0x1b601fa02b683e0e#64 ++ 0x01b601fa02b683e0#64 ++ 0x7fe01fe03ff83e0d#64 ++ 0xf7fe01fe03ff83e0#64 : BitVec 256),
   (0x4ddfa00035b7c000#64 ++ 0x04ddfa00035b7c00#64 ++ 0x7fffe0003fffc00b#64 ++ 0xe7fffe0003fffc00#64 : BitVec 256),
   (0x8ffededf80000000#64 ++ 0x08ffededf8000000#64 ++ 0x8fffffffc0000007#64 ++ 0xf8fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [12, 8]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0001010046042104 0x0000101004604210 0x90030301c604210f 0x290030301c604210

def z1 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xb067ef07c63ce73f 0xab067ef07c63ce73

def z2 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xd19b13f9c7c739cf 0x7d19b13f9c7c739c

def z3 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe01fe03ff83e0d 0xf7fe01fe03ff83e0

def z4 : W := mkw 0x26141814180294a9 0x026141814180294a 0xee1c1c1e3807fffe 0xfee1c1c1e3807fff

def z5 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z6 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xeffffffff807ffff 0xfeffffffff807fff

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0040c060004e73e 0xaa0040c060004e73

def z8 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x1063e301c6380001 0x01063e301c638000

def z9 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8fffffffc0000007 0xf8fffffffc000000

def z10 : W := mkw 0x008a006900c10840 0x8008a006900c1084 0xc19b13f9c1c318c7 0x7c19b13f9c1c318c

def z11 : W := mkw 0x00ab676bc6dd6b56 0xc00ab676bc6dd6b5 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z12 : W := mkw 0x8f74de9680000000 0x08f74de968000000 0x0e64ec0600000000 0x80e64ec060000000

def z13 : W := mkw 0x8fded8df80000000 0x08fded8df8000000 0x8f9ff0ffc0000002 0x58f9ff0ffc000000

def z14 : W := mkw 0x1b607e82a938561a 0x41b607e82a938561 0x2e64ec063838c630 0x82e64ec063838c63

def z15 : W := mkw 0x8dfec6df80000000 0x08dfec6df8000000 0x81ffe3ffc0000003 0x081ffe3ffc000000

def z16 : W := mkw 0x0940000021200000 0x0094000002120000 0x7fe000003ff80009 0xe7fe000003ff8000

def z17 : W := mkw 0x849ec05f80000000 0x0849ec05f8000000 0x801fe01fc0000002 0x0801fe01fc000000

def z18 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x01e3e3e1c0000001 0x001e3e3e1c000000

def z19 : W := mkw 0x26141814180294a9 0x026141814180294a 0xce181018380739ce 0x7ce181018380739c

def z20 : W := mkw 0x0200180008001408 0x0020018000800140 0xee181c1838073fce 0xfee181c1838073fc

def z21 : W := mkw 0x82205edf80000000 0x082205edf8000000 0x80001fffc0000004 0x180001fffc000000

def z22 : W := mkw 0x9ffedfffab683e0e 0x09ffedfffab683e0 0xfffffffffff83e0f 0xffffffffffff83e0

def z23 : W := mkw 0x6f54b8143932d4a9 0x06f54b8143932d4a 0x2e64ec063838c630 0x82e64ec063838c63

def z24 : W := mkw 0xcf74fe96b132c000 0x0cf74fe96b132c00 0x2e64ec063838c000 0x82e64ec063838c00

def z25 : W := mkw 0x0001200004144000 0x0000120000414400 0x3067e000063cc00b 0xa3067e000063cc00

def z26 : W := mkw 0x4ddf816977e7a944 0x84ddf816977e7a94 0xdf9b13f9ffc739cf 0x7df9b13f9ffc739c

def z27 : W := mkw 0x0000012002402804 0x0000001200240280 0x118003e007c00001 0x0118003e007c0000

def z28 : W := mkw 0x249f005d548781e1 0x8249f005d548781e 0x801f001fc007c1f2 0x0801f001fc007c1f

def z29 : W := mkw 0x8fffdfffc6c52944 0x88fffdfffc6c5294 0xdfffffffc7c739cf 0xfdfffffffc7c739c

def z30 : W := mkw 0xdfffffffbffffe0e 0x0dfffffffbffffe0 0xfffffffffffffe0f 0xffffffffffffffe0

def z31 : W := mkw 0x0414000010028000 0x0041400001002800 0x6e1c00003807c00a 0xe6e1c00003807c00

def z32 : W := mkw 0x6fdfb8143db7d4a9 0x06fdfb8143db7d4a 0xfffffc1e3fffffff 0xffffffc1e3ffffff

def z33 : W := mkw 0x0b601e8021200000 0x00b601e802120000 0x7fe01fe03ff8000d 0xf7fe01fe03ff8000

def z34 : W := mkw 0x9fffffffef7c7f1e 0x49fffffffef7c7f1 0xfffffffffffcff3f 0xffffffffffffcff3

def z35 : W := mkw 0x22001814080014a9 0x022001814080014a 0x80001c1e00003ff4 0x180001c1e00003ff

def z36 : W := mkw 0x8dfec6cb80000000 0x08dfec6cb8000000 0x0fffe3e1c0000003 0xe0fffe3e1c000000

def z37 : W := mkw 0x49cba00025b54000 0x049cba00025b5400 0x11e3e00007f80001 0x011e3e00007f8000

def z38 : W := mkw 0xc49fe05f9497c000 0x0c49fe05f9497c00 0x801fe01fc007c002 0x0801fe01fc007c00

def z39 : W := mkw 0xcffffedfb5b7c000 0x0cffffedfb5b7c00 0xffffffffffffc00f 0xfffffffffffffc00

def z40 : W := mkw 0x9b605fffab683e0e 0x09b605fffab683e0 0xffe01ffffff83e0d 0xfffe01ffffff83e0

def z41 : W := mkw 0x4d55a0003536c000 0x04d55a0003536c00 0x3e67e0003e3cc00b 0xa3e67e0003e3cc00

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0x3060000006380009 0xa306000000638000

def z43 : W := mkw 0x1b617fa2ef7c7f1e 0x41b617fa2ef7c7f1 0xffe7ffe7fffcff3f 0xfffe7ffe7fffcff3

def z44 : W := mkw 0x3f741fb43b6abeaf 0x03f741fb43b6abea 0xfffc1ffe3fffffff 0xffffc1ffe3ffffff

def z45 : W := mkw 0x26141814180294a9 0x026141814180294a 0x6e181c1838033ecc 0xf6e181c1838033ec

def z46 : W := mkw 0x0614181400000000 0x0061418140000000 0x0e18101800000000 0x50e1810180000000

def z47 : W := mkw 0x0b601fa002402804 0x00b601fa00240280 0x5fe01fe007c0380d 0xf5fe01fe007c0380

def z48 : W := mkw 0x196007a023682a06 0x0196007a023682a0 0x11e003e007f80001 0x011e003e007f8000

def z49 : W := mkw 0xa6345edf980294a9 0x0a6345edf980294a 0xee1c1ffff807fffe 0xfee1c1ffff807fff

def z50 : W := mkw 0x02201f000a08360e 0x002201f000a08360 0x7e601f003e383e0d 0xf7e601f003e383e0

def z51 : W := mkw 0x00204702c2082316 0x400204702c208231 0x80000f07c0002734 0x080000f07c000273

def z52 : W := mkw 0x00012100461c6316 0x400012100461c631 0x30000000063ce738 0x030000000063ce73

def z53 : W := mkw 0x100001202b683e0e 0x0100001202b683e0 0x700000003ff83e08 0x0700000003ff83e0

def z54 : W := mkw 0x0200180008001408 0x0020018000800140 0x6e001c0038003e0c 0xf6e001c0038003e0

def z55 : W := mkw 0x0b601e8000000000 0x00b601e800000000 0x0fe01fe000000005 0xf0fe01fe00000000

def z56 : W := mkw 0xcfde98dd31a38000 0x0cfde98dd31a3800 0x4f9810f839c30000 0x54f9810f839c3000

def z57 : W := mkw 0x26357f16de1ef7bf 0x426357f16de1ef7b 0xfe7fff1ffe3fffff 0xffe7fff1ffe3ffff

def z58 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0xfffff0183ffff9cf 0xffffff0183ffff9c

def z59 : W := mkw 0x8fde98fd00c10840 0x88fde98fd00c1084 0x4f9810f801c318c0 0x54f9810f801c318c

def z60 : W := mkw 0x0020660280184212 0x4002066028018421 0xa067ef07c038c637 0xaa067ef07c038c63

def z61 : W := mkw 0x24140014100280a1 0x024140014100280a 0x801c001e0007c1f2 0x0801c001e0007c1f

def z62 : W := mkw 0x0001012046442904 0x0000101204644290 0xd18313e1c7c4390f 0x7d18313e1c7c4390

def z63 : W := mkw 0x0001012046c52944 0x80001012046c5294 0x5000000007c739c8 0x05000000007c739c

def z64 : W := mkw 0x8beadecb80000000 0x08beadecb8000000 0x0fe3ffe1c0000005 0xf0fe3ffe1c000000

def z65 : W := mkw 0x008a006900c10840 0x8008a006900c1084 0x419810f801c318c0 0x5419810f801c318c

def z66 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0xffe41fe63ffcff3f 0xfffe41fe63ffcff3

def z67 : W := mkw 0x0000016942402944 0x8000001694240294 0x800013f9c00039c4 0x1800013f9c00039c

def z68 : W := mkw 0x4d54a0003132c000 0x04d54a0003132c00 0x2e64e0003838c000 0x82e64e0003838c00

def z69 : W := mkw 0x8ffededf90028000 0x08ffededf9002800 0xeffffffff807c00f 0xfeffffffff807c00

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z71 : W := mkw 0x0001016946c52944 0x80001016946c5294 0xd00013f9c7c739cc 0x1d00013f9c7c739c

def z72 : W := mkw 0x0001200004144000 0x0000120000414400 0x0007e0000004c002 0x00007e0000004c00

def z73 : W := mkw 0x1bca18e929e11c48 0x81bca18e929e11c4 0x4f9810f839c318c0 0x54f9810f839c318c

def z74 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x9067e307c63cc133 0x09067e307c63cc13

def z75 : W := mkw 0x449fa0001497c000 0x0449fa0001497c00 0x001fe0000007c002 0x0001fe0000007c00

def z76 : W := mkw 0x0001012046c52944 0x80001012046c5294 0xd018101807c739ce 0x7d018101807c739c

def z77 : W := mkw 0x00204702c2082316 0x400204702c208231 0x8067ef07c0002737 0xa8067ef07c000273

def z78 : W := mkw 0x6fde981439a394a9 0x06fde981439a394a 0x4f98101839c318c0 0x54f98101839c318c

def z79 : W := mkw 0x8f74de9680000000 0x08f74de968000000 0x8e67ef07c0000007 0xa8e67ef07c000000

def z80 : W := mkw 0x4dde800031a38000 0x04dde800031a3800 0x4f98000039c30000 0x44f98000039c3000

def z81 : W := mkw 0xcffededfb1a38000 0x0cffededfb1a3800 0xcffffffff9c30007 0xfcffffffff9c3000

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0x80180018000701c2 0x080180018000701c

def z83 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0181018000739ce 0x7c0181018000739c

def z84 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x3fe7e0003ff8c001 0x83fe7e0003ff8c00

def z85 : W := mkw 0x4ddfa16977f7e944 0x84ddfa16977f7e94 0xfffff3f9fffff9cf 0xffffff3f9fffff9c

def z86 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x9067ef07c6380007 0xa9067ef07c638000

def z87 : W := mkw 0x0020460280000000 0x0002046028000000 0x8067ef07c0000007 0xa8067ef07c000000

def z88 : W := mkw 0x008a004900000000 0x0008a00490000000 0x819b13f9c0000007 0x7819b13f9c000000

def z89 : W := mkw 0x22001814080014a9 0x022001814080014a 0x00000c0600000630 0x000000c060000063

def z90 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x5fe013e03ff81801 0x55fe013e03ff8180

def z91 : W := mkw 0x4001212077f7e944 0x84001212077f7e94 0x700000003ffff9c8 0x0700000003ffff9c

def z92 : W := mkw 0x0200180008001408 0x0020018000800140 0x00001c0000003e04 0x100001c0000003e0

def z93 : W := mkw 0x8ffededf88001408 0x08ffededf8800140 0xeffffffff8003e0f 0xfeffffffff8003e0

def z94 : W := mkw 0x26357f16de1ef7bf 0x426357f16de1ef7b 0xbe67ef07fe3ce73f 0xabe67ef07fe3ce73

def z95 : W := mkw 0x0ddf800004850000 0x00ddf80000485000 0x5fffe00007c7000b 0xe5fffe00007c7000

def z96 : W := mkw 0x069f197d46c52944 0x8069f197d46c5294 0xdf9f1fffc7c739cf 0xfdf9f1fffc7c739c

def z97 : W := mkw 0x12201fa02b683e0e 0x012201fa02b683e0 0x70001fe03ff83e0c 0x170001fe03ff83e0

def z98 : W := mkw 0x12201fa00a483e0e 0x012201fa00a483e0 0x00001fe000003e04 0x100001fe000003e0

def z99 : W := mkw 0x22001814080014a9 0x022001814080014a 0xa0041c1e0004fffe 0xba0041c1e0004fff

def z100 : W := mkw 0x1b601e802928160a 0x01b601e802928160 0x2e600c0038380600 0x82e600c003838060

def z101 : W := mkw 0x1beb1fe96fed3f4e 0x81beb1fe96fed3f4 0xfffb1ff9ffff3fcf 0xffffb1ff9ffff3fc

def z102 : W := mkw 0x09cb000025a50000 0x009cb000025a5000 0x7ffb00003fff000b 0xe7ffb00003fff000

def z103 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x118303e1c7c00001 0x0118303e1c7c0000

def z104 : W := mkw 0x7fffbfb43ffffeaf 0x07fffbfb43ffffea 0xfffffffe3fffffff 0xffffffffe3ffffff

def z105 : W := mkw 0x0020660280184212 0x4002066028018421 0x2064ec060038c630 0x82064ec060038c63

def z106 : W := mkw 0x008b014946042104 0x0008b01494604210 0x919b13f9c604210f 0x7919b13f9c604210

def z107 : W := mkw 0x1beb1fa02fed3e0e 0x01beb1fa02fed3e0 0x7ffb1fe03fff3e0f 0xf7ffb1fe03fff3e0

def z108 : W := mkw 0x0dde804900000000 0x00dde80490000000 0x8ffff3f9c0000007 0xf8ffff3f9c000000

def z109 : W := mkw 0x20000000080014a9 0x020000000080014a 0x0000000000003ff0 0x00000000000003ff

def z110 : W := mkw 0x26141814180294a9 0x026141814180294a 0x4e181018380318c0 0x54e181018380318c

def z111 : W := mkw 0x028b19694ec53d4c 0x8028b19694ec53d4 0xff9b1ff9ffc73fcf 0xfff9b1ff9ffc73fc

def z112 : W := mkw 0x89ebe7cbc61c6316 0x489ebe7cbc61c631 0xb1e7efe7c63ce73f 0xab1e7efe7c63ce73

def z113 : W := mkw 0x1b4018a029601c08 0x01b4018a029601c0 0x7fe010e03ff81809 0xf7fe010e03ff8180

def z114 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x0fe7efe7c0000001 0x80fe7efe7c000000

def z115 : W := mkw 0x4fffbe8035b7c000 0x04fffbe8035b7c00 0x7fffffe03fffc00f 0xf7fffffe03fffc00

def z116 : W := mkw 0x99eac7eba3682a06 0x099eac7eba3682a0 0x11e3e3e1c7f80001 0x011e3e3e1c7f8000

def z117 : W := mkw 0x0000010042082316 0x4000001004208231 0x0000000000002730 0x0000000000000273

def z118 : W := mkw 0x89ebe7cbc61c6316 0x489ebe7cbc61c631 0x11e3e3e1c6380001 0x011e3e3e1c638000

def z119 : W := mkw 0x82205fffc2402944 0x882205fffc240294 0x80001fffc00039c4 0x180001fffc00039c

def z120 : W := mkw 0x8ddec05f80000000 0x08ddec05f8000000 0x8fffe01fc0000003 0xe8fffe01fc000000

def z121 : W := mkw 0x22001814080014a9 0x022001814080014a 0x00001018000018c0 0x100001018000018c

def z122 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xf07fff1fc63fffff 0xff07fff1fc63ffff

def z123 : W := mkw 0x26141814180294a9 0x026141814180294a 0x6e040c063807fff8 0x86e040c063807fff

def z124 : W := mkw 0x8960c68280000000 0x08960c6828000000 0x0060e00000000000 0x00060e0000000000

def z125 : W := mkw 0x1b601ea029681e0a 0x01b601ea029681e0 0x6fe01ce039f81e00 0xd6fe01ce039f81e0

def z126 : W := mkw 0x008b004944850140 0x8008b00494485014 0x801b0019c00701c2 0x0801b0019c00701c

def z127 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0xfff81ff83fff3fcf 0xffff81ff83fff3fc

def z128 : W := mkw 0x200101205ec7bded 0x8200101205ec7bde 0x700000003fc7fff8 0x0700000003fc7fff

def z129 : W := mkw 0x0f741e9400000000 0x00f741e940000000 0x8ffc1ffe00000007 0xf8ffc1ffe0000000

def z130 : W := mkw 0x00012100461c6316 0x400012100461c631 0xb0040c06063ce73e 0xab0040c06063ce73

def z131 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0xffffec063fffe73f 0xeffffec063fffe73

def z132 : W := mkw 0x0020460280080212 0x4002046028008021 0x00000c0600000630 0x000000c060000063

def z133 : W := mkw 0x1b605fa2eb683f1e 0x41b605fa2eb683f1 0xffe01fe7fff83f3d 0xfffe01fe7fff83f3

def z134 : W := mkw 0x20000000180294a9 0x020000000180294a 0x600000003807fff8 0x0600000003807fff

def z135 : W := mkw 0x1b4018a029601c08 0x01b4018a029601c0 0x4f8010e039c01800 0x54f8010e039c0180

def z136 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x5ffbe0003ffb0001 0x45ffbe0003ffb000

def z137 : W := mkw 0x300001203b6abeaf 0x0300001203b6abea 0x700000003ffffff8 0x0700000003ffffff

def z138 : W := mkw 0x49cba00025b54000 0x049cba00025b5400 0x7fe3e0003ff80009 0xe7fe3e0003ff8000

def z139 : W := mkw 0x008a004900000000 0x0008a00490000000 0xc19b13f9c00739cf 0x7c19b13f9c00739c

def z140 : W := mkw 0x26157816dc16d5b9 0x426157816dc16d5b 0xee1ffc1ff807fffe 0xfee1ffc1ff807fff

def z141 : W := mkw 0x49ebe702e7bd6316 0x449ebe702e7bd631 0x11e3e301c7f80001 0x011e3e301c7f8000

def z142 : W := mkw 0x1b605fa2ab683e0e 0x01b605fa2ab683e0 0xffe7ffe7fff83e0f 0xfffe7ffe7fff83e0

def z143 : W := mkw 0x8ffedfffc2402944 0x88ffedfffc240294 0x8fffffffc00039c7 0xf8fffffffc00039c

def z144 : W := mkw 0x108b01696fed3f4e 0x8108b01696fed3f4 0xf19b13f9ffff3fcf 0x7f19b13f9ffff3fc

def z145 : W := mkw 0x4dde800031a38000 0x04dde800031a3800 0x7ff800003ffb0009 0xe7ff800003ffb000

def z146 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7e600c003ff83e08 0x87e600c003ff83e0

def z147 : W := mkw 0x0ddfa00004144000 0x00ddfa0000414400 0x3fffe000063cc00b 0xe3fffe000063cc00

def z148 : W := mkw 0x0dde800000000000 0x00dde80000000000 0x0fffe00000000003 0xe0fffe0000000000

def z149 : W := mkw 0x00016102c61c6316 0x400016102c61c631 0xb007e007c63ce73a 0x0b007e007c63ce73

def z150 : W := mkw 0x8beadedf80000000 0x08beadedf8000000 0x81e3ffffc0000005 0x181e3ffffc000000

def z151 : W := mkw 0x49ebe702e7bd6316 0x449ebe702e7bd631 0xb1e7ef07c7fce73f 0xab1e7ef07c7fce73

def z152 : W := mkw 0x4ddfa04975b7c140 0x84ddfa04975b7c14 0xffffe019ffffc1cb 0xeffffe019ffffc1c

def z153 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x3067ef07c638c631 0x83067ef07c638c63

def z154 : W := mkw 0x26141814180294a9 0x026141814180294a 0x6e1c0c063807c63a 0xe6e1c0c063807c63

def z155 : W := mkw 0x2f741e94180294a9 0x02f741e94180294a 0xeffc1ffe3807ffff 0xfeffc1ffe3807fff

def z156 : W := mkw 0x802046cb80000000 0x0802046cb8000000 0x000003e1c0000000 0x0000003e1c000000

def z157 : W := mkw 0x008b014946852144 0x8008b01494685214 0x901b0319c60721cf 0x2901b0319c60721c

def z158 : W := mkw 0xaffededf900280a1 0x0affededf900280a 0x8fffffffc007c1f7 0xf8fffffffc007c1f

def z159 : W := mkw 0x20000000180294a9 0x020000000180294a 0x200000003800c630 0x0200000003800c63

def z160 : W := mkw 0x49ca800021a10000 0x049ca800021a1000 0x0180000001c00000 0x00180000001c0000

def z161 : W := mkw 0x1b613fa02f7c7e0e 0x01b613fa02f7c7e0 0x7fe7ffe03ffcfe0f 0xf7fe7ffe03ffcfe0

def z162 : W := mkw 0x261419341a42bcad 0x0261419341a42bca 0xff9c1ffe3fc7ffff 0xfff9c1ffe3fc7fff

def z163 : W := mkw 0x26141814180294a9 0x026141814180294a 0x2e040c063800c630 0x82e040c063800c63

def z164 : W := mkw 0x4ddfa10077b7e104 0x04ddfa10077b7e10 0xffffe301ffffe10f 0xeffffe301ffffe10

def z165 : W := mkw 0x8414c01680000000 0x08414c0168000000 0x0004e00600000000 0x00004e0060000000

def z166 : W := mkw 0x4001200035b7c000 0x04001200035b7c00 0x700000003fffc008 0x0700000003fffc00

def z167 : W := mkw 0x2f541814392294a9 0x02f541814392294a 0xfffc1c1e3fffffff 0xffffc1c1e3ffffff

def z168 : W := mkw 0x4dffe602b5bfc212 0x44dffe602b5bfc21 0x7fffec063fffc63b 0xe7fffec063fffc63

def z169 : W := mkw 0x649fa0141497c0a1 0x0649fa0141497c0a 0x801fe01e0007c1f2 0x0801fe01e0007c1f

def z170 : W := mkw 0xaffededf880014a9 0x0affededf880014a 0x8fffffffc0003ff7 0xf8fffffffc0003ff

def z171 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000000004210e 0x2800000000004210

def z172 : W := mkw 0x06345e1680000000 0x006345e168000000 0x8e7fff1fc0000007 0xf8e7fff1fc000000

def z173 : W := mkw 0x26141814180294a9 0x026141814180294a 0x6e1c10183807d8ca 0xf6e1c10183807d8c

def z174 : W := mkw 0x5ffe9fa03bebbe0e 0x05ffe9fa03bebbe0 0x7ff81fe03ffb3e0d 0xf7ff81fe03ffb3e0

def z175 : W := mkw 0x3fff1ffd7fefbfef 0x83fff1ffd7fefbfe 0xffff1fffffffffff 0xfffff1ffffffffff

def z176 : W := mkw 0x8f75ff96c61c6316 0x48f75ff96c61c631 0xbe67ef07c63ce73f 0xabe67ef07c63ce73

def z177 : W := mkw 0x9ffedfff8a483e0e 0x09ffedfff8a483e0 0x8fffffffc0003e07 0xf8fffffffc0003e0

def z178 : W := mkw 0x8fde98dd00000000 0x08fde98dd0000000 0x0f9810f800000000 0x50f9810f80000000

def z179 : W := mkw 0x269e185d180294a9 0x0269e185d180294a 0xef9f1ffff807ffff 0xfef9f1ffff807fff

def z180 : W := mkw 0x02217f02ce1c771e 0x402217f02ce1c771 0xfe67ff07fe3cff3f 0xffe67ff07fe3cff3

def z181 : W := mkw 0x44bfe702d69fe316 0x444bfe702d69fe31 0xb07fef07c63fe73f 0xab07fef07c63fe73

def z182 : W := mkw 0xcffffedfa5b54000 0x0cffffedfa5b5400 0x9fffffffc7f80007 0xf9fffffffc7f8000

def z183 : W := mkw 0x1bea1fe92be93e4e 0x81bea1fe92be93e4 0x7ff81ff83ffb3ecd 0xf7ff81ff83ffb3ec

def z184 : W := mkw 0x00ab476bc6c52944 0x800ab476bc6c5294 0xd1ffffffc7c739cf 0xfd1ffffffc7c739c

def z185 : W := mkw 0x0614181410028000 0x0061418141002800 0xee1c1c1e3807c00e 0xfee1c1c1e3807c00

def z186 : W := mkw 0x0001212046dd6b56 0xc0001212046dd6b5 0x7000000007fffff8 0x07000000007fffff

def z187 : W := mkw 0x00016002c4144110 0x400016002c414411 0x8007e007c004c132 0x08007e007c004c13

def z188 : W := mkw 0x0000006900400840 0x8000000690040084 0x000010f8000018c0 0x1000010f8000018c

def z189 : W := mkw 0x8ffedeff80c10840 0x88ffedeff80c1084 0xcfffffffc1c318c7 0xfcfffffffc1c318c

def z190 : W := mkw 0x0001012046c52944 0x80001012046c5294 0xd0030301c7c739cf 0x2d0030301c7c739c

def z191 : W := mkw 0xafffdfffdec7bded 0x8afffdfffdec7bde 0xffffffffffc7ffff 0xfffffffffffc7fff

def z192 : W := mkw 0x0001012046c52944 0x80001012046c5294 0x1000000007c00000 0x01000000007c0000

def z193 : W := mkw 0xcdffe6cbb5b7c000 0x0cdffe6cbb5b7c00 0x7fffe3e1ffffc00b 0xe7fffe3e1ffffc00

def z194 : W := mkw 0x89ca80c900000000 0x089ca80c90000000 0x018000e000000000 0x0018000e00000000

def z195 : W := mkw 0x0001210046146104 0x0000121004614610 0xb067e301c63ce10f 0xab067e301c63ce10

def z196 : W := mkw 0xaf74de96980294a9 0x0af74de96980294a 0xee7cfc1e3807fffe 0xfee7cfc1e3807fff

def z197 : W := mkw 0x669fb8141c97d4a9 0x0669fb8141c97d4a 0xee1ffc1e3807fffe 0xfee1ffc1e3807fff

def z198 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x519b13f9c7c318c1 0x5519b13f9c7c318c

def z199 : W := mkw 0x1b4018a029601c08 0x01b4018a029601c0 0x6f801ce039c03e0c 0xf6f801ce039c03e0

def z200 : W := mkw 0xbffedfffbb6abeaf 0x0bffedfffbb6abea 0xffffffffffffffff 0xffffffffffffffff

def z201 : W := mkw 0x8fde98dd00000000 0x08fde98dd0000000 0x8f9c1cfe00000006 0xf8f9c1cfe0000000

def z202 : W := mkw 0x0614181400000000 0x0061418140000000 0x8e1c1c1e00000006 0xf8e1c1c1e0000000

def z203 : W := mkw 0x008b216946d56944 0x8008b216946d5694 0xf1fff3f9c7fff9cf 0xff1fff3f9c7fff9c

def z204 : W := mkw 0x26141814180294a9 0x026141814180294a 0xce181c1e38033ff4 0x5ce181c1e38033ff

def z205 : W := mkw 0x049f000014878000 0x0049f00001487800 0x7f9f00003fc7c00b 0xe7f9f00003fc7c00

def z206 : W := mkw 0x0021660284144000 0x0002166028414400 0xb067ef07c63cc00f 0xab067ef07c63cc00

def z207 : W := mkw 0x8fffffffc6dd6b56 0xc8fffffffc6dd6b5 0xffffffffc7ffffff 0xfffffffffc7fffff

def z208 : W := mkw 0x26341f141a0ab6af 0x026341f141a0ab6a 0xfe7c1f1e3e3fffff 0xffe7c1f1e3e3ffff

def z209 : W := mkw 0x0020070002082206 0x0002007000208220 0x30600f000638260d 0xa30600f000638260

def z210 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xcffffffff80318c7 0xfcffffffff80318c

def z211 : W := mkw 0x1b4019a02b683e0e 0x01b4019a02b683e0 0x7f8010e03ff83e08 0x57f8010e03ff83e0

def z212 : W := mkw 0x008a004900000000 0x0008a00490000000 0x801b0019c0000002 0x0801b0019c000000

def z213 : W := mkw 0x0414000000000000 0x0041400000000000 0x0e1c000000000002 0xe0e1c00000000000

def z214 : W := mkw 0x4ddfa00025b54000 0x04ddfa00025b5400 0x1fffe00007f80003 0xe1fffe00007f8000

def z215 : W := mkw 0x0000002000c10840 0x80000002000c1084 0x4000000001c318c0 0x04000000001c318c

def z216 : W := mkw 0x4dffe702f7bfe316 0x44dffe702f7bfe31 0xffffef07ffffe73f 0xeffffef07ffffe73

def z217 : W := mkw 0x82205fdfc2082316 0x482205fdfc208231 0x80001fffc0002734 0x180001fffc000273

def z218 : W := mkw 0x5fffbfa03ffffe0e 0x05fffbfa03ffffe0 0x7fffffe03ffffe0f 0xf7fffffe03ffffe0

def z219 : W := mkw 0x0000200000104000 0x0000020000010400 0x2064e0000038c000 0x82064e0000038c00

def z220 : W := mkw 0x0940000021200000 0x0094000002120000 0x4f80000039c00000 0x44f80000039c0000

def z221 : W := mkw 0x269f197d5ec7bded 0x8269f197d5ec7bde 0xff9f1fffffc7ffff 0xfff9f1fffffc7fff

def z222 : W := mkw 0x0020460280000000 0x0002046028000000 0x80000f07c0000004 0x080000f07c000000

def z223 : W := mkw 0x00ab6702c69d6316 0x400ab6702c69d631 0xf1ffef07c7ffe73f 0xef1ffef07c7ffe73

def z224 : W := mkw 0x12205fa2ca483f1e 0x412205fa2ca483f1 0x80001fe7c0003f34 0x180001fe7c0003f3

def z225 : W := mkw 0x8fdf99fd46c52944 0x88fdf99fd46c5294 0xdf9b13f9c7c739cf 0x7df9b13f9c7c739c

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0x6e00000038000008 0xe6e0000003800000

def z227 : W := mkw 0x0414000010028000 0x0041400001002800 0x001c00000007c002 0x0001c00000007c00

def z228 : W := mkw 0x84bfe75fc61c6316 0x484bfe75fc61c631 0xb07fef1fc63ce73f 0xab07fef1fc63ce73

def z229 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000004e738 0x0200000000004e73

def z230 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x519810f807c739c8 0x5519810f807c739c

def z231 : W := mkw 0x008b216946dd6b56 0xc008b216946dd6b5 0xf19b13f9c7ffffff 0x7f19b13f9c7fffff

def z232 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x81fbf3f9c0000007 0x781fbf3f9c000000

def z233 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x919b03f9c7c701c3 0x0919b03f9c7c701c

def z234 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000c000000260c 0xa20000c000000260

def z235 : W := mkw 0x0001200004144000 0x0000120000414400 0x30000000063cc008 0x030000000063cc00

def z236 : W := mkw 0x49cba00025b54000 0x049cba00025b5400 0x51fbe00007ff000b 0x651fbe00007ff000

def z237 : W := mkw 0x9fde98fd29601c08 0x09fde98fd29601c0 0x4f9810f839c01800 0x54f9810f839c0180

def z238 : W := mkw 0x4d55a00035b7c000 0x04d55a00035b7c00 0x7e64e0003fffc008 0x87e64e0003fffc00

def z239 : W := mkw 0x9f74dfb6ab683e0e 0x09f74dfb6ab683e0 0x7fe4ffe63ff83e0d 0xf7fe4ffe63ff83e0

def z240 : W := mkw 0x1b601ea029601c08 0x01b601ea029601c0 0x4fe01fe039c01805 0xf4fe01fe039c0180

def z241 : W := mkw 0x8ffede9680000000 0x08ffede968000000 0x0fffec0600000003 0xe0fffec060000000

def z242 : W := mkw 0x6f54b8143932d4a9 0x06f54b8143932d4a 0xee7cfc1e383ffffe 0xfee7cfc1e383ffff

def z243 : W := mkw 0x0000004940000140 0x8000000494000014 0x80000019c00001c0 0x080000019c00001c

def z244 : W := mkw 0x120019202b683e0e 0x0120019202b683e0 0x7e001c003ff83e0c 0xf7e001c003ff83e0

def z245 : W := mkw 0x1960068021280202 0x0196006802128020 0x0060000000380000 0x0006000000038000

def z246 : W := mkw 0x00216722c6dd6b56 0xc00216722c6dd6b5 0xf067ef07c7ffffff 0xaf067ef07c7fffff

def z247 : W := mkw 0x449fa0001497c000 0x0449fa0001497c00 0x6e1fe0003807c00a 0xe6e1fe0003807c00

def z248 : W := mkw 0xa2205edf880014a9 0x0a2205edf880014a 0x80001fffc0003ff4 0x180001fffc0003ff

def z249 : W := mkw 0x0960070023282206 0x0096007002328220 0x7fe00f003ff8260d 0xe7fe00f003ff8260

def z250 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x8007ef07c004e736 0x08007ef07c004e73

def z251 : W := mkw 0x92205fff8a483e0e 0x092205fff8a483e0 0x80001fffc0003e04 0x180001fffc0003e0

def z252 : W := mkw 0x40216702f7bfe316 0x440216702f7bfe31 0xf067ef07ffffe73f 0xaf067ef07ffffe73

def z253 : W := mkw 0x8fde98dd00000000 0x08fde98dd0000000 0x0ffff0f800000003 0xf0ffff0f80000000

def z254 : W := mkw 0x12201fe94a483f4e 0x812201fe94a483f4 0x80001ff9c0003fc4 0x180001ff9c0003fc

def z255 : W := mkw 0x86bededf80000000 0x086bededf8000000 0x801fffffc0000006 0x1801fffffc000000

def z256 : W := mkw 0x100121206f7c7f1e 0x4100121206f7c7f1 0x700000003ffcff38 0x0700000003ffcff3

def z257 : W := mkw 0x4dde800031a38000 0x04dde800031a3800 0x4fffe00039c30003 0xe4fffe00039c3000

def z258 : W := mkw 0x9ffe9ffd2b683e0e 0x09ffe9ffd2b683e0 0x7ff81ff83ff83e0d 0xf7ff81ff83ff83e0

def z259 : W := mkw 0x102007202b683e0e 0x0102007202b683e0 0x70600f003ff83e0d 0xa70600f003ff83e0

def z260 : W := mkw 0x20000000180294a9 0x020000000180294a 0xe0040c063807fffe 0xae0040c063807fff

def z261 : W := mkw 0x1beb1fe96fed3f4e 0x81beb1fe96fed3f4 0x7fe31fe1fff83e0d 0xf7fe31fe1fff83e0

def z262 : W := mkw 0x4dde806931e38840 0x84dde806931e3884 0x4f9810f839c318c0 0x54f9810f839c318c

def z263 : W := mkw 0x22001800180294a9 0x022001800180294a 0x6e001c003807fffc 0xf6e001c003807fff

def z264 : W := mkw 0x26141814080014a9 0x026141814080014a 0x8e1c1c1e00003ff6 0xf8e1c1c1e00003ff

def z265 : W := mkw 0x6fdfb8143db7d4a9 0x06fdfb8143db7d4a 0x7ffff0183fffd8cb 0xf7ffff0183fffd8c

def z266 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x11ffe00007ffc003 0x011ffe00007ffc00

def z267 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x81e7efe7c0000007 0xa81e7efe7c000000

def z268 : W := mkw 0x4000000031a38000 0x04000000031a3800 0x4000000039c30000 0x04000000039c3000

def z269 : W := mkw 0x8fffdedfc4850140 0x88fffdedfc485014 0x8fffffffc00701c7 0xf8fffffffc00701c

def z270 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xafffffffc004e73f 0xfafffffffc004e73

def z271 : W := mkw 0x6ddfa0003db7d4a9 0x06ddfa0003db7d4a 0x7fffe0003ffffffb 0xe7fffe0003ffffff

def z272 : W := mkw 0x008b616bc6d56954 0xc008b616bc6d5695 0xd19ff3ffc7c7f9ff 0x7d19ff3ffc7c7f9f

def z273 : W := mkw 0x3f741e94392a96ab 0x03f741e94392a96a 0xee7c1c1e383ffffe 0xfee7c1c1e383ffff

def z274 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x4f801fe039c03e04 0x54f801fe039c03e0

def z275 : W := mkw 0x5fffbe803dbfd60a 0x05fffbe803dbfd60 0x7fffec003fffc60b 0xe7fffec003fffc60

def z276 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x3fe00fe03ff80601 0x83fe00fe03ff8060

def z277 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x518313e1c7c0380d 0x7518313e1c7c0380

def z278 : W := mkw 0x3b601fb42b683eaf 0x03b601fb42b683ea 0xffe01ffe3ff83ffd 0xfffe01ffe3ff83ff

def z279 : W := mkw 0x00ab676bc6dd6b56 0xc00ab676bc6dd6b5 0x11e3e3e1c7f80001 0x011e3e3e1c7f8000

def z280 : W := mkw 0x09ca800000000000 0x009ca80000000000 0x01e3e00000000001 0x001e3e0000000000

def z281 : W := mkw 0x4414a0001012c000 0x04414a0001012c00 0x0004e0000000c000 0x00004e0000000c00

def z282 : W := mkw 0x4001210077bfe316 0x44001210077bfe31 0x700000003fffe738 0x0700000003fffe73

def z283 : W := mkw 0x0940012023602804 0x0094001202360280 0x7fe013e03ff8380d 0xf7fe013e03ff8380

def z284 : W := mkw 0x2614197d5a42bded 0x82614197d5a42bde 0xee1c1ffff807fffe 0xfee1c1ffff807fff

def z285 : W := mkw 0x008b000004850000 0x0008b00000485000 0x519b000007c7000b 0x6519b000007c7000

def z286 : W := mkw 0x4ddfa04935b7c000 0x04ddfa04935b7c00 0xfffff3f9ffffc00f 0xffffff3f9ffffc00

def z287 : W := mkw 0x00212700061c6206 0x000212700061c620 0x3067ef00063ce60f 0xa3067ef00063ce60

def z288 : W := mkw 0x26347e16981ad6bb 0x426347e16981ad6b 0x2e64ec063838c630 0x82e64ec063838c63

def z289 : W := mkw 0x849ec05f80000000 0x0849ec05f8000000 0x819ff3ffc0000007 0x7819ff3ffc000000

def z290 : W := mkw 0x0000000000000000 0x0000000000000000 0x401800000007000a 0x6401800000007000

def z291 : W := mkw 0x102007a002482a06 0x0102007a002482a0 0x000003e000000000 0x0000003e00000000

def z292 : W := mkw 0x261519145e06b5ad 0x0261519145e06b5a 0xfe1f1f1ffe07ffff 0xffe1f1f1ffe07fff

def z293 : W := mkw 0x8fffffdfc61c6316 0x48fffffdfc61c631 0xbfffffffc63ce73f 0xfbfffffffc63ce73

def z294 : W := mkw 0x19eb07e967ed2b46 0x819eb07e967ed2b4 0x11e303e1c7f80001 0x011e303e1c7f8000

def z295 : W := mkw 0x82aa5edf80000000 0x082aa5edf8000000 0x819b1fffc0000007 0x7819b1fffc000000

def z296 : W := mkw 0x0b601e8008001408 0x00b601e800800140 0x6fe01fe038003e0d 0xf6fe01fe038003e0

def z297 : W := mkw 0x00012100461c6316 0x400012100461c631 0x3067e000063ce73b 0xa3067e000063ce73

def z298 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x4f9fe00039c7c002 0x44f9fe00039c7c00

def z299 : W := mkw 0x00214702c60c2316 0x400214702c60c231 0x90030f07c604273f 0x290030f07c604273

def z300 : W := mkw 0x26141814180294a9 0x026141814180294a 0xae1c1c1e3800c636 0xfae1c1c1e3800c63

def z301 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x3067e301c63cc00b 0xa3067e301c63cc00

def z302 : W := mkw 0x196007a02b683e0e 0x0196007a02b683e0 0x71e003e03ff83e09 0x071e003e03ff83e0

def z303 : W := mkw 0x26141814180294a9 0x026141814180294a 0xae040c063804e73e 0xaae040c063804e73

def z304 : W := mkw 0x00216722c65c6b16 0x400216722c65c6b1 0xf1e7ffe7c7fcff3f 0xff1e7ffe7c7fcff3

def z305 : W := mkw 0x00216602c41c4312 0x400216602c41c431 0xa067ec07c03cc732 0x8a067ec07c03cc73

def z306 : W := mkw 0xcffffe96b5b7c000 0x0cffffe96b5b7c00 0x7fffec063fffc00b 0xe7fffec063fffc00

def z307 : W := mkw 0x0414001400000000 0x0041400140000000 0x801c001e00000002 0x0801c001e0000000

def z308 : W := mkw 0x4dffe76bf7ffeb56 0xc4dffe76bf7ffeb5 0xffffffffffffffff 0xffffffffffffffff

def z309 : W := mkw 0x26141814180294a9 0x026141814180294a 0xce1c101e3807d9f2 0x5ce1c101e3807d9f

def z310 : W := mkw 0x9fffdfffefed3f4e 0x89fffdfffefed3f4 0xffffffffffff3fcf 0xfffffffffffff3fc

def z311 : W := mkw 0x1b601e802928160a 0x01b601e802928160 0x7fe00c003ff80609 0xe7fe00c003ff8060

def z312 : W := mkw 0x1f741fa03b6abe0e 0x01f741fa03b6abe0 0x7ffc1fe03ffffe0f 0xf7ffc1fe03ffffe0

def z313 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x919b13f9c7c00007 0x7919b13f9c7c0000

def z314 : W := mkw 0x0020070002082206 0x0002007000208220 0x00000f0000002604 0x000000f000000260

def z315 : W := mkw 0x00216602841c4212 0x400216602841c421 0x3067ec06063cc63b 0xa3067ec06063cc63

def z316 : W := mkw 0x0020072002482a06 0x00020072002482a0 0x71e01fe007f83e0d 0xf71e01fe007f83e0

def z317 : W := mkw 0x0000012002402804 0x0000001200240280 0x518013e007c0380d 0x7518013e007c0380

def z318 : W := mkw 0x449fa0495497c140 0x8449fa0495497c14 0x801fe019c007c1c2 0x0801fe019c007c1c

def z319 : W := mkw 0x26141814100280a1 0x026141814100280a 0x8e1c1c1e0007c1f6 0xf8e1c1c1e0007c1f

def z320 : W := mkw 0x26141814180294a9 0x026141814180294a 0x6e1c1c1e3803def0 0xd6e1c1c1e3803def

def z321 : W := mkw 0x00216602c4144110 0x400216602c414411 0x8067ef07c004c137 0xa8067ef07c004c13

def z322 : W := mkw 0x20216702de1ef7bf 0x420216702de1ef7b 0xf067ef07fe3fffff 0xaf067ef07fe3ffff

def z323 : W := mkw 0x26141814180294a9 0x026141814180294a 0x0e00000038000000 0x00e0000003800000

def z324 : W := mkw 0x0b605e8280000000 0x00b605e828000000 0x8fe7ffe7c0000007 0xf8fe7ffe7c000000

def z325 : W := mkw 0x00204702c2082316 0x400204702c208231 0x00000301c0000000 0x000000301c000000

def z326 : W := mkw 0x008a004900000000 0x0008a00490000000 0x018303e1c0000001 0x0018303e1c000000

def z327 : W := mkw 0x59eba7a027fd6a06 0x059eba7a027fd6a0 0x11e3e3e007f80001 0x011e3e3e007f8000

def z328 : W := mkw 0x0dde800010028000 0x00dde80001002800 0x6fffe0003807c00b 0xe6fffe0003807c00

def z329 : W := mkw 0x8fffffdfc61c6316 0x48fffffdfc61c631 0x9fffffffc6380007 0xf9fffffffc638000

def z330 : W := mkw 0x008b000004850000 0x0008b00000485000 0x001b000000070002 0x0001b00000007000

def z331 : W := mkw 0x00204702c2082316 0x400204702c208231 0xa0040f07c004e73e 0xaa0040f07c004e73

def z332 : W := mkw 0x269f197d5ec7bded 0x8269f197d5ec7bde 0xdf9b13f9ffc739cf 0x7df9b13f9ffc739c

def z333 : W := mkw 0x4ddfe002f5b7c110 0x44ddfe002f5b7c11 0xffffe007ffffc13b 0xeffffe007ffffc13

def z334 : W := mkw 0x8f74de9680000000 0x08f74de968000000 0x0fe4ffe600000005 0xf0fe4ffe60000000

def z335 : W := mkw 0x5f74be80393ad60a 0x05f74be80393ad60 0x2e64ec003838c600 0x82e64ec003838c60

def z336 : W := mkw 0x100101206fed3f4e 0x8100101206fed3f4 0x700000003fff3fc8 0x0700000003fff3fc

def z337 : W := mkw 0x8f54989400000000 0x08f5498940000000 0x0e00000000000000 0x00e0000000000000

def z338 : W := mkw 0x069e185d00000000 0x0069e185d0000000 0x8f9f1fffc0000007 0xf8f9f1fffc000000

def z339 : W := mkw 0x0941200025344000 0x0094120002534400 0x7fe7e0003ffcc00b 0xe7fe7e0003ffcc00

def z340 : W := mkw 0x00210700460c2306 0x000210700460c230 0xb0630f01c63c270f 0xab0630f01c63c270

def z341 : W := mkw 0x6ddfa01435b7c0a1 0x06ddfa01435b7c0a 0xffffe01e3fffc1fb 0xeffffe01e3fffc1f

def z342 : W := mkw 0x84bec65f80000000 0x084bec65f8000000 0x807fef1fc0000007 0xa807fef1fc000000

def z343 : W := mkw 0x0414000010028000 0x0041400001002800 0xee1c0c063807e73e 0xeee1c0c063807e73

def z344 : W := mkw 0x0940000021200000 0x0094000002120000 0x11e0000007f80001 0x011e0000007f8000

def z345 : W := mkw 0xafde98dd180294a9 0x0afde98dd180294a 0x4f9810f8380318c0 0x54f9810f8380318c

def z346 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xaffffffff800c637 0xfaffffffff800c63

def z347 : W := mkw 0x9f74de96a928160a 0x09f74de96a928160 0x2e64ec0638380600 0x82e64ec063838060

def z348 : W := mkw 0x4ddfa10077bfe316 0x44ddfa10077bfe31 0x7fffe0003fffe73b 0xe7fffe0003fffe73

def z349 : W := mkw 0x500121203ffffe0e 0x0500121203ffffe0 0x700000003ffffe08 0x0700000003ffffe0

def z350 : W := mkw 0x0001200044144110 0x4000120004414411 0x000000000004c130 0x0000000000004c13

def z351 : W := mkw 0x26141814180294a9 0x026141814180294a 0x801c1c1e0007fff6 0x1801c1c1e0007fff

def z352 : W := mkw 0x0940000021200000 0x0094000002120000 0x2e60000038380000 0x82e6000003838000

def z353 : W := mkw 0x0000004900000000 0x0000000490000000 0x800013f9c0000004 0x1800013f9c000000

def z354 : W := mkw 0x09616702e73c6316 0x409616702e73c631 0xffe7ef07fffce73f 0xeffe7ef07fffce73

def z355 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8f981fffc0000004 0x58f981fffc000000

def z356 : W := mkw 0x0001016946442944 0x8000101694644294 0x900313f9c60439cf 0x3900313f9c60439c

def z357 : W := mkw 0x0beb1fe946c52944 0x80beb1fe946c5294 0xdffb1ff9c7c739cf 0xfdffb1ff9c7c739c

def z358 : W := mkw 0x008b004944850140 0x8008b00494485014 0x819b13f9c00701c7 0x7819b13f9c00701c

def z359 : W := mkw 0x00aa464b80000000 0x000aa464b8000000 0x81ffffffc0000007 0xf81ffffffc000000

def z360 : W := mkw 0x0200180008001408 0x0020018000800140 0xee041c063804ff3e 0xfee041c063804ff3

def z361 : W := mkw 0x00ab676bc6dd6b56 0xc00ab676bc6dd6b5 0xd1fbf3f9c7ff39cf 0x7d1fbf3f9c7ff39c

def z362 : W := mkw 0x10216722ef7c7f1e 0x410216722ef7c7f1 0xf067ef07fffcff3f 0xaf067ef07fffcff3

def z363 : W := mkw 0x0020060000080202 0x0002006000008020 0x20600c0000380600 0x820600c000038060

def z364 : W := mkw 0x20000000100280a1 0x020000000100280a 0x000000000007c1f0 0x0000000000007c1f

def z365 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x9063ef07c6382735 0x09063ef07c638273

def z366 : W := mkw 0xaf74de96980294a9 0x0af74de96980294a 0x2e64ec063800c630 0x82e64ec063800c63

def z367 : W := mkw 0x00016002c4144110 0x400016002c414411 0x0003e001c0000000 0x00003e001c000000

def z368 : W := mkw 0x49cba00025b54000 0x049cba00025b5400 0x31e7e00007fcc00b 0xa31e7e00007fcc00

def z369 : W := mkw 0xc9ebe6cba5b54000 0x0c9ebe6cba5b5400 0x11e3e3e1c7f80001 0x011e3e3e1c7f8000

def z370 : W := mkw 0x0020060000000000 0x0002006000000000 0x00600f0000000005 0xa00600f000000000

def z371 : W := mkw 0x8ffffedf84144000 0x08ffffedf8414400 0xbfffffffc63cc00f 0xfbfffffffc63cc00

def z372 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xcfffffffc00739cf 0xfcfffffffc00739c

def z373 : W := mkw 0x00016002c4144110 0x400016002c414411 0xa007ec07c004e73e 0xaa007ec07c004e73

def z374 : W := mkw 0xafffffdfde1ef7bf 0x4afffffdfde1ef7b 0xfffffffffe3fffff 0xffffffffffe3ffff

def z375 : W := mkw 0x19eb07e967ed2b46 0x819eb07e967ed2b4 0xd1fb13f9c7ff39cf 0x7d1fb13f9c7ff39c

def z376 : W := mkw 0x849e805d00000000 0x0849e805d0000000 0x0018001800000000 0x0001800180000000

def z377 : W := mkw 0x00206702c2186316 0x400206702c218631 0xa064ef07c038e734 0x8a064ef07c038e73

def z378 : W := mkw 0x02201e8000000000 0x002201e800000000 0x00001fe000000004 0x100001fe00000000

def z379 : W := mkw 0x400120001497c000 0x0400120001497c00 0x000000000007c000 0x0000000000007c00

def z380 : W := mkw 0x82217fdfc61c6316 0x482217fdfc61c631 0xb067ffffc63ce73f 0xbb067ffffc63ce73

def z381 : W := mkw 0x0614181400000000 0x0061418140000000 0xae1c1c1e0004e73e 0xfae1c1c1e0004e73

def z382 : W := mkw 0x0020670282186216 0x4002067028218621 0x3064ef060638e63d 0xa3064ef060638e63

def z383 : W := mkw 0x008a000000810000 0x0008a00000081000 0x4198000001c30000 0x44198000001c3000

def z384 : W := mkw 0x0020460280000000 0x0002046028000000 0x0063e301c0000001 0x00063e301c000000

def z385 : W := mkw 0x849fc05fc4850140 0x8849fc05fc485014 0x801fe01fc00701c2 0x0801fe01fc00701c

def z386 : W := mkw 0x89ebc7ebc6c52944 0x889ebc7ebc6c5294 0x11e3e3e1c7c00001 0x011e3e3e1c7c0000

def z387 : W := mkw 0x0000016942402944 0x8000001694240294 0xd18013f9c7c039cd 0x7d18013f9c7c039c

def z388 : W := mkw 0x4ddea00031b3c000 0x04ddea00031b3c00 0x6ffce00039fbc000 0xc6ffce00039fbc00

def z389 : W := mkw 0xcfdfb8dd35b7c000 0x0cfdfb8dd35b7c00 0x7ffff0f83fffc00b 0xf7ffff0f83fffc00

def z390 : W := mkw 0x400020003132c000 0x0400020003132c00 0x200000003838c000 0x0200000003838c00

def z391 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x11e01fe007f83e05 0x111e01fe007f83e0

def z392 : W := mkw 0x0020460280000000 0x0002046028000000 0xa067ef07c004e73f 0xaa067ef07c004e73

def z393 : W := mkw 0x3f757fb6ff7effbf 0x43f757fb6ff7effb 0xffffffffffffffff 0xffffffffffffffff

def z394 : W := mkw 0x5fffffa2ffffff1e 0x45fffffa2ffffff1 0xffffffe7ffffff3f 0xfffffffe7ffffff3

def z395 : W := mkw 0x00012100461c6316 0x400012100461c631 0x1000000006380000 0x0100000000638000

def z396 : W := mkw 0x0021676bc65c6b56 0xc0021676bc65c6b5 0xb067ffffc63cffff 0xbb067ffffc63cfff

def z397 : W := mkw 0x0dde800021200000 0x00dde80002120000 0x7fffe0003ff8000b 0xe7fffe0003ff8000

def z398 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xb0000f07c63ce73c 0x0b0000f07c63ce73

def z399 : W := mkw 0x449fa0001497c000 0x0449fa0001497c00 0x307fe000063fc00b 0xa307fe000063fc00

def z400 : W := mkw 0x1b4019a02b603c0c 0x01b4019a02b603c0 0x5f8013e03fc0380d 0x75f8013e03fc0380

def z401 : W := mkw 0x0b601f8002082206 0x00b601f800208220 0x3fe01fe00638260d 0xf3fe01fe00638260

def z402 : W := mkw 0x100001202b683e0e 0x0100001202b683e0 0x718013e03ff83e0d 0x7718013e03ff83e0

def z403 : W := mkw 0x008a006900c10840 0x8008a006900c1084 0x018000e001c00000 0x0018000e001c0000

def z404 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x2e601fe038383e04 0x92e601fe038383e0

def z405 : W := mkw 0x00214702c6042104 0x000214702c604210 0x9067ef07c604210f 0xa9067ef07c604210

def z406 : W := mkw 0x3f5418b439629ca9 0x03f5418b439629ca 0x4f9810f839c318c0 0x54f9810f839c318c

def z407 : W := mkw 0x8000405f80000000 0x08000405f8000000 0x8000001fc0000000 0x08000001fc000000

def z408 : W := mkw 0xcddfe05fb5b7c000 0x0cddfe05fb5b7c00 0xffffe01fffffc00b 0xeffffe01fffffc00

def z409 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x0ffbf3f9c0000001 0x50ffbf3f9c000000

def z410 : W := mkw 0x12201fa00a483e0e 0x012201fa00a483e0 0x30601fe006383e0d 0xb30601fe006383e0

def z411 : W := mkw 0x4d54a0003132c000 0x04d54a0003132c00 0x7fe4e0003ff8c009 0xe7fe4e0003ff8c00

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0x80001018000039c4 0x180001018000039c

def z413 : W := mkw 0x5fffbfe97fffff4e 0x85fffbfe97fffff4 0xfffffff9ffffffcf 0xffffffff9ffffffc

def z414 : W := mkw 0x1b611fa06f6c3f0e 0x01b611fa06f6c3f0 0xffe31fe1fffc3f0f 0xfffe31fe1fffc3f0

def z415 : W := mkw 0x3f5418b439629ca9 0x03f5418b439629ca 0xef9c1cfe39c7fffe 0xfef9c1cfe39c7fff

def z416 : W := mkw 0x0001000004850000 0x0000100000485000 0x5000000007c70008 0x05000000007c7000

def z417 : W := mkw 0x408ba00004954000 0x0408ba0000495400 0x0003e00000000000 0x00003e0000000000

def z418 : W := mkw 0x0614180018029408 0x0061418001802940 0x6e1c1c003807fe0e 0xf6e1c1c003807fe0

def z419 : W := mkw 0x1000002029601c08 0x01000002029601c0 0x4000000039c01800 0x04000000039c0180

def z420 : W := mkw 0x0b601e8000000000 0x00b601e800000000 0x0e600c0000000000 0x80e600c000000000

def z421 : W := mkw 0x261538141c16d4a9 0x0261538141c16d4a 0xfe7ffc1e3e3fffff 0xffe7ffc1e3e3ffff

def z422 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x801b13f9c00739c6 0x1801b13f9c00739c

def z423 : W := mkw 0xeffffedfbdb7d4a9 0x0effffedfbdb7d4a 0xffffffffffffffff 0xffffffffffffffff

def z424 : W := mkw 0x00204702c2082316 0x400204702c208231 0xb0600f07c638273d 0xab0600f07c638273

def z425 : W := mkw 0x0020460280000000 0x0002046028000000 0x0064ec0600000000 0x80064ec060000000

def z426 : W := mkw 0x32201fb40a483eaf 0x032201fb40a483ea 0x80001ffe00003ff4 0x180001ffe00003ff

def z427 : W := mkw 0x8ffededfa1200000 0x08ffededfa120000 0xfffffffffff8000f 0xffffffffffff8000

def z428 : W := mkw 0x0001010046042104 0x0000101004604210 0x1000000006042108 0x0100000000604210

def z429 : W := mkw 0x1b601e802928160a 0x01b601e802928160 0x6e601c0038383e0c 0xf6e601c0038383e0

def z430 : W := mkw 0x194001202b683e0e 0x0194001202b683e0 0x7fe000003ff83e09 0xe7fe000003ff83e0

def z431 : W := mkw 0x00ab674bc61c6316 0x400ab674bc61c631 0xb1ffffffc63ce73f 0xfb1ffffffc63ce73

def z432 : W := mkw 0x008a016942402944 0x8008a01694240294 0x819b13f9c00039c7 0x7819b13f9c00039c

def z433 : W := mkw 0x4ddfa12037f7e804 0x04ddfa12037f7e80 0x7ffff3e03ffff80f 0xf7ffff3e03ffff80

def z434 : W := mkw 0x0414000010028000 0x0041400001002800 0x2e0400003800c000 0x82e0400003800c00

def z435 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x519b03e1c7c7000b 0x6519b03e1c7c7000

def z436 : W := mkw 0x49cba16967f56944 0x849cba16967f5694 0xd1fbf3f9c7ff39cf 0x7d1fbf3f9c7ff39c

def z437 : W := mkw 0x00ab674bc69d6356 0xc00ab674bc69d635 0xb07fef1fc63fe7ff 0xab07fef1fc63fe7f

def z438 : W := mkw 0x0000000000000000 0x0000000000000000 0x80030301c0000007 0x280030301c000000

def z439 : W := mkw 0x36341fb41a4abeaf 0x036341fb41a4abea 0xee1c1ffe3807fffe 0xfee1c1ffe3807fff

def z440 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xf19f1fffc7c7ffff 0xff19f1fffc7c7fff

def z441 : W := mkw 0x0000000021200000 0x0000000002120000 0x700000003ff80008 0x0700000003ff8000

def z442 : W := mkw 0x196007a023682a06 0x0196007a023682a0 0x7fe003e03ff80009 0xe7fe003e03ff8000

def z443 : W := mkw 0x20000000180294a9 0x020000000180294a 0x40000000380318c0 0x040000000380318c

def z444 : W := mkw 0x8fffdfffc6c52944 0x88fffdfffc6c5294 0x9fffffffc7c00007 0xf9fffffffc7c0000

def z445 : W := mkw 0x26141814180294a9 0x026141814180294a 0xae041c1e3800fff4 0x9ae041c1e3800fff

def z446 : W := mkw 0x26345f16da0ab7bf 0x426345f16da0ab7b 0xee1c1f1ff807fffe 0xfee1c1f1ff807fff

def z447 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8e7fec1fc0000002 0x88e7fec1fc000000

def z448 : W := mkw 0x449fa0001497c000 0x0449fa0001497c00 0x519fe00007c7c00b 0x6519fe00007c7c00

def z449 : W := mkw 0x12201fa00a483e0e 0x012201fa00a483e0 0x51801fe007c03e0d 0x751801fe007c03e0

def z450 : W := mkw 0x008b004904850000 0x0008b00490485000 0xd19b13f9c7c7000f 0x7d19b13f9c7c7000

def z451 : W := mkw 0x4001200035b7c000 0x04001200035b7c00 0x7067e0003fffc00b 0xa7067e0003fffc00

def z452 : W := mkw 0x008b004944850140 0x8008b00494485014 0x00030001c0000000 0x000030001c000000

def z453 : W := mkw 0x361419343b6abeaf 0x0361419343b6abea 0xfe1c1c1e3ffffffe 0xffe1c1c1e3ffffff

def z454 : W := mkw 0x0ddf816946c52944 0x80ddf816946c5294 0xdffff3f9c7c739cf 0xfdffff3f9c7c739c

def z455 : W := mkw 0x26345e16980294a9 0x026345e16980294a 0xee7fff1ff807ffff 0xfee7fff1ff807fff

def z456 : W := mkw 0x09cb016967e52944 0x809cb016967e5294 0xfffb13f9ffff39cf 0xffffb13f9ffff39c

def z457 : W := mkw 0x1b601fe96b683f4e 0x81b601fe96b683f4 0xffe01ff9fff83fcd 0xfffe01ff9fff83fc

def z458 : W := mkw 0x12201fa00a483e0e 0x012201fa00a483e0 0x6e001fe038003e0c 0xf6e001fe038003e0

def z459 : W := mkw 0x4001200025b54000 0x04001200025b5400 0x1000000007f80000 0x01000000007f8000

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x800400060004c132 0x0800400060004c13

def z461 : W := mkw 0x26141814180294a9 0x026141814180294a 0xae1c0c1e3807c7f2 0x8ae1c0c1e3807c7f

def z462 : W := mkw 0x0614181408001408 0x0061418140800140 0xee1c1c1e38003e0e 0xfee1c1c1e38003e0

def z463 : W := mkw 0x008a016942c12944 0x8008a016942c1294 0xc19813f9c1c339c4 0x5c19813f9c1c339c

def z464 : W := mkw 0x82205edf80000000 0x082205edf8000000 0x8067ffffc0000007 0xb8067ffffc000000

def z465 : W := mkw 0x0001000044850140 0x8000100004485014 0x00000000000701c0 0x000000000000701c

def z466 : W := mkw 0xcffefedfb132c000 0x0cffefedfb132c00 0xaffffffff838c007 0xfaffffffff838c00

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x80040c0600000006 0xa80040c060000000

def z468 : W := mkw 0x0001010046042104 0x0000101004604210 0xd01b1319c60739cf 0x7d01b1319c60739c

def z469 : W := mkw 0x041520001416c000 0x0041520001416c00 0x7e7fe0003e3fc00b 0xe7e7fe0003e3fc00

def z470 : W := mkw 0x0b617f82c61c6316 0x40b617f82c61c631 0xbfe7ffe7c63ce73f 0xfbfe7ffe7c63ce73

def z471 : W := mkw 0x008b010046852104 0x0008b01004685210 0xd19b0301c7c7210f 0x6d19b0301c7c7210

def z472 : W := mkw 0x5b613fa03ffffe0e 0x05b613fa03ffffe0 0x7fe01fe03ffffe0d 0xf7fe01fe03ffffe0

def z473 : W := mkw 0x26141814180294a9 0x026141814180294a 0x6e1810183807fff8 0x56e1810183807fff

def z474 : W := mkw 0x269e187d18c39ce9 0x8269e187d18c39ce 0x4f9810f839c318c0 0x54f9810f839c318c

def z475 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x9063e301c63c210f 0x29063e301c63c210

def z476 : W := mkw 0x12217fa2ce5c7f1e 0x412217fa2ce5c7f1 0xb067ffe7c63cff3f 0xbb067ffe7c63cff3

def z477 : W := mkw 0x24140014180294a9 0x024140014180294a 0xe01c001e3807fffa 0x0e01c001e3807fff

def z478 : W := mkw 0x0000400280000000 0x0000040028000000 0x8007e007c0000002 0x08007e007c000000

def z479 : W := mkw 0x3f741e94392a96ab 0x03f741e94392a96a 0x2e640c063838c630 0x82e640c063838c63

def z480 : W := mkw 0x1000012023682a06 0x01000012023682a0 0x1000000007f80000 0x01000000007f8000

def z481 : W := mkw 0x269e187d18c39ce9 0x8269e187d18c39ce 0xef9c1cfe39c7fffe 0xfef9c1cfe39c7fff

def z482 : W := mkw 0x24140014100280a1 0x024140014100280a 0xc01c101e0007f9fe 0x7c01c101e0007f9f

def z483 : W := mkw 0x0200180000000000 0x0020018000000000 0x0e001c0000000004 0xf0e001c000000000

def z484 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fe0000000000001 0xe0fe000000000000

def z485 : W := mkw 0x0001010046042104 0x0000101004604210 0x10030301c6000001 0x010030301c600000

def z486 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x918303e1c7c4210f 0x2918303e1c7c4210

def z487 : W := mkw 0x0000000000000000 0x0000000000000000 0x40181018000318c0 0x540181018000318c

def z488 : W := mkw 0x0001010046042104 0x0000101004604210 0xb0070f07c604e73f 0xab0070f07c604e73

def z489 : W := mkw 0x269f18141c8794a9 0x0269f18141c8794a 0xff9f1c1e3fc7ffff 0xfff9f1c1e3fc7fff

def z490 : W := mkw 0x008a000000000000 0x0008a00000000000 0x019b000000000003 0x6019b00000000000

def z491 : W := mkw 0x0414000010028000 0x0041400001002800 0xee1c10183807f9ce 0xfee1c10183807f9c

def z492 : W := mkw 0x4941200035b7c000 0x04941200035b7c00 0x7fe000003fffc009 0xe7fe000003fffc00

def z493 : W := mkw 0x0b40180029201408 0x00b4018002920140 0x7fe01c003ff83e0d 0xf7fe01c003ff83e0

def z494 : W := mkw 0x0000000000000000 0x0000000000000000 0xe01c1c1e0007fffe 0xfe01c1c1e0007fff

def z495 : W := mkw 0x449fe002d497c110 0x4449fe002d497c11 0x801fe007c007c132 0x0801fe007c007c13

def z496 : W := mkw 0x5bebbfa02ffd7e0e 0x05bebbfa02ffd7e0 0x7fe3ffe03ff83e0d 0xf7fe3ffe03ff83e0

def z497 : W := mkw 0x0020660280184212 0x4002066028018421 0x0060e00000380000 0x00060e0000038000

def z498 : W := mkw 0x0dffe702c61c6316 0x40dffe702c61c631 0xbfffef07c63ce73f 0xebfffef07c63ce73

def z499 : W := mkw 0x820018dd00000000 0x0820018dd0000000 0x000010f800000000 0x1000010f80000000

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000000739c8 0x040000000000739c

def z501 : W := mkw 0x0020660280184212 0x4002066028018421 0xa064ec06003ce73e 0xaa064ec06003ce73

def z502 : W := mkw 0x0020476bc2482b56 0xc0020476bc2482b5 0x80001fffc0003ff4 0x180001fffc0003ff

def z503 : W := mkw 0x0d54800000000000 0x00d5480000000000 0x0e64e00000000000 0x80e64e0000000000

def z504 : W := mkw 0x8ffe9edd00000000 0x08ffe9edd0000000 0x0ff81ff800000005 0xf0ff81ff80000000

def z505 : W := mkw 0x00ab076946cd2b46 0x800ab076946cd2b4 0xf1fb1ff9c7ff3fcf 0xff1fb1ff9c7ff3fc

def z506 : W := mkw 0x00212700461c6316 0x400212700461c631 0x30600f00063ce73d 0xa30600f00063ce73

def z507 : W := mkw 0x5fde98a039e39c08 0x05fde98a039e39c0 0x4f9810e039c31800 0x54f9810e039c3180

def z508 : W := mkw 0x1b40188029201408 0x01b4018802920140 0x0e00000038000000 0x00e0000003800000

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x20040c060000c630 0x820040c060000c63

def z510 : W := mkw 0x8f74dedf80000000 0x08f74dedf8000000 0x8e64ffffc0000004 0x98e64ffffc000000

def z511 : W := mkw 0x600120003db7d4a9 0x0600120003db7d4a 0x700000003ffffff8 0x0700000003ffffff

def z512 : W := mkw 0x2fde9814180294a9 0x02fde9814180294a 0xeffffc1e3807ffff 0xfeffffc1e3807fff

def z513 : W := mkw 0x8ffedfdf82082206 0x08ffedfdf8208220 0xbfffffffc638260f 0xfbfffffffc638260

def z514 : W := mkw 0xafde98dd180294a9 0x0afde98dd180294a 0xef9c1cfe3807fffe 0xfef9c1cfe3807fff

def z515 : W := mkw 0x1b611fa06fed3f4e 0x81b611fa06fed3f4 0x7fe01fe03fff3fcd 0xf7fe01fe03fff3fc

def z516 : W := mkw 0x008a016902402804 0x0008a01690240280 0xd19b13f9c7c0380f 0x7d19b13f9c7c0380

def z517 : W := mkw 0x661538143db7d4a9 0x0661538143db7d4a 0xfe1c1c1e3ffffffe 0xffe1c1c1e3ffffff

def z518 : W := mkw 0x196167a2e77c6b16 0x4196167a2e77c6b1 0x11e3e3e1c7f80001 0x011e3e3e1c7f8000

def z519 : W := mkw 0x0b40188000000000 0x00b4018800000000 0x0f8010e000000000 0x50f8010e00000000

def z520 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x3063e301c63ce739 0x03063e301c63ce73

def z521 : W := mkw 0x4fdfb81435b7c000 0x04fdfb81435b7c00 0xfffffc1e3fffc00f 0xffffffc1e3fffc00

def z522 : W := mkw 0x008b200004954000 0x0008b20000495400 0x71ffe00007ffc00b 0xe71ffe00007ffc00

def z523 : W := mkw 0x008b004944850140 0x8008b00494485014 0xd19b0019c7c701cb 0x6d19b0019c7c701c

def z524 : W := mkw 0x120018a008401c08 0x0120018a008401c0 0x000010e000001800 0x1000010e00000180

def z525 : W := mkw 0x1b601e802928160a 0x01b601e802928160 0x2fe01fe038380605 0xf2fe01fe03838060

def z526 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x3063ef01c638260d 0xa3063ef01c638260

def z527 : W := mkw 0xcffffedf9497c000 0x0cffffedf9497c00 0x8fffffffc007c007 0xf8fffffffc007c00

def z528 : W := mkw 0x8b605edf80000000 0x08b605edf8000000 0x8fe01fffc0000005 0xf8fe01fffc000000

def z529 : W := mkw 0x4ddfa0001497c000 0x04ddfa0001497c00 0x0fffe0000007c003 0xe0fffe0000007c00

def z530 : W := mkw 0x008a016902c12844 0x8008a016902c1284 0x519813f807c338cd 0x7519813f807c338c

def z531 : W := mkw 0x020019200a403c0c 0x0020019200a403c0 0x7f801fe03fc03e0d 0xf7f801fe03fc03e0

def z532 : W := mkw 0x24356716d61ee3b7 0x424356716d61ee3b 0xb07fef1fc63fe7ff 0xab07fef1fc63fe7f

def z533 : W := mkw 0x8ffedfff82402804 0x08ffedfff8240280 0xdfffffffc7c0380f 0xfdfffffffc7c0380

def z534 : W := mkw 0x9ffededfa928160a 0x09ffededfa928160 0xaffffffff8380607 0xfaffffffff838060

def z535 : W := mkw 0x408b200035b7c000 0x0408b200035b7c00 0x719b00003fffc00b 0x6719b00003fffc00

def z536 : W := mkw 0x0960068000000000 0x0096006800000000 0x01e003e000000001 0x001e003e00000000

def z537 : W := mkw 0x049f016956c7a944 0x8049f016956c7a94 0xff9f13f9ffc7f9cf 0xfff9f13f9ffc7f9c

def z538 : W := mkw 0x1b601fa00a483e0e 0x01b601fa00a483e0 0x0fe01fe000003e05 0xf0fe01fe000003e0

def z539 : W := mkw 0x4ddea0003132c000 0x04ddea0003132c00 0x2fffe0003838c003 0xe2fffe0003838c00

def z540 : W := mkw 0x196007a023682a06 0x0196007a023682a0 0x31e00fe007f8260d 0xa31e00fe007f8260

def z541 : W := mkw 0x1b601f802b28360e 0x01b601f802b28360 0x3e600f003e38260d 0xa3e600f003e38260

def z542 : W := mkw 0x22001814080014a9 0x022001814080014a 0xc0181c1e00073ffe 0x7c0181c1e00073ff

def z543 : W := mkw 0x00ab676bc6dd6b56 0xc00ab676bc6dd6b5 0xb1e7efe7c7fce73f 0xab1e7efe7c7fce73

def z544 : W := mkw 0x4d75e702f73ee316 0x44d75e702f73ee31 0xbe67ef07fe3ce73f 0xabe67ef07fe3ce73

def z545 : W := mkw 0x4ddf800035a78000 0x04ddf800035a7800 0x5f9b00003fc7000b 0x65f9b00003fc7000

def z546 : W := mkw 0x0dde800000000000 0x00dde80000000000 0x0f98000000000000 0x40f9800000000000

def z547 : W := mkw 0x808ac04b80000000 0x0808ac04b8000000 0x0003e001c0000000 0x00003e001c000000

def z548 : W := mkw 0x4415200035b7c000 0x04415200035b7c00 0x7e1c00003fffc00a 0xe7e1c00003fffc00

def z549 : W := mkw 0x849fe05fc4144110 0x4849fe05fc414411 0x801fe01fc004c132 0x0801fe01fc004c13

def z550 : W := mkw 0x4d54800031228000 0x04d5480003122800 0x0e00000038000000 0x00e0000003800000

def z551 : W := mkw 0x22205f16ca0837bf 0x422205f16ca0837b 0x80001f1fc0003ff4 0x180001f1fc0003ff

def z552 : W := mkw 0x261539145e1ef7bf 0x4261539145e1ef7b 0xfe1c1c1e3e3ffffe 0xffe1c1c1e3e3ffff

def z553 : W := mkw 0x869ed85f80000000 0x0869ed85f8000000 0x8e1ffc1fc0000006 0xf8e1ffc1fc000000

def z554 : W := mkw 0x5ddfa1203ffffe0e 0x05ddfa1203ffffe0 0x7fffe0003ffffe0b 0xe7fffe0003ffffe0

def z555 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x918313f9c7c039c5 0x1918313f9c7c039c

def z556 : W := mkw 0x49cba00035b7c000 0x049cba00035b7c00 0x71e3e0003fffc009 0x071e3e0003fffc00

def z557 : W := mkw 0x26141814180294a9 0x026141814180294a 0xce1c1c1e380318c6 0xfce1c1c1e380318c

def z558 : W := mkw 0x0000000000000000 0x0000000000000000 0x400010000000380c 0x7400010000000380

def z559 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x3064ec06063ce738 0x83064ec06063ce73

def z560 : W := mkw 0x0200181400000000 0x0020018140000000 0x80001c1e00000004 0x180001c1e0000000

def z561 : W := mkw 0x008b604bc4954150 0xc008b604bc495415 0x801fe01fc007c1f2 0x0801fe01fc007c1f

def z562 : W := mkw 0x20000014000000a1 0x020000014000000a 0x8000001e000001f0 0x08000001e000001f

def z563 : W := mkw 0x82ab5fffc6c52944 0x882ab5fffc6c5294 0xd19b1fffc7c739cf 0x7d19b1fffc7c739c

def z564 : W := mkw 0x00ab476bc6cd2b56 0xc00ab476bc6cd2b5 0xd19b1fffc7c73fff 0x7d19b1fffc7c73ff

def z565 : W := mkw 0x1b601fa023682a06 0x01b601fa023682a0 0x1fe01fe007f80005 0xf1fe01fe007f8000

def z566 : W := mkw 0x12201e800808160a 0x012201e800808160 0x00000c0000000600 0x000000c000000060

def z567 : W := mkw 0x89ebc7ebc6c52944 0x889ebc7ebc6c5294 0xd1fbf3f9c7c739cf 0x7d1fbf3f9c7c739c

def z568 : W := mkw 0x4d54a0003132c000 0x04d54a0003132c00 0x6e7ce000383fc00a 0xe6e7ce000383fc00

def z569 : W := mkw 0x4ddfa06935f7c840 0x84ddfa06935f7c84 0x7ffff0f83fffd8cb 0xf7ffff0f83fffd8c

def z570 : W := mkw 0x00012100461c6316 0x400012100461c631 0xb0030301c63ce73f 0x2b0030301c63ce73

def z571 : W := mkw 0xa49ec05f900280a1 0x0a49ec05f900280a 0x801fe01fc007c1f2 0x0801fe01fc007c1f

def z572 : W := mkw 0x261519345ec7bded 0x8261519345ec7bde 0xfe1c1c1e3fc7fffe 0xffe1c1c1e3fc7fff

def z573 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xd01b0019c7c739ca 0x0d01b0019c7c739c

def z574 : W := mkw 0x0001012046c52944 0x80001012046c5294 0x518013e007c739cd 0x7518013e007c739c

def z575 : W := mkw 0x1b607fa2ab787e1e 0x41b607fa2ab787e1 0x7fe4ffe63ff8fe3d 0xf7fe4ffe63ff8fe3

def z576 : W := mkw 0x196007a023682a06 0x0196007a023682a0 0x51e013e007f8380d 0x751e013e007f8380

def z577 : W := mkw 0x20000000180294a9 0x020000000180294a 0xe01810183807fffe 0x7e01810183807fff

def z578 : W := mkw 0x8fde98dd00000000 0x08fde98dd0000000 0x8f9b13f9c0000007 0x78f9b13f9c000000

def z579 : W := mkw 0x008b006944c50940 0x8008b006944c5094 0xc19b10f9c1c719c2 0x5c19b10f9c1c719c

def z580 : W := mkw 0x0d54000031228000 0x00d5400003122800 0x7ffc00003fffc00b 0xe7ffc00003fffc00

def z581 : W := mkw 0x249f017d56c7a9e5 0x8249f017d56c7a9e 0xd19f13ffc7c7f9ff 0x7d19f13ffc7c7f9f

def z582 : W := mkw 0x8fffdfdfc6042104 0x08fffdfdfc604210 0x9fffffffc604210f 0xf9fffffffc604210

def z583 : W := mkw 0xcfffffdff7bfe316 0x4cfffffdff7bfe31 0xffffffffffffe73f 0xfffffffffffffe73

def z584 : W := mkw 0x0000002000400800 0x0000000200040080 0x418010e001c01800 0x5418010e001c0180

def z585 : W := mkw 0x0000200000184212 0x4000020000018421 0x200000000038c630 0x0200000000038c63

def z586 : W := mkw 0x269f185d5c8795e9 0x8269f185d5c8795e 0xee1f1c1ff807fffe 0xfee1f1c1ff807fff

def z587 : W := mkw 0x0000000008001408 0x0000000000800140 0x6000000038003e08 0x06000000038003e0

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x0067e00000000003 0xa0067e0000000000

def z589 : W := mkw 0x5dffa7a037ffea06 0x05dffa7a037ffea0 0x7fffe3e03fffc00b 0xe7fffe3e03fffc00

def z590 : W := mkw 0x9ffedfffa3682a06 0x09ffedfffa3682a0 0x9fffffffc7f80007 0xf9fffffffc7f8000

def z591 : W := mkw 0x008b012006c52804 0x0008b012006c5280 0x519b13e007c7380f 0x7519b13e007c7380

def z592 : W := mkw 0x24140014100280a1 0x024140014100280a 0xee1c001e3807c1fa 0xeee1c001e3807c1f

def z593 : W := mkw 0x1b617fa2ef7c7f1e 0x41b617fa2ef7c7f1 0x7fe3ffe1fff83e0d 0xf7fe3ffe1fff83e0

def z594 : W := mkw 0x26141814180294a9 0x026141814180294a 0x6e041c063800fe3c 0xf6e041c063800fe3

def z595 : W := mkw 0x8ffefedf80184212 0x48ffefedf8018421 0xafffffffc038c637 0xfafffffffc038c63

def z596 : W := mkw 0x24156016d416c1b1 0x424156016d416c1b 0x801fe01fc007c1f2 0x0801fe01fc007c1f

def z597 : W := mkw 0x6fffff16ffbff7bf 0x46fffff16ffbff7b 0xffffff1fffffffff 0xfffffff1ffffffff

def z598 : W := mkw 0x449fa00035b7c000 0x0449fa00035b7c00 0x701fe0003fffc00a 0x0701fe0003fffc00

def z599 : W := mkw 0x0001000044040100 0x0000100004404010 0x80030001c0040102 0x080030001c004010

def z600 : W := mkw 0x1beb7febeffd7f5e 0xc1beb7febeffd7f5 0xffffffffffffffff 0xffffffffffffffff

def z601 : W := mkw 0x8f74de9680000000 0x08f74de968000000 0x8e7cfc1e00000006 0xf8e7cfc1e0000000

def z602 : W := mkw 0x0000000010028000 0x0000000001002800 0x600000003807c008 0x0600000003807c00

def z603 : W := mkw 0x0001000004040000 0x0000100000404000 0x100300000604000b 0x2100300000604000

def z604 : W := mkw 0x196167a2e77c6b16 0x4196167a2e77c6b1 0xb1e7efe7c7fce73f 0xab1e7efe7c7fce73

def z605 : W := mkw 0x449fa16956d7e944 0x8449fa16956d7e94 0xd19ff3f9c7c7f9cf 0x7d19ff3f9c7c7f9c

def z606 : W := mkw 0x4dffe702f7bfe316 0x44dffe702f7bfe31 0x7fffe301ffffc00b 0xe7fffe301ffffc00

def z607 : W := mkw 0x200121005e1ef7bf 0x4200121005e1ef7b 0x700000003e3ffff8 0x0700000003e3ffff

def z608 : W := mkw 0x26bf7f7fdedfffff 0xc26bf7f7fdedffff 0xffffffffffffffff 0xffffffffffffffff

def z609 : W := mkw 0x0020070002082206 0x0002007000208220 0x1060030006380001 0x0106003000638000

def z610 : W := mkw 0x008b000004850000 0x0008b00000485000 0x1183000007c00001 0x01183000007c0000

def z611 : W := mkw 0x008a006900c10840 0x8008a006900c1084 0xc19810f801c739ce 0x7c19810f801c739c

def z612 : W := mkw 0x49cba16967f56944 0x849cba16967f5694 0x11e3e3e1c7f80001 0x011e3e3e1c7f8000

def z613 : W := mkw 0x0020070002082206 0x0002007000208220 0xb0640f06063ce73f 0xab0640f06063ce73

def z614 : W := mkw 0x0dfec60280000000 0x00dfec6028000000 0x8fffef07c0000007 0xe8fffef07c000000

def z615 : W := mkw 0x0000012002402804 0x0000001200240280 0x000013e000003804 0x1000013e00000380

def z616 : W := mkw 0x6fdfb97d7ff7fded 0x86fdfb97d7ff7fde 0xffffffffffffffff 0xffffffffffffffff

def z617 : W := mkw 0x9beadfebab683e0e 0x09beadfebab683e0 0x7fe3ffe1fff83e0d 0xf7fe3ffe1fff83e0

def z618 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x0ffcfcfe00000000 0xd0ffcfcfe0000000

def z619 : W := mkw 0x8fffdedf84850000 0x08fffdedf8485000 0xdfffffffc7c7000f 0xfdfffffffc7c7000

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x200400000004c00a 0xa200400000004c00

def z621 : W := mkw 0x0000012002402804 0x0000001200240280 0x5000000007c03808 0x05000000007c0380

def z622 : W := mkw 0x00016102c6146114 0x400016102c614611 0x9007e307c604e13f 0x29007e307c604e13

def z623 : W := mkw 0x22001814080014a9 0x022001814080014a 0xee001c1e38003ffc 0xfee001c1e38003ff

def z624 : W := mkw 0x04356702d61ee316 0x404356702d61ee31 0xfe7fef07fe3fe73f 0xefe7fef07fe3fe73

def z625 : W := mkw 0x0000016942402944 0x8000001694240294 0xc01813f9c00739ce 0x7c01813f9c00739c

def z626 : W := mkw 0x86345edf80000000 0x086345edf8000000 0x8e1c1fffc0000006 0xf8e1c1fffc000000

def z627 : W := mkw 0x24140014100280a1 0x024140014100280a 0xa01c0c1e0007e7fe 0xaa01c0c1e0007e7f

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018101800000006 0x7801810180000000

def z629 : W := mkw 0x4ddfa16977f7e944 0x84ddfa16977f7e94 0x7fffe3e1ffffc00b 0xe7fffe3e1ffffc00

def z630 : W := mkw 0x24140000180294a9 0x024140000180294a 0x6e1c00003807fffa 0xe6e1c00003807fff

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x018013e000000005 0x7018013e00000000

def z632 : W := mkw 0x049e800000000000 0x0049e80000000000 0x001fe00000000002 0x0001fe0000000000

def z633 : W := mkw 0x22217f16ce1c77bf 0x422217f16ce1c77b 0xb067ff1fc63cffff 0xbb067ff1fc63cfff

def z634 : W := mkw 0x228b197d4ec53ded 0x8228b197d4ec53de 0xd19b1fffc7c73fff 0x7d19b1fffc7c73ff

def z635 : W := mkw 0x0614181400000000 0x0061418140000000 0x0e040c0600000000 0x80e040c060000000

def z636 : W := mkw 0x5fdfb8a03df7dc08 0x05fdfb8a03df7dc0 0x7ffff0e03fffd80b 0xf7ffff0e03fffd80

def z637 : W := mkw 0x0000000000000000 0x0000000000000000 0x5180000007c00009 0x65180000007c0000

def z638 : W := mkw 0x0020470282082206 0x0002047028208220 0xb067ef07c638260f 0xab067ef07c638260

def z639 : W := mkw 0x82205e9680000000 0x082205e968000000 0x00000c0600000000 0x000000c060000000

def z640 : W := mkw 0x24140014100280a1 0x024140014100280a 0x00180018000300c0 0x000180018000300c

def z641 : W := mkw 0x4dffe602b5b7c000 0x04dffe602b5b7c00 0xffffef07ffffc00f 0xeffffef07ffffc00

def z642 : W := mkw 0x0200180008001408 0x0020018000800140 0x2e000c0038000600 0x82e000c003800060

def z643 : W := mkw 0xa69ed85f980294a9 0x0a69ed85f980294a 0xee1ffc1ff807fffe 0xfee1ffc1ff807fff

def z644 : W := mkw 0x008b006904c50840 0x8008b006904c5084 0x519b10f807c718cb 0x7519b10f807c718c

def z645 : W := mkw 0x1b613fa06f7c7f1e 0x41b613fa06f7c7f1 0x7fe01fe03ffcff3d 0xf7fe01fe03ffcff3

def z646 : W := mkw 0x0000016942402944 0x8000001694240294 0x000003e1c0000000 0x0000003e1c000000

def z647 : W := mkw 0x0000600280104010 0x4000060028010401 0x0004e0060000c030 0x00004e0060000c03

def z648 : W := mkw 0x4dde800031a38000 0x04dde800031a3800 0x6f9c000039c7c00a 0xe6f9c000039c7c00

def z649 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7f9800003fffc008 0x47f9800003fffc00

def z650 : W := mkw 0x5f74bfa03b7afe0e 0x05f74bfa03b7afe0 0x7fe4ffe03ff8fe0d 0xf7fe4ffe03ff8fe0

def z651 : W := mkw 0x0ffe9e8000000000 0x00ffe9e800000000 0x0fffffe000000007 0xf0fffffe00000000

def z652 : W := mkw 0x1ffe9fa02b683e0e 0x01ffe9fa02b683e0 0x7fffffe03ff83e0f 0xf7fffffe03ff83e0

def z653 : W := mkw 0x008a004900000000 0x0008a00490000000 0x019810f800000000 0x5019810f80000000

def z654 : W := mkw 0x449e800010838000 0x0449e80001083800 0x0018000000030000 0x0001800000003000

def z655 : W := mkw 0x1b617f82ef3c771e 0x41b617f82ef3c771 0xbe67ef07fe3ce73f 0xabe67ef07fe3ce73

def z656 : W := mkw 0x4dffa70037bfe206 0x04dffa70037bfe20 0x7fffef003fffe60f 0xe7fffef003fffe60

def z657 : W := mkw 0x194000a021600800 0x0194000a02160080 0x018000e001c00000 0x0018000e001c0000

def z658 : W := mkw 0x0001200004144000 0x0000120000414400 0x1063e00006380001 0x01063e0000638000

def z659 : W := mkw 0x6fde981439a394a9 0x06fde981439a394a 0xef9c1c1e39c7fffe 0xfef9c1c1e39c7fff

def z660 : W := mkw 0x100000002928160a 0x0100000002928160 0x2000000038380600 0x0200000003838060

def z661 : W := mkw 0x0001200004144000 0x0000120000414400 0xb067ec06063ce73f 0xab067ec06063ce73

def z662 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x518303e1c7c739c9 0x0518303e1c7c739c

def z663 : W := mkw 0x0000010002082206 0x0000001000208220 0x3000000006382608 0x0300000000638260

def z664 : W := mkw 0x12ab1fe94ecd3f4e 0x812ab1fe94ecd3f4 0xd19b1ff9c7c73fcf 0x7d19b1ff9c7c73fc

def z665 : W := mkw 0x6fdfb8143db7d4a9 0x06fdfb8143db7d4a 0x7fffec063fffc63b 0xe7fffec063fffc63

def z666 : W := mkw 0x100001200a483e0e 0x0100001200a483e0 0x0000000000003e00 0x00000000000003e0

def z667 : W := mkw 0x06357f16c61c6316 0x406357f16c61c631 0xbe7fff1fc63ce73f 0xfbe7fff1fc63ce73

def z668 : W := mkw 0x1f741fb42b683e0e 0x01f741fb42b683e0 0xfffc1ffe3ff83e0f 0xffffc1ffe3ff83e0

def z669 : W := mkw 0x0000010042002104 0x0000001004200210 0x80000301c0002104 0x080000301c000210

def z670 : W := mkw 0x00016002c4144110 0x400016002c414411 0xb067e007c63cc13b 0xab067e007c63cc13

def z671 : W := mkw 0x8ffedfdfc2082316 0x48ffedfdfc208231 0x8fffffffc0002737 0xf8fffffffc000273

def z672 : W := mkw 0x0000010002002004 0x0000001000200200 0x100003000600200d 0x2100003000600200

def z673 : W := mkw 0x008b004944850140 0x8008b00494485014 0xc01b1019c00739ce 0x7c01b1019c00739c

def z674 : W := mkw 0x1bcb19e96fe53d4c 0x81bcb19e96fe53d4 0xdf9b13f9ffc739cf 0x7df9b13f9ffc739c

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000c0600002734 0x080000c060000273

def z676 : W := mkw 0x0414000010028000 0x0041400001002800 0x4e18000038030000 0x44e1800003803000

def z677 : W := mkw 0x0fde981400000000 0x00fde98140000000 0x8ffffc1e00000007 0xf8ffffc1e0000000

def z678 : W := mkw 0x008b012046c52944 0x8008b012046c5294 0x519b000007c739cb 0x6519b000007c739c

def z679 : W := mkw 0x8ffffedfc4144110 0x48ffffedfc414411 0x8fffffffc004c137 0xf8fffffffc004c13

def z680 : W := mkw 0x3b601fa03b6abeaf 0x03b601fa03b6abea 0x7fe01fe03ffffffd 0xf7fe01fe03ffffff

def z681 : W := mkw 0x8f74fe9680184212 0x48f74fe968018421 0x2e64ec060038c630 0x82e64ec060038c63

def z682 : W := mkw 0xcffffffff7f7e944 0x8cffffffff7f7e94 0xfffffffffffff9cf 0xffffffffffffff9c

def z683 : W := mkw 0x208b01695ec7bded 0x8208b01695ec7bde 0xf19b13f9ffc7ffff 0x7f19b13f9ffc7fff

def z684 : W := mkw 0x008a004900810040 0x8008a00490081004 0x00180018000300c0 0x000180018000300c

def z685 : W := mkw 0x00004002c0000110 0x400004002c000011 0x80000007c0000130 0x080000007c000013

def z686 : W := mkw 0x24140014100280a1 0x024140014100280a 0x000400060000c030 0x0000400060000c03

def z687 : W := mkw 0x0bea1ec900000000 0x00bea1ec90000000 0x8ffb1ff9c0000007 0xf8ffb1ff9c000000

def z688 : W := mkw 0x2200197d4a403ded 0x82200197d4a403de 0x80001fffc0003ff4 0x180001fffc0003ff

def z689 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x2e7fe000383fc002 0x82e7fe000383fc00

def z690 : W := mkw 0x4d74e602b13ac212 0x44d74e602b13ac21 0x2e64ec063838c630 0x82e64ec063838c63

def z691 : W := mkw 0x3f741fb43b6abeaf 0x03f741fb43b6abea 0x7fe41fe63ff8fe3d 0xf7fe41fe63ff8fe3

def z692 : W := mkw 0x1bea1fe92b683e0e 0x01bea1fe92b683e0 0xfffb1ff9fff83e0f 0xffffb1ff9fff83e0

def z693 : W := mkw 0x0200180008001408 0x0020018000800140 0x4e00100038001800 0x54e0010003800180

def z694 : W := mkw 0x0000012042402944 0x8000001204240294 0x00000000000039c0 0x000000000000039c

def z695 : W := mkw 0x0000012002402804 0x0000001200240280 0xd19813f807c739cf 0x7d19813f807c739c

def z696 : W := mkw 0x26347e16981ad6bb 0x426347e16981ad6b 0xee7cfc1e383ffffe 0xfee7cfc1e383ffff

def z697 : W := mkw 0x008b000004850000 0x0008b00000485000 0xd19b101807c739cf 0x7d19b101807c739c

def z698 : W := mkw 0x9ffedeffa9601c08 0x09ffedeffa9601c0 0xcffffffff9c01807 0xfcffffffff9c0180

def z699 : W := mkw 0x3f741fb43b6abeaf 0x03f741fb43b6abea 0x7ff81ff83ffb3ecd 0xf7ff81ff83ffb3ec

def z700 : W := mkw 0x4940a00021304000 0x04940a0002130400 0x0060e00000380000 0x00060e0000038000

def z701 : W := mkw 0x408b216977f7e944 0x8408b216977f7e94 0xf19b13f9fffff9cf 0x7f19b13f9fffff9c

def z702 : W := mkw 0x4ddfa12077f7e944 0x84ddfa12077f7e94 0x7fffe0003ffff9cb 0xe7fffe0003ffff9c

def z703 : W := mkw 0x4fdfb8003db7d408 0x04fdfb8003db7d40 0x7ffffc003ffffe0f 0xf7ffffc003ffffe0

def z704 : W := mkw 0x849fc17fc6c52944 0x8849fc17fc6c5294 0xd19ff3ffc7c739cf 0x7d19ff3ffc7c739c

def z705 : W := mkw 0x0614181400000000 0x0061418140000000 0xce1c1c1e000739ce 0xfce1c1c1e000739c

def z706 : W := mkw 0x22001814180294a9 0x022001814180294a 0xe0001c1e3807fffc 0x1e0001c1e3807fff

def z707 : W := mkw 0x849ec05f80000000 0x0849ec05f8000000 0x801ff3ffc0000006 0x1801ff3ffc000000

def z708 : W := mkw 0x008a016942c12944 0x8008a016942c1294 0x419813f9c1c318c0 0x5419813f9c1c318c

def z709 : W := mkw 0x1b605fa2ab683e0e 0x01b605fa2ab683e0 0xffe7ffe7fffcff3f 0xfffe7ffe7fffcff3

def z710 : W := mkw 0x92205feb8a483e0e 0x092205feb8a483e0 0x00001fe1c0003e04 0x100001fe1c0003e0

def z711 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xd19b13f9c7c318c7 0x7d19b13f9c7c318c

def z712 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x3fe01fe03ff80605 0xf3fe01fe03ff8060

def z713 : W := mkw 0x4d54a1697372e944 0x84d54a1697372e94 0xae64f3f9f838f9c4 0x9ae64f3f9f838f9c

def z714 : W := mkw 0x1b605fa2eb683f1e 0x41b605fa2eb683f1 0xffe41fe7fffcff3f 0xfffe41fe7fffcff3

def z715 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8fe7ffffc0000005 0x98fe7ffffc000000

def z716 : W := mkw 0x1b601fa06b683f0e 0x01b601fa06b683f0 0xffe01fe1fff83f0d 0xfffe01fe1fff83f0

def z717 : W := mkw 0x100121206ffd7f5e 0xc100121206ffd7f5 0x700000003ffffff8 0x0700000003ffffff

def z718 : W := mkw 0x8fdfb9dd461c6316 0x48fdfb9dd461c631 0x3f9810f8063ce738 0x53f9810f8063ce73

def z719 : W := mkw 0x6fde987d39e39ce9 0x86fde987d39e39ce 0x4f9810f839c318c0 0x54f9810f839c318c

def z720 : W := mkw 0x1b4018a029601c08 0x01b4018a029601c0 0x5fe010e03ff81801 0x55fe010e03ff8180

def z721 : W := mkw 0x008a016942c12944 0x8008a016942c1294 0xc19b13f9c1c339c7 0x7c19b13f9c1c339c

def z722 : W := mkw 0x86345edf80000000 0x086345edf8000000 0x8e7fffffc0000007 0xf8e7fffffc000000

def z723 : W := mkw 0x00216702c69d6356 0xc00216702c69d635 0xb067ef07c63fe7ff 0xab067ef07c63fe7f

def z724 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xcffffffff80739cf 0xfcffffffff80739c

def z725 : W := mkw 0x1b4019a02b683e0e 0x01b4019a02b683e0 0x7f801ce03ff83e0c 0xf7f801ce03ff83e0

def z726 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xf1e7ef07c7fce73f 0xef1e7ef07c7fce73

def z727 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xb067ef07c638e735 0x8b067ef07c638e73

def z728 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xb067ef07c638c637 0xab067ef07c638c63

def z729 : W := mkw 0x56bfbfa01edffe0e 0x056bfbfa01edffe0 0x001fffe00007fe06 0x1001fffe00007fe0

def z730 : W := mkw 0x4d55a00035b7c000 0x04d55a00035b7c00 0x7e7ce0003fffc00a 0xe7e7ce0003fffc00

def z731 : W := mkw 0x0020660280184212 0x4002066028018421 0x2067ef07c038c631 0x82067ef07c038c63

def z732 : W := mkw 0x10012120677c6b16 0x410012120677c6b1 0x1000000007f80000 0x01000000007f8000

def z733 : W := mkw 0x8ffededfb1228000 0x08ffededfb122800 0xffffffffffffc00f 0xfffffffffffffc00

def z734 : W := mkw 0x8dfec6df80000000 0x08dfec6df8000000 0x01fbe3f9c0000001 0x001fbe3f9c000000

def z735 : W := mkw 0x8beadecb80000000 0x08beadecb8000000 0x8fe7ffe7c0000007 0xf8fe7ffe7c000000

def z736 : W := mkw 0x26357f16de1ef7bf 0x426357f16de1ef7b 0x5e7bf319fe3b18c1 0x55e7bf319fe3b18c

def z737 : W := mkw 0x802046cb80000000 0x0802046cb8000000 0x8067efe7c0000007 0xa8067efe7c000000

def z738 : W := mkw 0x8ffededf88001408 0x08ffededf8800140 0xeffffffff804ff3f 0xfeffffffff804ff3

def z739 : W := mkw 0xc2217edfb5b7c000 0x0c2217edfb5b7c00 0xf0001fffffffc00c 0x1f0001fffffffc00

def z740 : W := mkw 0x449fa0491497c000 0x0449fa0491497c00 0x801fe019c007c002 0x0801fe019c007c00

def z741 : W := mkw 0x8fded8df80000000 0x08fded8df8000000 0x8f9ff3ffc0000007 0x78f9ff3ffc000000

def z742 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xcfffffffc000380f 0xfcfffffffc000380

def z743 : W := mkw 0x6ddfa00035b7c0a1 0x06ddfa00035b7c0a 0x7fffe0003fffc1fb 0xe7fffe0003fffc1f

def z744 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0xfff81ff83ff83e0f 0xffff81ff83ff83e0

def z745 : W := mkw 0x8ffededf80810000 0x08ffededf8081000 0xcfffffffc1c30007 0xfcfffffffc1c3000

def z746 : W := mkw 0x3b601fb42b683eaf 0x03b601fb42b683ea 0x7fe01ff83ff83ecd 0xf7fe01ff83ff83ec

def z747 : W := mkw 0xa49ec05f900280a1 0x0a49ec05f900280a 0xc19ff3ffc007f9ff 0x7c19ff3ffc007f9f

def z748 : W := mkw 0x449fe04bd497c150 0xc449fe04bd497c15 0x801fe01fc007c1f2 0x0801fe01fc007c1f

def z749 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7ffff0003ffff80f 0xf7ffff0003ffff80

def z750 : W := mkw 0x8ffededf88001408 0x08ffededf8800140 0xcffffffff8001807 0xfcffffffff800180

def z751 : W := mkw 0x4d55a00035b7c000 0x04d55a00035b7c00 0x3e64e0003ff8c000 0x83e64e0003ff8c00

def z752 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xa067ef07c03ce736 0x8a067ef07c03ce73

def z753 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x01fbe3e1c0000003 0x601fbe3e1c000000

def z754 : W := mkw 0x008a016942c12944 0x8008a016942c1294 0xc19813f9c1c739ce 0x7c19813f9c1c739c

def z755 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x3fffe0003ff8c003 0xe3fffe0003ff8c00

def z756 : W := mkw 0x00aa666b80d94a52 0xc00aa666b80d94a5 0x61fcfcfe01fbdef0 0xd61fcfcfe01fbdef

def z757 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xc19b13f9c1c739c6 0x5c19b13f9c1c739c

def z758 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xbfffffffc638000f 0xfbfffffffc638000

def z759 : W := mkw 0x661539347ff7fded 0x8661539347ff7fde 0xfe1c1c1e3ffffffe 0xffe1c1c1e3ffffff

def z760 : W := mkw 0x949ec17fab683e0e 0x0949ec17fab683e0 0xf01fe01ffff83e0a 0x0f01fe01ffff83e0

def z761 : W := mkw 0x4415200035b7c000 0x04415200035b7c00 0x7e7fe0003fffc00b 0xe7e7fe0003fffc00

def z762 : W := mkw 0x008a016942c12944 0x8008a016942c1294 0xd19813f9c7c339cd 0x7d19813f9c7c339c

def z763 : W := mkw 0x9b60dfa2ab683e0e 0x09b60dfa2ab683e0 0x7fe0ffe03ff83e0d 0xf7fe0ffe03ff83e0

def z764 : W := mkw 0x00216602c41c4312 0x400216602c41c431 0xb067ec07c63cc73b 0xab067ec07c63cc73

def z765 : W := mkw 0x10012120677c6b16 0x410012120677c6b1 0x3000000007fce738 0x03000000007fce73

def z766 : W := mkw 0x4ddfa00075b7c100 0x04ddfa00075b7c10 0xffffe001ffffc10b 0xeffffe001ffffc10

def z767 : W := mkw 0x9ffededfa9201408 0x09ffededfa920140 0x8ffffffff8000007 0xf8ffffffff800000

def z768 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xd19b13f9c7c339c5 0x5d19b13f9c7c339c

def z769 : W := mkw 0x0b605e8280000000 0x00b605e828000000 0x0fe3ffe1c0000005 0xf0fe3ffe1c000000

def z770 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xf067ff07c63cff3f 0xff067ff07c63cff3

def z771 : W := mkw 0x0960468280000000 0x0096046828000000 0x81e7efe7c0000007 0xa81e7efe7c000000

def z772 : W := mkw 0x00216722c6dd6b56 0xc00216722c6dd6b5 0xf1e7ffe7c7ffffff 0xff1e7ffe7c7fffff

def z773 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0xffffe0003fffe10f 0xeffffe0003fffe10

def z774 : W := mkw 0x6ddfa01435b7c0a1 0x06ddfa01435b7c0a 0xffffec1e3fffe7ff 0xeffffec1e3fffe7f

def z775 : W := mkw 0x269f197d5ec7bded 0x8269f197d5ec7bde 0x3f870fe7ffc0c631 0x83f870fe7ffc0c63

def z776 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x81ffffffc0000007 0x181ffffffc000000

def z777 : W := mkw 0x008b004904850000 0x0008b00490485000 0xd19b13f9c7c739cf 0x7d19b13f9c7c739c

def z778 : W := mkw 0x4941200035b7c000 0x04941200035b7c00 0x7fe7e0003fffc00b 0xe7fe7e0003fffc00

def z779 : W := mkw 0x00216702c69d6316 0x400216702c69d631 0xf067ef07c7ffe73f 0xaf067ef07c7ffe73

def z780 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x81e3f3f9c0000005 0x181e3f3f9c000000

def z781 : W := mkw 0x0020660280184212 0x4002066028018421 0xa067ec07c038c632 0x8a067ec07c038c63

def z782 : W := mkw 0x8ffededfa9201408 0x08ffededfa920140 0xfffffffffff83e0f 0xffffffffffff83e0

def z783 : W := mkw 0x00216722c65c6b56 0xc00216722c65c6b5 0xb067ef07c63cffff 0xab067ef07c63cfff

def z784 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7f801fe03ff83e0c 0x57f801fe03ff83e0

def z785 : W := mkw 0xc9eac6cba1a10000 0x0c9eac6cba1a1000 0x01e3e3e1c1c00001 0x001e3e3e1c1c0000

def z786 : W := mkw 0xc49fa05d1497c000 0x0c49fa05d1497c00 0x001fe0180007c002 0x0001fe0180007c00

def z787 : W := mkw 0x500121207fffff4e 0x8500121207fffff4 0x700000003fffffc8 0x0700000003fffffc

def z788 : W := mkw 0x1b605fa2ab683e0e 0x01b605fa2ab683e0 0x7fe3ffe1fff83e0d 0xf7fe3ffe1fff83e0

def z789 : W := mkw 0x808ac04b80000000 0x0808ac04b8000000 0x0183e3e1c0000001 0x00183e3e1c000000

def z790 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x5fe013e03ff8380d 0x75fe013e03ff8380

def z791 : W := mkw 0x26141814180294a9 0x026141814180294a 0xfe7c1c1e3e3fffff 0xffe7c1c1e3e3ffff

def z792 : W := mkw 0x00216602c41c4312 0x400216602c41c431 0xa067ef07c03cc737 0xaa067ef07c03cc73

def z793 : W := mkw 0xa6bededf980294a9 0x0a6bededf980294a 0x801fffffc007fff6 0x1801fffffc007fff

def z794 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xaffffffff807c7f7 0xfaffffffff807c7f

def z795 : W := mkw 0x8dfec6cb80000000 0x08dfec6cb8000000 0x8ffff3f9c0000007 0xf8ffff3f9c000000

def z796 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xff9b13f9ffc739cf 0xfff9b13f9ffc739c

def z797 : W := mkw 0x00016002c4144110 0x400016002c414411 0xb067ec07c63ce73f 0xab067ec07c63ce73

def z798 : W := mkw 0x84bec6df80000000 0x084bec6df8000000 0x801fe3ffc0000002 0x0801fe3ffc000000

def z799 : W := mkw 0x09ca804900000000 0x009ca80490000000 0x81fbf3f9c0000007 0x781fbf3f9c000000

def z800 : W := mkw 0x00216722c6dd6b56 0xc00216722c6dd6b5 0xf07fff1fc7ffffff 0xff07fff1fc7fffff

def z801 : W := mkw 0x0ddfa00025344000 0x00ddfa0002534400 0x7fffe0003ffcc00b 0xe7fffe0003ffcc00

def z802 : W := mkw 0x8dfec6df80000000 0x08dfec6df8000000 0x81fff3ffc0000007 0x781fff3ffc000000

def z803 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x01e7efe7c0000001 0x801e7efe7c000000

def z804 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x5fe01fe03ff81805 0xf5fe01fe03ff8180

def z805 : W := mkw 0x3b601fa02b683eaf 0x03b601fa02b683ea 0x7fe01fe03ff83ffd 0xf7fe01fe03ff83ff

def z806 : W := mkw 0x00aa464b80000000 0x000aa464b8000000 0x81e7efe7c0000007 0xa81e7efe7c000000

def z807 : W := mkw 0x06be5e5f80000000 0x006be5e5f8000000 0x8fffffffc0000007 0xf8fffffffc000000

def z808 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x5fffe0003ffb0003 0xe5fffe0003ffb000

def z809 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xb067ff1fc63cffff 0xbb067ff1fc63cfff

def z810 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8fffefffc0000003 0x88fffefffc000000

def z811 : W := mkw 0x1b601fb42b683e0e 0x01b601fb42b683e0 0xffe01ffe3ff83e0d 0xfffe01ffe3ff83e0

def z812 : W := mkw 0x0960468280000000 0x0096046828000000 0x01e3e3e1c0000001 0x001e3e3e1c000000

def z813 : W := mkw 0x99eac6cba1280202 0x099eac6cba128020 0x01e3e3e1c0380001 0x001e3e3e1c038000

def z814 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xd1fff3f9c7c739cf 0xfd1fff3f9c7c739c

def z815 : W := mkw 0x0dde804910028000 0x00dde80491002800 0xeffff3f9f807f9cf 0xfeffff3f9f807f9c

def z816 : W := mkw 0x9ffededfa928160a 0x09ffededfa928160 0xfffffffffff8060f 0xffffffffffff8060

def z817 : W := mkw 0xb2205fff8a483eaf 0x0b2205fff8a483ea 0x80001fffc0003ff4 0x180001fffc0003ff

def z818 : W := mkw 0x8dfec6cb80000000 0x08dfec6cb8000000 0x0ffbe3e1c0000001 0x40ffbe3e1c000000

def z819 : W := mkw 0x6ddfa01435b7c0a1 0x06ddfa01435b7c0a 0xfffff01e3ffff9ff 0xffffff01e3ffff9f

def z820 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0xffffec063fffc00f 0xeffffec063fffc00

def z821 : W := mkw 0x89eac6cba1200000 0x089eac6cba120000 0x7fe3e3e1fff80009 0xe7fe3e3e1fff8000

def z822 : W := mkw 0x6bcbb8142db554a9 0x06bcbb8142db554a 0x91e3fc1e07f83ff5 0x191e3fc1e07f83ff

def z823 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x01e7e3e1c0000003 0xa01e7e3e1c000000

def z824 : W := mkw 0xaffededf880014a9 0x0affededf880014a 0x8fffffffc0000637 0xf8fffffffc000063

def z825 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x5fe01fe03ff83e05 0x55fe01fe03ff83e0

def z826 : W := mkw 0x26141814180294a9 0x026141814180294a 0xee1f1f1ff807ffff 0xfee1f1f1ff807fff

def z827 : W := mkw 0x09cb200025b54000 0x009cb200025b5400 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z828 : W := mkw 0x00216602841c4212 0x400216602841c421 0xb067ef07c63cc63f 0xab067ef07c63cc63

def z829 : W := mkw 0x0ffede8280000000 0x00ffede828000000 0x8fffffe7c0000007 0xf8fffffe7c000000

def z830 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7fffe0003fffe73b 0xe7fffe0003fffe73

def z831 : W := mkw 0xeffededfb9a394a9 0x0effededfb9a394a 0xeffffffff9c7ffff 0xfeffffffff9c7fff

def z832 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe01fe03fff3fcd 0xf7fe01fe03fff3fc

def z833 : W := mkw 0x1b4018a029601c08 0x01b4018a029601c0 0x7fe01ce03ff83e0d 0xf7fe01ce03ff83e0

def z834 : W := mkw 0x0020660280184212 0x4002066028018421 0xa067ef07c03ce73f 0xaa067ef07c03ce73

def z835 : W := mkw 0x00aa464b80000000 0x000aa464b8000000 0x01e3e3e1c0000001 0x001e3e3e1c000000

def z836 : W := mkw 0x1b605fa2eb683f1e 0x41b605fa2eb683f1 0x7fe01fe1fff83e0d 0xf7fe01fe1fff83e0

def z837 : W := mkw 0xa69ed85f980294a9 0x0a69ed85f980294a 0xef9ffffff807ffff 0xfef9ffffff807fff

def z838 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x3067ef07c63cc63b 0xa3067ef07c63cc63

def z839 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x3067ef07c63ce739 0x83067ef07c63ce73

def z840 : W := mkw 0x0dde804900000000 0x00dde80490000000 0x0fffe3e1c0000003 0xe0fffe3e1c000000

def z841 : W := mkw 0x100121206f7c7f1e 0x4100121206f7c7f1 0x700000003ff83e08 0x0700000003ff83e0

def z842 : W := mkw 0xcffededfb1228000 0x0cffededfb122800 0x8ffffffff8000007 0xf8ffffffff800000

def z843 : W := mkw 0x008b216946d56944 0x8008b216946d5694 0xd1fbf3f9c7ff39cf 0x7d1fbf3f9c7ff39c

def z844 : W := mkw 0x8f75dfb6c6c52944 0x88f75dfb6c6c5294 0x5e64ec0607c739c8 0x85e64ec0607c739c

def z845 : W := mkw 0x92205fffca483f1e 0x492205fffca483f1 0x80001fffc0003f34 0x180001fffc0003f3

def z846 : W := mkw 0x4ddfa04935b7c000 0x04ddfa04935b7c00 0x7fffe3e1ffffc00b 0xe7fffe3e1ffffc00

def z847 : W := mkw 0xeffededfb9a394a9 0x0effededfb9a394a 0xcffffffff9c318c7 0xfcffffffff9c318c

def z848 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x81ffffffc0000007 0xf81ffffffc000000

def z849 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8fffffffc004c137 0xf8fffffffc004c13

def z850 : W := mkw 0xa9eac6cb980294a9 0x0a9eac6cb980294a 0x61e3e3e1f807fff9 0x061e3e3e1f807fff

def z851 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7fffec003fffe60f 0xe7fffec003fffe60

def z852 : W := mkw 0x4ddfa04935b7c040 0x84ddfa04935b7c04 0x7fffe0183fffc0cb 0xe7fffe0183fffc0c

def z853 : W := mkw 0x82205edf80000000 0x082205edf8000000 0x8063ffffc0000005 0x18063ffffc000000

def z854 : W := mkw 0x3d7407b4336aaaa7 0x03d7407b4336aaaa 0x91fc03fe07ffc1f3 0x091fc03fe07ffc1f

def z855 : W := mkw 0xcddfa0c935b7c000 0x0cddfa0c935b7c00 0x7fffe0e03fffc00b 0xe7fffe0e03fffc00

def z856 : W := mkw 0x26141814180294a9 0x026141814180294a 0xee7ffc1e3807ffff 0xfee7ffc1e3807fff

def z857 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8fffffffc00039c7 0xf8fffffffc00039c

def z858 : W := mkw 0x4001212067f56944 0x84001212067f5694 0x5000000007ff39c8 0x05000000007ff39c

def z859 : W := mkw 0x4d54a0003132c000 0x04d54a0003132c00 0x7ffce0003fffc00b 0xe7ffce0003fffc00

def z860 : W := mkw 0xe49fe05f9497c0a1 0x0e49fe05f9497c0a 0x801fe01fc007c1f2 0x0801fe01fc007c1f

def z861 : W := mkw 0x09ca800021200000 0x009ca80002120000 0x7fe3e0003ff80009 0xe7fe3e0003ff8000

def z862 : W := mkw 0x82205edf80000000 0x082205edf8000000 0x8007ffffc0000006 0x18007ffffc000000

def z863 : W := mkw 0x6ddfa05d75b7c1e1 0x86ddfa05d75b7c1e 0xffffe01fffffc1fb 0xeffffe01fffffc1f

def z864 : W := mkw 0x4001212077f7e944 0x84001212077f7e94 0x700000003fffc008 0x0700000003fffc00

def z865 : W := mkw 0xabeadedf880014a9 0x0abeadedf880014a 0x81e3ffffc0003ff5 0x181e3ffffc0003ff

def z866 : W := mkw 0x1b605fa2ab683e1e 0x41b605fa2ab683e1 0x7fe01fe63ff83e3d 0xf7fe01fe63ff83e3

def z867 : W := mkw 0x8ffededf80810040 0x88ffededf8081004 0x8fffffffc00300c7 0xf8fffffffc00300c

def z868 : W := mkw 0x26141814180294a9 0x026141814180294a 0x6e1c1c1e3807fff8 0xd6e1c1c1e3807fff

def z869 : W := mkw 0x8beadecb80000000 0x08beadecb8000000 0x0fe3f3e1c0000001 0x50fe3f3e1c000000

def z870 : W := mkw 0x802046cb80000000 0x0802046cb8000000 0x0063e3e1c0000001 0x00063e3e1c000000

def z871 : W := mkw 0x008a006900c10840 0x8008a006900c1084 0x419b13f9c1c318c1 0x5419b13f9c1c318c

def z872 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xd19b13f9c7c719c3 0x5d19b13f9c7c719c

def z873 : W := mkw 0x1b4178a2ed745d18 0x41b4178a2ed745d1 0xcf87f0e7f9c4d932 0x5cf87f0e7f9c4d93

def z874 : W := mkw 0x0414000010028000 0x0041400001002800 0xee1c1c1e3807fffe 0xfee1c1c1e3807fff

def z875 : W := mkw 0x0940002021600800 0x0094000202160080 0x7fe010e03ff81809 0xf7fe010e03ff8180

def z876 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x0ffbfff9c0000005 0xf0ffbfff9c000000

def z877 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7fffec063fffc63b 0xe7fffec063fffc63

def z878 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xb067ec07c63ce73a 0x8b067ec07c63ce73

def z879 : W := mkw 0x8dfec6cb80000000 0x08dfec6cb8000000 0x0fe7e3e1c0000001 0x80fe7e3e1c000000

def z880 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0x4ffbf3f9f80318c1 0x54ffbf3f9f80318c

def z881 : W := mkw 0x8ffededfa1200000 0x08ffededfa120000 0x9fffffffc7f80007 0xf9fffffffc7f8000

def z882 : W := mkw 0x4ddfa00075b7c110 0x44ddfa00075b7c11 0x7fffe0003fffc13b 0xe7fffe0003fffc13

def z883 : W := mkw 0x26141814180294a9 0x026141814180294a 0xee181c1e3807fffc 0x5ee181c1e3807fff

def z884 : W := mkw 0x8dfec6df80000000 0x08dfec6df8000000 0x01e7e3e7c0000001 0x001e7e3e7c000000

def z885 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x01e3efe1c0000005 0xa01e3efe1c000000

def z886 : W := mkw 0x49cba00025b54000 0x049cba00025b5400 0x7fe7e0003ffcc00b 0xe7fe7e0003ffcc00

def z887 : W := mkw 0x8ffededf88001408 0x08ffededf8800140 0xaffffffff8000607 0xfaffffffff800060

def z888 : W := mkw 0x00216722c6dd6b56 0xc00216722c6dd6b5 0xb067ef07c7fce73f 0xab067ef07c7fce73

def z889 : W := mkw 0xaffededf880014a9 0x0affededf880014a 0xcfffffffc0073fff 0xfcfffffffc0073ff

def z890 : W := mkw 0x008b216946d56944 0x8008b216946d5694 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z891 : W := mkw 0x0bea5ecb80000000 0x00bea5ecb8000000 0x8fffffffc0000007 0xf8fffffffc000000

def z892 : W := mkw 0x86bededf80000000 0x086bededf8000000 0x807fffffc0000007 0xb807fffffc000000

def z893 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xd19b1fffc7c73fff 0x7d19b1fffc7c73ff

def z894 : W := mkw 0x4dfec702f3aba316 0x44dfec702f3aba31 0xcf980f07f9c32734 0x4cf980f07f9c3273

def z895 : W := mkw 0x02201f200a483e0e 0x002201f200a483e0 0x7fe01fe03ff83e0d 0xf7fe01fe03ff83e0

def z896 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xcffffffff8033ff7 0xfcffffffff8033ff

def z897 : W := mkw 0x8ddec05f80000000 0x08ddec05f8000000 0x8ffff3ffc0000007 0xf8ffff3ffc000000

def z898 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x3fe01fe03ff83e05 0x93fe01fe03ff83e0

def z899 : W := mkw 0x0021660284144000 0x0002166028414400 0xb067ef07c63ce73f 0xab067ef07c63ce73

def z900 : W := mkw 0x8fde98dd00000000 0x08fde98dd0000000 0x8ffff3f9c0000007 0xf8ffff3f9c000000

def z901 : W := mkw 0x26141814180294a9 0x026141814180294a 0xff9c1c1e3fc7ffff 0xfff9c1c1e3fc7fff

def z902 : W := mkw 0x9beadecba928160a 0x09beadecba928160 0x2fe3efe1f8380601 0x82fe3efe1f838060

def z903 : W := mkw 0x600121207ff7fded 0x8600121207ff7fde 0x700000003ffffff8 0x0700000003ffffff

def z904 : W := mkw 0x449fa0491497c040 0x8449fa0491497c04 0x001fe0180007c0c2 0x0001fe0180007c0c

def z905 : W := mkw 0xcffededf90838000 0x0cffededf9083800 0x8fffffffc0030007 0xf8fffffffc003000

def z906 : W := mkw 0x008b216946d56954 0xc008b216946d5695 0xd19b13f9c7c7f9ff 0x7d19b13f9c7c7f9f

def z907 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7fffe0003ffff9cb 0xe7fffe0003ffff9c

def z908 : W := mkw 0xaffededf880014a9 0x0affededf880014a 0xeffffffff8003fff 0xfeffffffff8003ff

def z909 : W := mkw 0x008b216946d56944 0x8008b216946d5694 0xd19ff3f9c7c7f9cf 0x7d19ff3f9c7c7f9c

def z910 : W := mkw 0x008a006900c10840 0x8008a006900c1084 0xc19b13f9c1c739cf 0x7c19b13f9c1c739c

def z911 : W := mkw 0x4ddea0003132c000 0x04ddea0003132c00 0x7fffe0003ff8c00b 0xe7fffe0003ff8c00

def z912 : W := mkw 0x12205febca483f5e 0xc12205febca483f5 0x80001fffc0003ff4 0x180001fffc0003ff

def z913 : W := mkw 0x4ddfa04935b7c000 0x04ddfa04935b7c00 0xffffe019ffffc00b 0xeffffe019ffffc00

def z914 : W := mkw 0x82aadedf80000000 0x082aadedf8000000 0x8003ffffc0000004 0x18003ffffc000000

def z915 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0xfffc1ffe3fffffff 0xffffc1ffe3ffffff

def z916 : W := mkw 0x0f745e9680000000 0x00f745e968000000 0x8fffffffc0000007 0xf8fffffffc000000

def z917 : W := mkw 0x1b601fa06b683f4e 0x81b601fa06b683f4 0x7fe01fe03ff83fcd 0xf7fe01fe03ff83fc

def z918 : W := mkw 0x008b006944c50940 0x8008b006944c5094 0xc19b13f9c1c719c7 0x7c19b13f9c1c719c

def z919 : W := mkw 0x02205e8280000000 0x002205e828000000 0x8067ffe7c0000007 0xb8067ffe7c000000

def z920 : W := mkw 0x249f605fd497c1f1 0xc249f605fd497c1f 0x801fe01fc007c1f2 0x0801fe01fc007c1f

def z921 : W := mkw 0xefde98dd39a394a9 0x0efde98dd39a394a 0x4f9810f839c318c0 0x54f9810f839c318c

def z922 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x9067ef07c63ce737 0x09067ef07c63ce73

def z923 : W := mkw 0x4ddea00031b3c000 0x04ddea00031b3c00 0x7ffce0003ffbc009 0xe7ffce0003ffbc00

def z924 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8fffffffc004210f 0xf8fffffffc004210

def z925 : W := mkw 0xaffededf900280a1 0x0affededf900280a 0xafffffffc007e7ff 0xfafffffffc007e7f

def z926 : W := mkw 0x26be5e5f980294a9 0x026be5e5f980294a 0xeffffffff807ffff 0xfeffffffff807fff

def z927 : W := mkw 0x0b601fa023602804 0x00b601fa02360280 0x7fe01fe03ff8380d 0xf7fe01fe03ff8380

def z928 : W := mkw 0x8ffededf80080202 0x08ffededf8008020 0xafffffffc0380607 0xfafffffffc038060

def z929 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0x3067ef07c638e63d 0xa3067ef07c638e63

def z930 : W := mkw 0x8dfec6cb80000000 0x08dfec6cb8000000 0x01ffe3e1c0000003 0x001ffe3e1c000000

def z931 : W := mkw 0xbf74de96b92a96ab 0x0bf74de96b92a96a 0x2e64ec063838c630 0x82e64ec063838c63

def z932 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x0fffffffc0000001 0xd0fffffffc000000

def z933 : W := mkw 0x19eb67ebe7fd6b56 0xc19eb67ebe7fd6b5 0x11e3e3e1c7f80001 0x011e3e3e1c7f8000

def z934 : W := mkw 0x86bededf80000000 0x086bededf8000000 0x8e1fffffc0000006 0xf8e1fffffc000000

def z935 : W := mkw 0x4d55a0003536c000 0x04d55a0003536c00 0x7fe7e0003ffcc00b 0xe7fe7e0003ffcc00

def z936 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xd19f1fffc7c739cf 0xfd19f1fffc7c739c

def z937 : W := mkw 0x1b4019a02b683e0e 0x01b4019a02b683e0 0x7fe010e03ff83e09 0xf7fe010e03ff83e0

def z938 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0xffe41fe63ff83e0f 0xfffe41fe63ff83e0

def z939 : W := mkw 0x1beb1ec96dad174a 0x81beb1ec96dad174 0xae7b0c19f83f07c2 0x8ae7b0c19f83f07c

def z940 : W := mkw 0xaffededf900280a1 0x0affededf900280a 0x8fffffffc00300c7 0xf8fffffffc00300c

def z941 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0xa1e7efe7c004e73f 0xaa1e7efe7c004e73

def z942 : W := mkw 0x12205fa2ca483f1e 0x412205fa2ca483f1 0x00001fe1c0003e04 0x100001fe1c0003e0

def z943 : W := mkw 0x49cba00025b54000 0x049cba00025b5400 0x3fe3e0003ff80001 0x83fe3e0003ff8000

def z944 : W := mkw 0x8beadedf80000000 0x08beadedf8000000 0x01e3f3f9c0000001 0x101e3f3f9c000000

def z945 : W := mkw 0x4ddfa04935b7c000 0x04ddfa04935b7c00 0xfffff3f9fffff9cf 0xffffff3f9fffff9c

def z946 : W := mkw 0x00aa464b80000000 0x000aa464b8000000 0xe1ffffffc007ffff 0xfe1ffffffc007fff

def z947 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0xffffe0063fffc13b 0xeffffe0063fffc13

def z948 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xd19813f9c7c739cc 0x5d19813f9c7c739c

def z949 : W := mkw 0x120019202b683e0e 0x0120019202b683e0 0x7f801fe03ff83e0d 0xf7f801fe03ff83e0

def z950 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7fe7e0003fffc009 0x87fe7e0003fffc00

def z951 : W := mkw 0xbffededfb92a96ab 0x0bffededfb92a96a 0xaffffffff838c637 0xfaffffffff838c63

def z952 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xafffffffc000c637 0xfafffffffc000c63

def z953 : W := mkw 0x8f74de9680000000 0x08f74de968000000 0x8fe7ffe7c0000007 0xf8fe7ffe7c000000

def z954 : W := mkw 0x4ddfa04975b7c140 0x84ddfa04975b7c14 0x7fffe001ffffc00b 0xe7fffe001ffffc00

def z955 : W := mkw 0x4d55a00035b7c000 0x04d55a00035b7c00 0x7fe4e0003fffc009 0xe7fe4e0003fffc00

def z956 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe013e03ff81809 0xf7fe013e03ff8180

def z957 : W := mkw 0x00206702c2186316 0x400206702c218631 0xa067ef07c038e737 0xaa067ef07c038e73

def z958 : W := mkw 0x8ffededf88001408 0x08ffededf8800140 0xeffffffff8073fcf 0xfeffffffff8073fc

def z959 : W := mkw 0x0d54800021200000 0x00d5480002120000 0x7fe4e0003ff80009 0xe7fe4e0003ff8000

def z960 : W := mkw 0x8dfec6cb90028000 0x08dfec6cb9002800 0x6fffe3e1f807c00b 0xe6fffe3e1f807c00

def z961 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x1fe003e03ff80001 0x01fe003e03ff8000

def z962 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x0ffff3f9c0000003 0xf0ffff3f9c000000

def z963 : W := mkw 0x89eac6df80000000 0x089eac6df8000000 0x81e3e3ffc0000001 0x081e3e3ffc000000

def z964 : W := mkw 0x8f74dedf80000000 0x08f74dedf8000000 0x8e67ffffc0000007 0xb8e67ffffc000000

def z965 : W := mkw 0x26141814180294a9 0x026141814180294a 0xae1c1c1e3807fff6 0x9ae1c1c1e3807fff

def z966 : W := mkw 0x00012120465c6b16 0x400012120465c6b1 0x7000000007fcff38 0x07000000007fcff3

def z967 : W := mkw 0x008a016902402804 0x0008a01690240280 0xd19b13f9c7c739cf 0x7d19b13f9c7c739c

def z968 : W := mkw 0x12205fa28a483e1e 0x412205fa28a483e1 0x00001fe600003e34 0x100001fe600003e3

def z969 : W := mkw 0x049e804900000000 0x0049e80490000000 0x819ff3f9c0000007 0x7819ff3f9c000000

def z970 : W := mkw 0x1b4019a02b683e0e 0x01b4019a02b683e0 0x5f8010e03ff81800 0x55f8010e03ff8180

def z971 : W := mkw 0xef74fe96b932d4a9 0x0ef74fe96b932d4a 0x2e64ec063838c630 0x82e64ec063838c63

def z972 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x519b13f9c7c338cd 0x7519b13f9c7c338c

def z973 : W := mkw 0x3b601fb42b683eaf 0x03b601fb42b683ea 0x7fe01fe63ff83e3d 0xf7fe01fe63ff83e3

def z974 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xf1fb13f9c7ff39cf 0xff1fb13f9c7ff39c

def z975 : W := mkw 0xcddfa05d35b7c000 0x0cddfa05d35b7c00 0x7fffe0183fffc00b 0xe7fffe0183fffc00

def z976 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0xfffffc1e3fffffff 0xffffffc1e3ffffff

def z977 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xfe67ef07fe3ce73f 0xefe67ef07fe3ce73

def z978 : W := mkw 0x0020464b80000000 0x00020464b8000000 0x8067ffffc0000007 0xb8067ffffc000000

def z979 : W := mkw 0x8dfec6df80000000 0x08dfec6df8000000 0x8fffe3ffc0000003 0xe8fffe3ffc000000

def z980 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0xffe31fe1fff83e0f 0xfffe31fe1fff83e0

def z981 : W := mkw 0x0960072023682a06 0x00960072023682a0 0x7fe01fe03ff83e0d 0xf7fe01fe03ff83e0

def z982 : W := mkw 0x8ffededf80080212 0x48ffededf8008021 0x8fffffffc0000637 0xf8fffffffc000063

def z983 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe013e03ff83e09 0x57fe013e03ff83e0

def z984 : W := mkw 0x0020470282082206 0x0002047028208220 0xb067ef07c63ce73f 0xab067ef07c63ce73

def z985 : W := mkw 0x82aa5edf80000000 0x082aa5edf8000000 0x81ffffffc0000007 0xf81ffffffc000000

def z986 : W := mkw 0x196007a023682a06 0x0196007a023682a0 0x5fe003e03ff80001 0x45fe003e03ff8000

def z987 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x01fbf3f9c0000001 0x501fbf3f9c000000

def z988 : W := mkw 0xbfde98fd39629ca9 0x0bfde98fd39629ca 0x4f9810f839c318c0 0x54f9810f839c318c

def z989 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xf07fef07c63fe73f 0xef07fef07c63fe73

def z990 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe01fe03ff81e01 0xd7fe01fe03ff81e0

def z991 : W := mkw 0x049f20001497c000 0x0049f20001497c00 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z992 : W := mkw 0x008b216946dd6b56 0xc008b216946dd6b5 0xf1fff3f9c7ffffff 0xff1fff3f9c7fffff

def z993 : W := mkw 0x008b016946cd2b56 0xc008b016946cd2b5 0xd19b13f9c7c73fff 0x7d19b13f9c7c73ff

def z994 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xeffffffff807d8cf 0xfeffffffff807d8c

def z995 : W := mkw 0x0020670282186216 0x4002067028218621 0xb067ef07c638e63f 0xab067ef07c638e63

def z996 : W := mkw 0x194000a021600800 0x0194000a02160080 0x7fe000e03ff80009 0xe7fe000e03ff8000

def z997 : W := mkw 0x449fa0495497c140 0x8449fa0495497c14 0x001fe001c007c002 0x0001fe001c007c00

def z998 : W := mkw 0x0b601e8029201408 0x00b601e802920140 0x7fe01fe03ff83e0d 0xf7fe01fe03ff83e0

def z999 : W := mkw 0x196007a02b683e0e 0x0196007a02b683e0 0x7fe003e03ff83e09 0xe7fe003e03ff83e0

def z1000 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xf19b13f9c7c7ffff 0x7f19b13f9c7c7fff

def z1001 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xdfffffffc7c0000f 0xfdfffffffc7c0000

def z1002 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7fe7e0003ff8c009 0xe7fe7e0003ff8c00

def z1003 : W := mkw 0x8ffededfa1200000 0x08ffededfa120000 0xaffffffff8380007 0xfaffffffff838000

def z1004 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe7ffe03ff83e0f 0xf7fe7ffe03ff83e0

def z1005 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7ffff3e03fffc00f 0xf7ffff3e03fffc00

def z1006 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x81fbe3f9c0000003 0x081fbe3f9c000000

def z1007 : W := mkw 0x6ddfa01435b7c0a1 0x06ddfa01435b7c0a 0x7fffe0183fffc0cb 0xe7fffe0183fffc0c

def z1008 : W := mkw 0x49cba00035b7c000 0x049cba00035b7c00 0x7fe3e0003fffc009 0xe7fe3e0003fffc00

def z1009 : W := mkw 0x0960068021200000 0x0096006802120000 0x7fe003e03ff80009 0xe7fe003e03ff8000

def z1010 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7fffe0003ffbc001 0xc7fffe0003ffbc00

def z1011 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe41fe03ffcfe0f 0xf7fe41fe03ffcfe0

def z1012 : W := mkw 0xbffededfb92a96ab 0x0bffededfb92a96a 0xeffffffff83fffff 0xfeffffffff83ffff

def z1013 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xefffffffc007ffff 0xfefffffffc007fff

def z1014 : W := mkw 0x92205fffca483f4e 0x892205fffca483f4 0x80001fffc0003fc4 0x180001fffc0003fc

def z1015 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe00fe03ff80609 0xe7fe00fe03ff8060

def z1016 : W := mkw 0x9b605fb6ab683e0e 0x09b605fb6ab683e0 0x7fe01fe63ff83e0d 0xf7fe01fe63ff83e0

def z1017 : W := mkw 0x0001210046146104 0x0000121004614610 0xb067ef07c63ce73f 0xab067ef07c63ce73

def z1018 : W := mkw 0x0d5520003536c000 0x00d5520003536c00 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z1019 : W := mkw 0x1b601fa06b683f1e 0x41b601fa06b683f1 0x7fe01fe03ff83f3d 0xf7fe01fe03ff83f3

def z1020 : W := mkw 0xaffededf900280a1 0x0affededf900280a 0xeffffffff807c1ff 0xfeffffffff807c1f

def z1021 : W := mkw 0x00216602c41c4312 0x400216602c41c431 0xa067ec07c03ce73e 0xaa067ec07c03ce73

def z1022 : W := mkw 0x100121204e5c7f1e 0x4100121204e5c7f1 0x30000000063cff38 0x030000000063cff3

def z1023 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xafffffffc000260f 0xfafffffffc000260

def z1024 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8e7fffffc0000006 0x98e7fffffc000000

def z1025 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xb07fef1fc63fe7ff 0xab07fef1fc63fe7f

def z1026 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xeffffffff800fe3f 0xfeffffffff800fe3

def z1027 : W := mkw 0x0dde800031228000 0x00dde80003122800 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z1028 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x0fe7ffe7c0000005 0xf0fe7ffe7c000000

def z1029 : W := mkw 0x89eac6cba1200000 0x089eac6cba120000 0x11e3e3e1c7f80001 0x011e3e3e1c7f8000

def z1030 : W := mkw 0x22205f7fca483fff 0xc22205f7fca483ff 0x80001fffc0003ff4 0x180001fffc0003ff

def z1031 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xcfffffffc00318c7 0xfcfffffffc00318c

def z1032 : W := mkw 0x196007a023682a06 0x0196007a023682a0 0x7fe013e03ff8380d 0xf7fe013e03ff8380

def z1033 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x5fffe0003fffc003 0x45fffe0003fffc00

def z1034 : W := mkw 0x200121205edfffff 0xc200121205edffff 0x700000003ffffff8 0x0700000003ffffff

def z1035 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7ff81fe03fff3e0f 0xf7ff81fe03fff3e0

def z1036 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xd19f13ffc7c7f9ff 0x7d19f13ffc7c7f9f

def z1037 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xf19f13f9c7c7f9cf 0xff19f13f9c7c7f9c

def z1038 : W := mkw 0x2fde985d180294a9 0x02fde985d180294a 0xeffffffff807ffff 0xfeffffffff807fff

def z1039 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0xf19b1ff9c7c73fcf 0xff19b1ff9c7c73fc

def z1040 : W := mkw 0xcffededfb1a38000 0x0cffededfb1a3800 0xeffffffff9c7c00f 0xfeffffffff9c7c00

def z1041 : W := mkw 0x4ddfa04975b7c140 0x84ddfa04975b7c14 0xfffff019fffff9cf 0xffffff019fffff9c

def z1042 : W := mkw 0x26141814180294a9 0x026141814180294a 0xce1c1c1e3807fff6 0x5ce1c1c1e3807fff

def z1043 : W := mkw 0x0200180008001408 0x0020018000800140 0xee1c1c1e3807fffe 0xfee1c1c1e3807fff

def z1044 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8fe7efe7c0000007 0xa8fe7efe7c000000

def z1045 : W := mkw 0x008a004900000000 0x0008a00490000000 0x81fff3f9c0000007 0xf81fff3f9c000000

def z1046 : W := mkw 0x1b601fa023682a06 0x01b601fa023682a0 0x7fe01fe03ff8000d 0xf7fe01fe03ff8000

def z1047 : W := mkw 0x008b006904c50840 0x8008b006904c5084 0xd19b13f9c7c718cf 0x7d19b13f9c7c718c

def z1048 : W := mkw 0x849ec05f80000000 0x0849ec05f8000000 0x819fe3ffc0000003 0x0819fe3ffc000000

def z1049 : W := mkw 0x8beadecb80000000 0x08beadecb8000000 0x01e3ffe1c0000005 0x101e3ffe1c000000

def z1050 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7ffbe0003fffc009 0x47ffbe0003fffc00

def z1051 : W := mkw 0x0001212046d56944 0x80001212046d5694 0x7000000007fff9c8 0x07000000007fff9c

def z1052 : W := mkw 0x0b4019202b603c0c 0x00b4019202b603c0 0x7fe01fe03ff83e0d 0xf7fe01fe03ff83e0

def z1053 : W := mkw 0x196007a023682a06 0x0196007a023682a0 0x3fe003e03ff80001 0x83fe003e03ff8000

def z1054 : W := mkw 0x0000016942402944 0x8000001694240294 0xd19813f9c7c739cf 0x7d19813f9c7c739c

def z1055 : W := mkw 0xc49fe05fd497c110 0x4c49fe05fd497c11 0x801fe01fc007c132 0x0801fe01fc007c13

def z1056 : W := mkw 0x4415212077f7e944 0x84415212077f7e94 0xfe1c10183ffff9ce 0xffe1c10183ffff9c

def z1057 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0xc1fbf3f9c00739cf 0x7c1fbf3f9c00739c

def z1058 : W := mkw 0x00216722c65c6b16 0x400216722c65c6b1 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z1059 : W := mkw 0x008b216946dd6b56 0xc008b216946dd6b5 0xd19b13f9c7ff39cf 0x7d19b13f9c7ff39c

def z1060 : W := mkw 0x3b601fb42b683eaf 0x03b601fb42b683ea 0xfff81ffe3fff3fff 0xffff81ffe3fff3ff

def z1061 : W := mkw 0x0dfec64b80000000 0x00dfec64b8000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1062 : W := mkw 0x00012120465c6b56 0xc00012120465c6b5 0x30000000063cfff8 0x030000000063cfff

def z1063 : W := mkw 0x8ffededf98029408 0x08ffededf9802940 0xeffffffff807fe0f 0xfeffffffff807fe0

def z1064 : W := mkw 0x4001212056d7e944 0x84001212056d7e94 0x5000000007c7f9c8 0x05000000007c7f9c

def z1065 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0xfffff0183fffc00f 0xffffff0183fffc00

def z1066 : W := mkw 0x649fa05d5497c1e1 0x8649fa05d5497c1e 0x801fe01fc007c1f2 0x0801fe01fc007c1f

def z1067 : W := mkw 0x0940012023602804 0x0094001202360280 0x7fe003e03ff80009 0xe7fe003e03ff8000

def z1068 : W := mkw 0xc49fe04b9497c000 0x0c49fe04b9497c00 0x001fe001c007c002 0x0001fe001c007c00

def z1069 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x3fe00fe03ff8260d 0xa3fe00fe03ff8260

def z1070 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x81e3efe7c0000005 0x081e3efe7c000000

def z1071 : W := mkw 0x8ffedecb80000000 0x08ffedecb8000000 0x0fffffe1c0000007 0xf0fffffe1c000000

def z1072 : W := mkw 0x3f747e96b93ad6bb 0x43f747e96b93ad6b 0x2e64ec063838c630 0x82e64ec063838c63

def z1073 : W := mkw 0x008b216946d56944 0x8008b216946d5694 0xf19b13f9c7fff9cf 0x7f19b13f9c7fff9c

def z1074 : W := mkw 0xcdfec6cbb1a38000 0x0cdfec6cbb1a3800 0x4ffbe3e1f9c30001 0x44ffbe3e1f9c3000

def z1075 : W := mkw 0xa6345edf980294a9 0x0a6345edf980294a 0xee7ffffff807ffff 0xfee7ffffff807fff

def z1076 : W := mkw 0x0940000021200000 0x0094000002120000 0x7fe7e0003ff8000b 0xe7fe7e0003ff8000

def z1077 : W := mkw 0x80aac6cb80000000 0x080aac6cb8000000 0x0003e3e1c0000000 0x00003e3e1c000000

def z1078 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe41fe63ff8fe3d 0xf7fe41fe63ff8fe3

def z1079 : W := mkw 0x4dde800031a38000 0x04dde800031a3800 0x7fffe0003ffb000b 0xe7fffe0003ffb000

def z1080 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x519b13f9c7c718cb 0x7519b13f9c7c718c

def z1081 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x01e3f3e1c0000005 0x701e3f3e1c000000

def z1082 : W := mkw 0x120139206f7c7f1e 0x4120139206f7c7f1 0xfe041c063ffcff3e 0xffe041c063ffcff3

def z1083 : W := mkw 0x00aa464b80000000 0x000aa464b8000000 0x81fbf3f9c0000007 0x781fbf3f9c000000

def z1084 : W := mkw 0x8dfec6cb80000000 0x08dfec6cb8000000 0x8fffefe7c0000007 0xe8fffefe7c000000

def z1085 : W := mkw 0x86bededf80000000 0x086bededf8000000 0x819fffffc0000007 0x7819fffffc000000

def z1086 : W := mkw 0x4ddfa04935b7c000 0x04ddfa04935b7c00 0x7ffff0f83fffc00b 0xf7ffff0f83fffc00

def z1087 : W := mkw 0x8ffededf90028000 0x08ffededf9002800 0xeffffffff807e73f 0xfeffffffff807e73

def z1088 : W := mkw 0x0b40188021200000 0x00b4018802120000 0x7fe010e03ff80009 0xf7fe010e03ff8000

def z1089 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0xffe01fe03ffc3f0f 0xfffe01fe03ffc3f0

def z1090 : W := mkw 0x196007a023682a06 0x0196007a023682a0 0x7fe00fe03ff8260d 0xe7fe00fe03ff8260

def z1091 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xcfffffffc007000f 0xfcfffffffc007000

def z1092 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x81e3e3e1c0000007 0x281e3e3e1c000000

def z1093 : W := mkw 0x4d55a00035b7c000 0x04d55a00035b7c00 0x7e67e0003fffc00b 0xa7e67e0003fffc00

def z1094 : W := mkw 0x4940a00021304000 0x04940a0002130400 0x7fe0e0003ff80009 0xe7fe0e0003ff8000

def z1095 : W := mkw 0x09ca804900000000 0x009ca80490000000 0x01e3e3e1c0000001 0x001e3e3e1c000000

def z1096 : W := mkw 0x8beadedf80000000 0x08beadedf8000000 0x8fe3ffffc0000005 0xf8fe3ffffc000000

def z1097 : W := mkw 0x0001212046d56954 0xc0001212046d5695 0x5000000007c7f9f8 0x05000000007c7f9f

def z1098 : W := mkw 0x8ffededf90028000 0x08ffededf9002800 0xcffffffff8030007 0xfcffffffff803000

def z1099 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe01ce03ff83e08 0xd7fe01ce03ff83e0

def z1100 : W := mkw 0x1b4019a02b603c0c 0x01b4019a02b603c0 0x7fe013e03ff8380d 0xf7fe013e03ff8380

def z1101 : W := mkw 0x9ffededfa928160a 0x09ffededfa928160 0xeffffffff8383e0f 0xfeffffffff8383e0

def z1102 : W := mkw 0x4ddfa00025b54000 0x04ddfa00025b5400 0x7fffe0003ff8000b 0xe7fffe0003ff8000

def z1103 : W := mkw 0x008b216946dd6b56 0xc008b216946dd6b5 0xf19f1fffc7ffffff 0xff19f1fffc7fffff

def z1104 : W := mkw 0x1b601e802928160a 0x01b601e802928160 0x7fe01fe03ff8060d 0xf7fe01fe03ff8060

def z1105 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xeffffffff800000f 0xfeffffffff800000

def z1106 : W := mkw 0x8beadecb88001408 0x08beadecb8800140 0x6fe3ffe1f8003e0d 0xf6fe3ffe1f8003e0

def z1107 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0x8fffffffc007fff7 0xf8fffffffc007fff

def z1108 : W := mkw 0x00216602c41c4312 0x400216602c41c431 0x2067ec07c038c630 0x82067ec07c038c63

def z1109 : W := mkw 0x49ebe76be7fd6b56 0xc49ebe76be7fd6b5 0x11e3e3e1c7f80001 0x011e3e3e1c7f8000

def z1110 : W := mkw 0x49cba00025b54000 0x049cba00025b5400 0x7ffbe0003fff000b 0xe7ffbe0003fff000

def z1111 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x519b13f9c7c739c9 0x5519b13f9c7c739c

def z1112 : W := mkw 0x1b605fa2ab683e0e 0x01b605fa2ab683e0 0xffe01fe7fff83e0d 0xfffe01fe7fff83e0

def z1113 : W := mkw 0xaffededf880014a9 0x0affededf880014a 0xafffffffc004ffff 0xfafffffffc004fff

def z1114 : W := mkw 0x6ddfa01435b7c0a1 0x06ddfa01435b7c0a 0x7fffe0063fffc03b 0xe7fffe0063fffc03

def z1115 : W := mkw 0xaffededf900280a1 0x0affededf900280a 0x8fffffffc000c037 0xf8fffffffc000c03

def z1116 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xb07fff1fc63ce73f 0xfb07fff1fc63ce73

def z1117 : W := mkw 0xa6bededf980294a9 0x0a6bededf980294a 0xee1ffffff807fffe 0xfee1ffffff807fff

def z1118 : W := mkw 0x12205fa28a483e0e 0x012205fa28a483e0 0x80001fe7c0003e04 0x180001fe7c0003e0

def z1119 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7ffce0003fffc008 0xc7ffce0003fffc00

def z1120 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xaffffffff800fff7 0xfaffffffff800fff

def z1121 : W := mkw 0xaffededf880014a9 0x0affededf880014a 0x8fffffffc00018c7 0xf8fffffffc00018c

def z1122 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8ffff3ffc0000003 0x58ffff3ffc000000

def z1123 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7e7fe0003fffc00a 0x87e7fe0003fffc00

def z1124 : W := mkw 0x3b605fb6eb683fbf 0x43b605fb6eb683fb 0xffe01ffffff83ffd 0xfffe01ffffff83ff

def z1125 : W := mkw 0x0001212046dd6b56 0xc0001212046dd6b5 0x5000000007ff39c8 0x05000000007ff39c

def z1126 : W := mkw 0x8beadecb80000000 0x08beadecb8000000 0x8ffbfff9c0000007 0xf8ffbfff9c000000

def z1127 : W := mkw 0x4ddfa04975b7c140 0x84ddfa04975b7c14 0xfffff3f9ffffc1cf 0xffffff3f9ffffc1c

def z1128 : W := mkw 0x8beadedf80000000 0x08beadedf8000000 0x81fbffffc0000007 0x781fbffffc000000

def z1129 : W := mkw 0x1b605fa2ab683e0e 0x01b605fa2ab683e0 0x7fe4ffe63ff83e0d 0xf7fe4ffe63ff83e0

def z1130 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x81e7e3e7c0000003 0x081e7e3e7c000000

def z1131 : W := mkw 0x008b016946cd2b46 0x8008b016946cd2b4 0xf19b13f9c7ff3fcf 0x7f19b13f9c7ff3fc

def z1132 : W := mkw 0x0940200021304000 0x0094020002130400 0x7fe4e0003ff8c009 0xe7fe4e0003ff8c00

def z1133 : W := mkw 0x1b4019a02b683e0e 0x01b4019a02b683e0 0x7f8013e03ff83e0d 0x77f8013e03ff83e0

def z1134 : W := mkw 0x8dfec6df80000000 0x08dfec6df8000000 0x81ffefffc0000007 0xa81ffefffc000000

def z1135 : W := mkw 0x00216722c65c6b16 0x400216722c65c6b1 0xb1e7efe7c7fce73f 0xab1e7efe7c7fce73

def z1136 : W := mkw 0x194001202b683e0e 0x0194001202b683e0 0x7fe013e03ff83e0d 0xf7fe013e03ff83e0

def z1137 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0xffe01fe63ff83f3d 0xfffe01fe63ff83f3

def z1138 : W := mkw 0x408ba16946d56944 0x8408ba16946d5694 0xd19bf3f9c7c739cf 0x7d19bf3f9c7c739c

def z1139 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xeffffffff803def7 0xfeffffffff803def

def z1140 : W := mkw 0x0b605e8288001408 0x00b605e828800140 0xefe7ffe7f804ff3f 0xfefe7ffe7f804ff3

def z1141 : W := mkw 0x92205fb68a483e0e 0x092205fb68a483e0 0x00001fe600003e04 0x100001fe600003e0

def z1142 : W := mkw 0xaffededf800000a1 0x0affededf800000a 0x8fffffffc00001f7 0xf8fffffffc00001f

def z1143 : W := mkw 0x32205fb6ca483fbf 0x432205fb6ca483fb 0x80001fffc0003ff4 0x180001fffc0003ff

def z1144 : W := mkw 0x500121207fffff1e 0x4500121207fffff1 0x700000003fffff38 0x0700000003fffff3

def z1145 : W := mkw 0xcffededfb1a38000 0x0cffededfb1a3800 0xfffffffffffb000f 0xffffffffffffb000

def z1146 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0x2fe7efe7f800c631 0x82fe7efe7f800c63

def z1147 : W := mkw 0x0940000021200000 0x0094000002120000 0x7fe013e03ff8000d 0xf7fe013e03ff8000

def z1148 : W := mkw 0x0020460280000000 0x0002046028000000 0x81e7ffe7c0000007 0xf81e7ffe7c000000

def z1149 : W := mkw 0x0ddf800025a50000 0x00ddf800025a5000 0x7fffe0003fff000b 0xe7fffe0003fff000

def z1150 : W := mkw 0x8ffededf90028000 0x08ffededf9002800 0x8fffffffc007c007 0xf8fffffffc007c00

def z1151 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x0fe3e3e1c0000001 0x00fe3e3e1c000000

def z1152 : W := mkw 0x0ffe9ec900000000 0x00ffe9ec90000000 0x8ffffff9c0000007 0xf8ffffff9c000000

def z1153 : W := mkw 0x0001212046dd6b56 0xc0001212046dd6b5 0x3000000007fce738 0x03000000007fce73

def z1154 : W := mkw 0x102167a2c65c6b16 0x4102167a2c65c6b1 0xb067efe7c63ce73f 0xab067efe7c63ce73

def z1155 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7ff81ff83ffb3ecd 0xf7ff81ff83ffb3ec

def z1156 : W := mkw 0xa2205edf880014a9 0x0a2205edf880014a 0xa067ffffc004ffff 0xba067ffffc004fff

def z1157 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0xafffffffc004c00f 0xfafffffffc004c00

def z1158 : W := mkw 0xcffededfa1a10000 0x0cffededfa1a1000 0x8fffffffc1c00007 0xf8fffffffc1c0000

def z1159 : W := mkw 0x0b601f8023282206 0x00b601f802328220 0x7fe01fe03ff8260d 0xf7fe01fe03ff8260

def z1160 : W := mkw 0x00216722c65c6b16 0x400216722c65c6b1 0xb067ffe7c63cff3f 0xbb067ffe7c63cff3

def z1161 : W := mkw 0x8b605edf80000000 0x08b605edf8000000 0x8fe7ffffc0000007 0xf8fe7ffffc000000

def z1162 : W := mkw 0x869ed85f80000000 0x0869ed85f8000000 0x8f9fffffc0000007 0xf8f9fffffc000000

def z1163 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe00fe03ff83e09 0x87fe00fe03ff83e0

def z1164 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xb067ef07c63cc733 0x8b067ef07c63cc73

def z1165 : W := mkw 0x8ffededf90028000 0x08ffededf9002800 0xaffffffff800c007 0xfaffffffff800c00

def z1166 : W := mkw 0xaffededf900280a1 0x0affededf900280a 0xcfffffffc007f9ff 0xfcfffffffc007f9f

def z1167 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xaffffffff804e73f 0xfaffffffff804e73

def z1168 : W := mkw 0x0941200025344000 0x0094120002534400 0x7fe3e0003ff80009 0xe7fe3e0003ff8000

def z1169 : W := mkw 0x0fde985d00000000 0x00fde985d0000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1170 : W := mkw 0x4ddfa01435b7c000 0x04ddfa01435b7c00 0xffffe01e3fffc00b 0xeffffe01e3fffc00

def z1171 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8ffbffffc0000005 0x58ffbffffc000000

def z1172 : W := mkw 0x0001212046dd6b56 0xc0001212046dd6b5 0xf01c1c1e07fffffe 0xff01c1c1e07fffff

def z1173 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7ffff0183fffd8cb 0xf7ffff0183fffd8c

def z1174 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xcffffffff807d9f7 0xfcffffffff807d9f

def z1175 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8fffffffc00701c7 0xf8fffffffc00701c

def z1176 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xf067ef07c63fffff 0xaf067ef07c63ffff

def z1177 : W := mkw 0x8ffededf88001408 0x08ffededf8800140 0x8fffffffc0003e07 0xf8fffffffc0003e0

def z1178 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x1fe3e0003ff80001 0x01fe3e0003ff8000

def z1179 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8f9fffffc0000006 0x58f9fffffc000000

def z1180 : W := mkw 0x8beadedf80000000 0x08beadedf8000000 0x81e7ffffc0000007 0xb81e7ffffc000000

def z1181 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0x8ffffffff8000007 0xf8ffffffff800000

def z1182 : W := mkw 0x0001212046dd6b56 0xc0001212046dd6b5 0x1000000007f80000 0x01000000007f8000

def z1183 : W := mkw 0x26141814180294a9 0x026141814180294a 0xef9c1ffe3807ffff 0xfef9c1ffe3807fff

def z1184 : W := mkw 0x9ffededfa1280202 0x09ffededfa128020 0x8fffffffc0380007 0xf8fffffffc038000

def z1185 : W := mkw 0x008b016946c52944 0x8008b016946c5294 0x919b13f9c7c739c7 0x1919b13f9c7c739c

def z1186 : W := mkw 0x00216722c65c6b16 0x400216722c65c6b1 0xf067ef07c7fcff3f 0xaf067ef07c7fcff3

def z1187 : W := mkw 0xc49fe05fd497c140 0x8c49fe05fd497c14 0x801fe01fc007c1c2 0x0801fe01fc007c1c

def z1188 : W := mkw 0x300121207f7effbf 0x4300121207f7effb 0x700000003ffffff8 0x0700000003ffffff

def z1189 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0xffffe0183fffc1cb 0xeffffe0183fffc1c

def z1190 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xeffffffff807c63f 0xfeffffffff807c63

def z1191 : W := mkw 0xaffededfb92294a9 0x0affededfb92294a 0xffffffffffffffff 0xffffffffffffffff

def z1192 : W := mkw 0x4d54a0003132c000 0x04d54a0003132c00 0x3fe4e0003ff8c001 0x83fe4e0003ff8c00

def z1193 : W := mkw 0x1b4018a029601c08 0x01b4018a029601c0 0x7f8010e03ff81808 0x57f8010e03ff8180

def z1194 : W := mkw 0x1b601ea029681e0a 0x01b601ea029681e0 0x7fe01ce03ff81e09 0xf7fe01ce03ff81e0

def z1195 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0xffffe301ffffc00f 0xeffffe301ffffc00

def z1196 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8ffbf3f9c0000007 0x78ffbf3f9c000000

def z1197 : W := mkw 0x361539347f7effbf 0x4361539347f7effb 0xfe1c1c1e3ffffffe 0xffe1c1c1e3ffffff

def z1198 : W := mkw 0x261539345edfffff 0xc261539345edffff 0xfe1c1c1e3ffffffe 0xffe1c1c1e3ffffff

def z1199 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x7ffbe0003ffb0009 0xe7ffbe0003ffb000

def z1200 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0x7fe01fe03ffcff3d 0xf7fe01fe03ffcff3

def z1201 : W := mkw 0x8beadecb80000000 0x08beadecb8000000 0x0fe3efe1c0000001 0x80fe3efe1c000000

def z1202 : W := mkw 0xaffededf980294a9 0x0affededf980294a 0xeffffffff8033ecf 0xfeffffffff8033ec

def z1203 : W := mkw 0x8ffededfa1200000 0x08ffededfa120000 0xcffffffff9c00007 0xfcffffffff9c0000

def z1204 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x8fffffffc0002737 0xf8fffffffc000273

def z1205 : W := mkw 0x8beadedf80000000 0x08beadedf8000000 0x01e3efe7c0000001 0x001e3efe7c000000

def z1206 : W := mkw 0x2f745e96980294a9 0x02f745e96980294a 0xeffffffff807ffff 0xfeffffffff807fff

def z1207 : W := mkw 0x008a006900c10840 0x8008a006900c1084 0xc19813f9c1c318c4 0x5c19813f9c1c318c

def z1208 : W := mkw 0x84bec65f80000000 0x084bec65f8000000 0x81ffffffc0000007 0xf81ffffffc000000

def z1209 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x3fe7e0003ffcc00b 0xa3fe7e0003ffcc00

def z1210 : W := mkw 0x3b601fb42b683eaf 0x03b601fb42b683ea 0xffe41ffe3ffcffff 0xfffe41ffe3ffcfff

def z1211 : W := mkw 0x1b601fa02b683e0e 0x01b601fa02b683e0 0xffe01ff83ff83fcd 0xfffe01ff83ff83fc

def z1212 : W := mkw 0x808ac04b80000000 0x0808ac04b8000000 0x819bf3f9c0000007 0x7819bf3f9c000000

def z1213 : W := mkw 0x00216702c61c6316 0x400216702c61c631 0xb1e7ffe7c63ce73f 0xfb1e7ffe7c63ce73

def z1214 : W := mkw 0x26141814180294a9 0x026141814180294a 0xee1c0c1e3807fffa 0x8ee1c0c1e3807fff

def z1215 : W := mkw 0x9ffededf8808160a 0x09ffededf8808160 0x8fffffffc0000607 0xf8fffffffc000060

def z1216 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x5ffbe0003fff000b 0x65ffbe0003fff000

def z1217 : W := mkw 0x0001012046442904 0x0000101204644290 0xd19b13f9c7c739cf 0x7d19b13f9c7c739c

def z1218 : W := mkw 0x4ddfa00035b7c000 0x04ddfa00035b7c00 0x3fffe0003fffc003 0x83fffe0003fffc00

def z1219 : W := mkw 0x8ffededf80000000 0x08ffededf8000000 0x0fffefe7c0000003 0xe0fffefe7c000000

def z1220 : W := mkw 0x4001212077ffeb56 0xc4001212077ffeb5 0x700000003ffffff8 0x0700000003ffffff

def z1221 : W := mkw 0x008a404b80000000 0x0008a404b8000000 0x819ff3ffc0000007 0x7819ff3ffc000000

def z1222 : W := mkw 0x4001212067f56944 0x84001212067f5694 0x1000000007f80000 0x01000000007f8000

def z1223 : W := mkw 0xadfec6df900280a1 0x0adfec6df900280a 0x81ffe3ffc007c1f3 0x081ffe3ffc007c1f

def z1224 : W := mkw 0x89eac6cb80000000 0x089eac6cb8000000 0x0fe3e3e1c0000001 0xe0fe3e3e1c000000

def z1225 : W := mkw 0x1b601ea029601c08 0x01b601ea029601c0 0x7fe01fe03ff8180d 0xf7fe01fe03ff8180

def z1226 : W := mkw 0x4ddfa00075b7c140 0x84ddfa00075b7c14 0x7fffe0003fffc1cb 0xe7fffe0003fffc1c

def z1227 : W := mkw 0x4d54a0003132c000 0x04d54a0003132c00 0x7e64e0003ff8c008 0x87e64e0003ff8c00

def z1228 : W := mkw 0x1b605fa2eb683f1e 0x41b605fa2eb683f1 0xffe7ffe7fff83f3f 0xfffe7ffe7fff83f3

def z1229 : W := mkw 0x008a016902c12844 0x8008a016902c1284 0xd19b13f9c7c338cf 0x7d19b13f9c7c338c

def z1230 : W := mkw 0x8ffededf90028000 0x08ffededf9002800 0xeffffffff807f9cf 0xfeffffffff807f9c

def z1231 : W := mkw 0x49cba00025b54000 0x049cba00025b5400 0x5fe3e0003ff80001 0x45fe3e0003ff8000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z8,z2,z3,z4,z5,z9]),(0,[z1,z10,z2,z3,z4,z5,z9])],[(0,[z1,z11,z3,z4,z5,z12,z9]),(0,[z1,z2,z3,z4,z5,z13,z9]),(0,[z1,z2,z3,z14,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z16,z4,z5,z17,z9])],[(0,[z1,z2,z11,z3,z4,z5,z18]),(0,[z1,z2,z3,z19,z4,z5,z9]),(0,[z1,z2,z20,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z21,z22]),(0,[z1,z2,z3,z4,z5,z23,z9]),(0,[z1,z2,z3,z4,z5,z9,z24])],[(0,[z25,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z26,z5,z9]),(0,[z27,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z28,z4,z5,z9]),(0,[z1,z3,z4,z5,z12,z9,z29]),(0,[z1,z2,z3,z4,z5,z9,z30]),(0,[z1,z2,z31,z3,z5,z32,z9]),(0,[z1,z2,z33,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z34]),(0,[z1,z2,z3,z35,z4,z5,z36]),(0,[z1,z2,z3,z35,z37,z5,z9]),(0,[z1,z2,z4,z5,z9,z38,z39]),(0,[z1,z2,z3,z4,z21,z9,z39]),(0,[z1,z2,z3,z4,z5,z9,z40])],[(0,[z1,z2,z3,z4,z41,z5,z9]),(0,[z42,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z43,z4,z44,z5,z9]),(0,[z1,z2,z3,z45,z4,z5,z9]),(0,[z1,z2,z46,z3,z4,z5,z9]),(0,[z1,z2,z47,z3,z4,z5,z9]),(0,[z1,z2,z48,z3,z44,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z49])],[(0,[z1,z2,z50,z3,z4,z5,z9]),(0,[z51,z1,z2,z16,z3,z4,z9]),(0,[z52,z1,z2,z53,z3,z4,z5]),(0,[z1,z2,z54,z3,z4,z5,z15]),(0,[z1,z2,z55,z3,z4,z5,z17]),(0,[z1,z2,z3,z4,z5,z9,z56])],[(0,[z1,z2,z3,z4,z57,z5,z18]),(0,[z1,z2,z3,z4,z5,z58,z9]),(0,[z1,z2,z3,z4,z5,z59,z9]),(0,[z60,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z48,z61,z5,z9])]],
   [[(0,[z62,z1,z2,z3,z4,z5,z9]),(0,[z63,z1,z2,z3,z4,z5,z17]),(1,[z1,z2,z3,z4,z5,z64])],[(0,[z1,z65,z2,z3,z4,z5,z9]),(1,[z1,z2,z66,z4,z5,z9]),(0,[z67,z1,z2,z3,z4,z68,z9]),(0,[z1,z2,z48,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z69]),(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z71,z1,z2,z3,z4,z5,z9])],[(0,[z72,z1,z2,z3,z4,z5,z9]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z9]),(0,[z74,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z48,z3,z61,z5,z9]),(0,[z1,z2,z3,z61,z4,z5,z6]),(0,[z1,z2,z55,z4,z75,z5,z9]),(0,[z76,z1,z2,z3,z4,z5,z18]),(0,[z77,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z55,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z78,z9])],[(0,[z1,z2,z3,z4,z5,z79,z9]),(0,[z1,z2,z3,z4,z80,z5,z81]),(0,[z82,z1,z2,z3,z4,z5,z9]),(0,[z83,z1,z2,z3,z4,z84,z9]),(0,[z1,z2,z3,z4,z5,z85,z9]),(0,[z86,z1,z2,z3,z4,z5,z9])],[(0,[z87,z1,z88,z2,z3,z4,z5]),(0,[z1,z2,z3,z89,z4,z5,z9]),(0,[z63,z1,z2,z3,z4,z5,z9])],[(1,[z1,z2,z90,z4,z5,z9]),(0,[z7,z2,z3,z4,z57,z5,z9])],[(1,[z1,z10,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z91,z5]),(0,[z1,z2,z92,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z93])]],
   [[(0,[z1,z2,z3,z4,z94,z5,z9]),(0,[z1,z2,z95,z3,z4,z5,z9]),(1,[z60,z2,z3,z4,z5,z9]),(0,[z1,z2,z96,z3,z4,z5,z9]),(0,[z1,z2,z3,z5,z18,z9,z6]),(0,[z1,z2,z97,z3,z4,z5,z9])],[(0,[z51,z1,z2,z98,z3,z4,z9]),(0,[z1,z2,z3,z99,z4,z5,z9]),(0,[z1,z100,z3,z101,z4,z5,z9]),(0,[z1,z2,z102,z3,z4,z5,z9]),(0,[z1,z103,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z104,z9]),(0,[z1,z2,z31,z3,z4,z5,z6])],[(0,[z105,z65,z2,z3,z4,z5,z9]),(0,[z1,z106,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z107,z4,z5,z9]),(1,[z1,z2,z108,z3,z4,z5]),(0,[z1,z2,z3,z109,z4,z5,z9])],[(0,[z1,z2,z3,z110,z4,z5,z18]),(0,[z1,z2,z111,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z18,z112])],[(1,[z1,z2,z113,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z114,z9]),(0,[z1,z2,z54,z3,z4,z5,z93]),(0,[z1,z2,z3,z4,z5,z115,z9]),(0,[z1,z2,z3,z4,z5,z17,z9]),(0,[z1,z2,z3,z4,z5,z9,z116])],[(0,[z117,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z118,z9]),(0,[z1,z2,z3,z4,z5,z119,z9]),(0,[z1,z2,z3,z4,z5,z120,z9])],[(0,[z1,z2,z3,z121,z4,z5,z9]),(1,[z122,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z123,z4,z5,z9]),(0,[z1,z2,z3,z4,z37,z5,z9]),(0,[z1,z2,z3,z4,z5,z124,z18])],[(0,[z1,z2,z125,z3,z4,z5,z9]),(0,[z1,z126,z2,z3,z4,z5,z6]),(0,[z83,z1,z2,z127,z4,z5,z9]),(0,[z1,z2,z3,z128,z4,z5,z9]),(0,[z1,z2,z129,z3,z4,z5,z9]),(0,[z1,z2,z3,z35,z4,z5,z6]),(0,[z130,z1,z2,z3,z4,z5,z18])]],
   [[(1,[z1,z2,z3,z4,z131,z9]),(0,[z1,z2,z3,z4,z5,z29,z6]),(0,[z1,z2,z55,z53,z4,z5,z9])],[(0,[z132,z1,z2,z3,z4,z5,z9]),(0,[z8,z1,z2,z3,z57,z5,z9]),(0,[z51,z1,z2,z133,z4,z5,z9]),(0,[z1,z2,z3,z134,z5,z18,z9])],[(0,[z1,z2,z135,z4,z44,z5,z9]),(0,[z7,z1,z2,z3,z4,z136,z9]),(0,[z1,z2,z3,z4,z137,z5,z9]),(0,[z1,z2,z3,z61,z4,z138,z9]),(0,[z1,z2,z55,z3,z4,z5,z22]),(0,[z1,z139,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z140,z5,z9]),(0,[z1,z2,z3,z4,z141,z5,z9]),(0,[z1,z2,z3,z142,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z143]),(0,[z1,z2,z144,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z32,z9])],[(0,[z1,z2,z3,z4,z145,z5,z9]),(0,[z1,z2,z146,z3,z4,z5,z9])],[(0,[z1,z2,z11,z3,z4,z5,z6]),(0,[z1,z2,z147,z3,z4,z5,z9]),(0,[z1,z2,z16,z148,z3,z4,z9]),(0,[z1,z2,z148,z3,z4,z5,z6])],[(0,[z149,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z150,z9]),(0,[z1,z2,z3,z4,z151,z5,z9])],[(0,[z8,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z152,z9]),(0,[z153,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z154,z4,z5,z9]),(0,[z1,z2,z16,z3,z4,z37,z9]),(0,[z1,z2,z3,z4,z155,z5,z9]),(0,[z1,z2,z3,z4,z5,z156,z18])]],
   [[(0,[z1,z157,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z158])],[(0,[z1,z2,z3,z159,z4,z5,z9])],[(0,[z1,z2,z3,z4,z57,z5,z6]),(0,[z1,z2,z3,z4,z160,z5,z9]),(0,[z1,z2,z3,z161,z4,z5,z9]),(0,[z1,z2,z100,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z162,z5,z9]),(0,[z1,z2,z3,z163,z4,z5,z18]),(0,[z1,z2,z108,z3,z4,z5,z9]),(0,[z1,z88,z2,z3,z4,z5,z18])],[(0,[z1,z2,z3,z4,z5,z164,z9]),(0,[z1,z2,z3,z133,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z165,z9]),(0,[z1,z2,z148,z3,z4,z166,z9])],[(0,[z1,z2,z3,z4,z44,z5,z18]),(0,[z1,z2,z3,z4,z167,z5,z9])],[(0,[z1,z2,z3,z4,z5,z168,z9]),(0,[z1,z2,z135,z3,z4,z5,z18]),(0,[z52,z1,z2,z55,z3,z4,z5])],[(0,[z51,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z169,z9]),(1,[z1,z2,z3,z4,z5,z170]),(0,[z1,z2,z3,z4,z5,z18,z39])],[(0,[z67,z1,z2,z3,z4,z85,z9])]],
   [[(0,[z171,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z172,z3,z4,z5,z9]),(0,[z1,z2,z3,z173,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z174,z9]),(0,[z1,z2,z3,z4,z175,z5,z9]),(0,[z1,z2,z3,z4,z37,z68,z9]),(0,[z1,z2,z3,z4,z5,z176,z9]),(0,[z1,z2,z3,z4,z5,z9,z177])],[(0,[z105,z1,z2,z3,z4,z5,z18]),(0,[z25,z1,z2,z3,z4,z80,z9]),(0,[z52,z1,z2,z3,z4,z5,z178]),(0,[z1,z2,z3,z4,z179,z5,z9]),(0,[z1,z2,z180,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z181,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z182]),(0,[z1,z2,z3,z4,z4,z5,z6])],[(0,[z1,z2,z3,z183,z4,z5,z9]),(1,[z51,z2,z3,z4,z80,z9]),(0,[z1,z2,z53,z3,z4,z5,z18])],[(0,[z1,z88,z11,z3,z4,z5,z9]),(0,[z1,z2,z184,z3,z4,z5,z9]),(0,[z52,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z185,z3,z4,z5,z9])],[(1,[z186,z1,z2,z3,z4,z5]),(0,[z187,z105,z2,z3,z4,z5,z9]),(0,[z188,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z189])],[(0,[z1,z11,z3,z4,z5,z85,z9]),(1,[z52,z2,z3,z4,z5,z178]),(0,[z190,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z191]),(0,[z192,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z193])],[(0,[z1,z2,z3,z4,z5,z194,z9]),(0,[z1,z2,z3,z110,z4,z5,z6]),(0,[z195,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z196]),(0,[z1,z2,z3,z4,z5,z197,z9])],[(1,[z1,z198,z3,z4,z5,z9]),(0,[z1,z2,z3,z66,z4,z5,z9]),(0,[z1,z2,z199,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z85,z9,z39]),(0,[z1,z2,z3,z4,z5,z9,z200]),(0,[z1,z2,z98,z3,z4,z21,z9]),(0,[z1,z2,z3,z4,z5,z9,z193])]],
   [[(0,[z1,z2,z3,z4,z5,z201,z9]),(1,[z1,z2,z3,z4,z84,z9]),(0,[z1,z2,z3,z61,z4,z5,z64]),(1,[z1,z2,z202,z3,z5,z6])],[(0,[z1,z2,z203,z3,z4,z5,z9])],[(0,[z1,z2,z2,z3,z4,z5,z9]),(0,[z105,z1,z11,z3,z4,z5,z9]),(0,[z1,z2,z3,z204,z4,z5,z9]),(0,[z1,z2,z205,z3,z4,z5,z9]),(0,[z206,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z207]),(0,[z1,z2,z3,z4,z208,z5,z9]),(1,[z1,z126,z100,z4,z5,z9])],[(0,[z209,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z110,z4,z5,z210]),(1,[z1,z2,z211,z4,z5,z9]),(0,[z1,z212,z2,z3,z4,z5,z9]),(0,[z1,z126,z2,z100,z4,z5,z9])],[(0,[z87,z105,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z136,z9]),(0,[z1,z2,z3,z4,z91,z5,z85]),(0,[z1,z2,z213,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z214,z5,z9])],[(0,[z215,z1,z2,z3,z4,z5,z9]),(0,[z7,z1,z2,z90,z4,z5,z9]),(0,[z25,z1,z2,z3,z4,z216,z9]),(0,[z1,z2,z3,z4,z5,z217,z9]),(1,[z1,z2,z54,z44,z5,z9]),(0,[z1,z2,z3,z4,z5,z218,z18])],[(0,[z0,z105,z2,z3,z4,z5,z9]),(0,[z187,z2,z11,z3,z4,z5,z9]),(0,[z219,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z220,z3,z4,z5,z9]),(0,[z63,z87,z1,z2,z3,z4,z5]),(0,[z1,z3,z163,z4,z221,z5,z9])]],
   [[(0,[z222,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z223,z3,z4,z5,z9]),(0,[z1,z2,z16,z3,z4,z5,z6])],[(0,[z1,z2,z224,z3,z4,z5,z9]),(0,[z87,z1,z2,z3,z4,z5,z39]),(0,[z1,z2,z3,z4,z5,z225,z9]),(0,[z67,z1,z2,z3,z4,z5,z18]),(0,[z226,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z227,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z228,z9])],[],[(0,[z229,z1,z2,z3,z4,z5,z9]),(0,[z1,z230,z2,z3,z4,z5,z9]),(0,[z52,z1,z231,z3,z4,z5,z9]),(0,[z1,z2,z3,z163,z4,z5,z232]),(0,[z1,z2,z31,z3,z4,z37,z9]),(0,[z1,z2,z3,z4,z166,z5,z6]),(1,[z1,z2,z3,z4,z166,z21])],[(0,[z1,z2,z3,z101,z4,z5,z18]),(0,[z1,z2,z3,z4,z68,z5,z6]),(0,[z1,z233,z2,z3,z4,z5,z9])],[(0,[z234,z1,z2,z3,z4,z5,z9]),(0,[z235,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z236,z5,z9]),(0,[z1,z88,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z5,z9,z237]),(0,[z1,z2,z33,z4,z5,z9,z39])],[(0,[z1,z88,z2,z3,z4,z238,z9]),(0,[z1,z2,z3,z4,z5,z9,z239])],[(0,[z1,z65,z3,z4,z221,z5,z9]),(0,[z1,z2,z240,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z241,z9]),(0,[z1,z2,z3,z4,z5,z242,z9]),(0,[z1,z88,z2,z3,z4,z5,z29]),(0,[z1,z2,z61,z4,z44,z5,z9])]],
   [[(0,[z87,z2,z11,z3,z4,z5,z9]),(0,[z1,z88,z65,z3,z4,z5,z9]),(0,[z1,z2,z135,z3,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z152,z9]),(0,[z243,z1,z2,z3,z4,z5,z9]),(0,[z83,z1,z2,z3,z221,z5,z9]),(0,[z1,z2,z244,z3,z4,z5,z9])],[(1,[z1,z203,z3,z4,z5,z9]),(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z245,z3,z4,z5,z9]),(0,[z1,z246,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z247,z5,z9]),(1,[z1,z2,z3,z4,z5,z69]),(0,[z1,z2,z3,z35,z4,z37,z9]),(0,[z1,z2,z3,z4,z5,z9,z248])],[(1,[z1,z2,z3,z4,z5,z9]),(0,[z0,z2,z11,z3,z4,z5,z9]),(0,[z67,z1,z11,z3,z4,z5,z9]),(0,[z1,z2,z249,z3,z4,z5,z9]),(0,[z250,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z9,z251,z22]),(0,[z1,z2,z3,z4,z252,z5,z9])],[(0,[z1,z2,z3,z4,z5,z253,z9]),(0,[z1,z2,z254,z3,z4,z5,z9]),(0,[z1,z2,z16,z3,z4,z5,z255]),(1,[z1,z2,z4,z5,z9,z38])],[(0,[z105,z1,z2,z3,z4,z5,z6]),(0,[z187,z1,z2,z43,z4,z5,z9]),(0,[z1,z2,z16,z43,z4,z5,z9]),(0,[z1,z2,z256,z3,z4,z5,z9]),(0,[z1,z2,z113,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z257,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z258]),(0,[z1,z2,z259,z3,z4,z5,z9]),(0,[z1,z2,z3,z260,z4,z5,z9]),(0,[z1,z2,z3,z261,z4,z5,z9]),(0,[z1,z2,z3,z4,z262,z5,z9]),(0,[z1,z2,z3,z263,z4,z5,z9]),(0,[z1,z2,z3,z264,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z265,z9]),(0,[z83,z1,z103,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z266,z5,z9]),(0,[z1,z2,z53,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z267]),(0,[z1,z2,z3,z4,z268,z5,z9]),(0,[z52,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z269]),(0,[z1,z2,z3,z4,z37,z85,z9]),(1,[z1,z2,z3,z35,z37,z9])],[(0,[z105,z1,z65,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z270]),(0,[z1,z2,z54,z3,z4,z5,z9])]],
   [[(0,[z2,z135,z3,z43,z4,z5,z9]),(0,[z1,z2,z98,z3,z4,z85,z9]),(0,[z1,z88,z2,z3,z4,z166,z5]),(0,[z1,z2,z3,z4,z5,z271,z9])],[(0,[z1,z2,z272,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z273,z5,z9])],[(0,[z1,z2,z274,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z275,z9]),(0,[z1,z2,z276,z3,z4,z5,z9]),(0,[z1,z277,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z75,z5,z6]),(1,[z1,z2,z4,z278,z5,z9])],[(0,[z1,z2,z279,z3,z4,z5,z9]),(0,[z1,z65,z2,z3,z4,z5,z18]),(0,[z1,z88,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z18,z9])],[(0,[z1,z2,z3,z4,z5,z255,z9]),(0,[z1,z2,z202,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z9,z9]),(0,[z1,z2,z55,z3,z4,z5,z18]),(0,[z1,z2,z280,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z281,z5,z9]),(0,[z1,z2,z3,z4,z5,z85,z18])],[(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z282,z5,z9]),(0,[z1,z2,z211,z3,z4,z5,z9]),(0,[z1,z2,z283,z4,z5,z85,z9]),(0,[z1,z2,z3,z4,z284,z5,z9]),(0,[z63,z1,z2,z3,z4,z5,z18])]],
   [[(0,[z87,z1,z2,z211,z4,z5,z9]),(0,[z1,z285,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z286,z9]),(0,[z287,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z21,z6])],[(0,[z1,z2,z3,z4,z288,z5,z9]),(0,[z1,z2,z100,z3,z4,z5,z289]),(0,[z290,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z291,z3,z4,z5,z9]),(0,[z1,z2,z53,z4,z5,z17,z9])],[(0,[z1,z2,z3,z4,z292,z5,z9]),(0,[z1,z2,z3,z4,z5,z18,z293]),(0,[z1,z2,z294,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z295,z9]),(0,[z1,z2,z296,z3,z4,z5,z6]),(0,[z297,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z298,z5,z9]),(0,[z1,z103,z2,z3,z4,z5,z18]),(0,[z299,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z300,z4,z5,z9]),(0,[z301,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z302,z3,z4,z5,z9])],[(0,[z1,z2,z3,z303,z4,z5,z9]),(1,[z87,z2,z3,z4,z5,z293]),(0,[z1,z2,z3,z4,z5,z9,z293]),(1,[z304,z2,z3,z4,z5,z9]),(0,[z305,z1,z2,z3,z4,z5,z9]),(0,[z83,z1,z3,z4,z221,z5,z9]),(0,[z67,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z306]),(0,[z1,z2,z307,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z308,z9]),(0,[z187,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z309,z4,z5,z9]),(0,[z52,z1,z88,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z9,z310]),(0,[z1,z2,z311,z3,z4,z5,z9]),(0,[z1,z2,z3,z312,z4,z5,z9]),(0,[z1,z313,z2,z3,z4,z5,z9])],[(0,[z314,z1,z2,z3,z4,z5,z9]),(0,[z51,z2,z3,z4,z80,z5,z9]),(0,[z315,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z17,z18])],[(0,[z316,z1,z2,z3,z4,z5,z9]),(0,[z67,z1,z65,z3,z4,z5,z9]),(0,[z1,z2,z3,z43,z4,z5,z9]),(0,[z7,z1,z198,z3,z4,z5,z9]),(0,[z317,z1,z2,z4,z75,z5,z9]),(0,[z1,z2,z3,z101,z4,z5,z6]),(1,[z1,z2,z4,z318,z5,z9]),(0,[z1,z2,z98,z3,z4,z32,z9]),(0,[z1,z2,z3,z319,z4,z5,z9]),(0,[z1,z2,z3,z134,z4,z5,z9])]],
   [[(0,[z1,z2,z3,z320,z4,z5,z9]),(0,[z1,z2,z48,z43,z4,z5,z9]),(0,[z317,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z158]),(0,[z321,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z37,z5,z18]),(0,[z1,z2,z3,z322,z4,z5,z9]),(0,[z1,z2,z148,z3,z4,z5,z39])],[(0,[z1,z2,z3,z323,z4,z5,z9]),(0,[z1,z2,z324,z3,z43,z4,z5]),(0,[z325,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z100,z4,z44,z5,z9]),(0,[z1,z326,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z327,z9]),(0,[z1,z2,z328,z3,z4,z5,z6])],[(0,[z187,z2,z135,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z329]),(0,[z1,z330,z2,z3,z4,z5,z9]),(0,[z1,z88,z3,z4,z5,z9,z29]),(0,[z1,z2,z98,z4,z75,z5,z9]),(0,[z1,z2,z3,z4,z5,z18,z22]),(0,[z331,z1,z2,z3,z4,z5,z9])],[(1,[z7,z2,z3,z57,z5,z9]),(0,[z1,z2,z3,z4,z332,z5,z9]),(0,[z1,z2,z98,z3,z4,z5,z9]),(0,[z1,z2,z3,z35,z4,z5,z170])],[(0,[z1,z103,z11,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z333,z9]),(0,[z1,z2,z3,z4,z5,z178,z9]),(0,[z1,z2,z3,z4,z5,z334,z9]),(0,[z1,z2,z3,z4,z5,z335,z9]),(0,[z1,z2,z3,z4,z5,z9,z22]),(0,[z1,z2,z3,z4,z5,z22,z6])],[(0,[z1,z2,z336,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z32,z18])],[(0,[z1,z2,z3,z4,z5,z337,z9]),(0,[z87,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z338,z3,z4,z5,z9])],[(0,[z1,z2,z339,z3,z43,z4,z9]),(0,[z1,z2,z90,z3,z4,z5,z9]),(0,[z340,z1,z2,z3,z4,z5,z9]),(0,[z63,z1,z2,z3,z4,z5,z22]),(1,[z1,z2,z3,z4,z341,z9])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z9]),(0,[z105,z2,z3,z43,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z342,z9]),(0,[z1,z2,z343,z3,z4,z5,z9]),(0,[z1,z2,z344,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z345,z6]),(0,[z1,z2,z3,z4,z5,z6,z6])],[(0,[z83,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z127,z4,z5,z9]),(0,[z1,z2,z3,z163,z4,z5,z346]),(0,[z67,z1,z3,z4,z68,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z347])],[(0,[z25,z1,z203,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z348,z9]),(0,[z1,z285,z2,z3,z4,z68,z9]),(0,[z1,z2,z3,z4,z5,z15,z9]),(0,[z1,z2,z3,z4,z5,z349,z9])],[(0,[z350,z1,z2,z3,z4,z5,z9]),(0,[z7,z1,z2,z3,z57,z5,z9]),(0,[z25,z1,z2,z3,z4,z5,z9])],[(0,[z7,z1,z2,z3,z4,z5,z270]),(0,[z1,z2,z100,z3,z4,z5,z18]),(0,[z1,z2,z3,z351,z4,z5,z9])],[(0,[z105,z2,z3,z4,z5,z178,z9]),(0,[z87,z1,z2,z3,z4,z5,z293]),(0,[z1,z2,z352,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z85,z32,z9]),(0,[z353,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z354,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z355,z9]),(1,[z25,z2,z3,z4,z216,z9]),(0,[z356,z1,z2,z3,z4,z5,z9]),(0,[z1,z103,z2,z3,z163,z5,z9]),(0,[z1,z2,z357,z3,z4,z5,z9]),(0,[z1,z358,z2,z3,z4,z5,z9])],[(1,[z1,z2,z359,z3,z4,z5]),(0,[z1,z2,z360,z3,z4,z5,z9]),(0,[z7,z1,z2,z3,z110,z5,z9]),(0,[z1,z2,z361,z3,z4,z5,z9]),(0,[z52,z2,z3,z4,z5,z178,z9]),(0,[z1,z126,z100,z3,z4,z5,z9]),(0,[z1,z2,z362,z3,z4,z5,z9])]],
   [[(0,[z363,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z221,z5,z9]),(0,[z1,z2,z3,z364,z4,z5,z9]),(0,[z1,z2,z55,z3,z4,z5,z6]),(0,[z365,z1,z2,z3,z4,z5,z9])],[(0,[z70,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z85,z6]),(0,[z1,z2,z48,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z366,z6])],[(0,[z7,z1,z2,z3,z4,z5,z9]),(0,[z317,z304,z2,z3,z4,z5,z9]),(0,[z1,z88,z2,z148,z3,z4,z5]),(0,[z1,z2,z3,z4,z138,z5,z9])],[(0,[z209,z2,z3,z43,z4,z5,z9]),(0,[z367,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z368,z5,z9]),(0,[z1,z2,z54,z48,z4,z5,z9]),(0,[z1,z2,z48,z61,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z369])],[(1,[z0,z11,z3,z4,z5,z9]),(0,[z370,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z371]),(0,[z1,z2,z3,z4,z5,z216,z9]),(0,[z1,z2,z3,z4,z5,z9,z372]),(1,[z1,z2,z3,z4,z5,z114]),(0,[z373,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z98,z3,z4,z68,z9]),(0,[z1,z2,z3,z4,z5,z6,z374])],[(0,[z83,z1,z2,z276,z4,z5,z9]),(0,[z1,z103,z2,z3,z4,z5,z6]),(0,[z1,z2,z375,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z376,z9]),(0,[z1,z2,z3,z4,z5,z131,z9]),(0,[z317,z1,z2,z16,z4,z5,z9]),(0,[z377,z1,z2,z3,z4,z5,z9])]],
   [[(0,[z63,z246,z2,z3,z4,z5,z9]),(0,[z1,z2,z378,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z379,z5,z9]),(0,[z1,z2,z31,z3,z4,z5,z69]),(0,[z1,z2,z3,z4,z5,z194,z18]),(0,[z1,z2,z3,z4,z5,z380,z9])],[(0,[z1,z2,z381,z3,z4,z5,z9]),(0,[z382,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z17,z6]),(0,[z1,z2,z31,z3,z4,z5,z9])],[(0,[z1,z383,z2,z3,z4,z5,z9]),(0,[z384,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z385,z9]),(0,[z1,z2,z3,z4,z5,z386,z9]),(0,[z387,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z388,z5,z9]),(0,[z186,z1,z2,z3,z4,z5,z9]),(0,[z51,z1,z2,z113,z4,z5,z9]),(0,[z52,z1,z10,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z389]),(0,[z1,z2,z3,z4,z390,z5,z9]),(0,[z1,z2,z98,z3,z4,z218,z9]),(0,[z1,z2,z391,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z37,z5,z6]),(0,[z392,z1,z2,z3,z4,z5,z9])],[(0,[z1,z65,z3,z4,z5,z12,z9]),(0,[z1,z2,z3,z4,z393,z5,z9]),(0,[z1,z2,z3,z4,z5,z394,z9]),(0,[z51,z1,z2,z3,z4,z216,z9]),(0,[z395,z1,z2,z3,z4,z5,z6])],[(0,[z1,z396,z2,z3,z4,z5,z9]),(1,[z1,z88,z3,z4,z5,z29]),(0,[z1,z2,z4,z5,z17,z9,z22]),(0,[z1,z2,z397,z3,z4,z5,z9]),(0,[z398,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z399,z5,z9]),(0,[z67,z1,z285,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z166,z5,z39])],[(0,[z1,z2,z400,z3,z4,z5,z9]),(0,[z1,z2,z401,z3,z4,z5,z9]),(0,[z1,z2,z402,z3,z4,z5,z9])]],
   [[(0,[z1,z403,z2,z3,z4,z5,z9]),(0,[z187,z1,z2,z135,z4,z5,z9]),(0,[z1,z2,z16,z135,z4,z5,z9]),(0,[z1,z2,z404,z3,z4,z5,z9]),(0,[z405,z1,z2,z3,z4,z5,z9]),(0,[z63,z1,z3,z4,z5,z12,z9]),(0,[z1,z2,z3,z4,z406,z5,z9]),(0,[z1,z2,z3,z4,z5,z407,z9]),(0,[z1,z2,z3,z4,z5,z9,z408]),(0,[z1,z2,z3,z4,z5,z32,z6])],[(1,[z105,z65,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z409,z9]),(0,[z1,z2,z410,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z411,z9]),(0,[z412,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z413,z9]),(0,[z1,z2,z3,z4,z5,z36,z9]),(0,[z1,z2,z202,z3,z134,z5,z9])],[(0,[z1,z2,z3,z414,z4,z5,z9]),(0,[z1,z2,z3,z4,z415,z5,z9]),(0,[z416,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z417,z5,z9]),(0,[z1,z2,z418,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z251])],[(0,[z8,z2,z11,z3,z4,z5,z9]),(0,[z1,z2,z419,z3,z4,z5,z9]),(0,[z1,z2,z420,z3,z4,z5,z9])],[(0,[z105,z8,z2,z3,z4,z5,z9]),(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z421,z5,z9]),(1,[z317,z1,z101,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z150]),(0,[z1,z2,z148,z3,z4,z5,z9])],[],[(0,[z1,z2,z43,z4,z5,z9,z22]),(1,[z1,z2,z3,z4,z5,z270]),(0,[z1,z2,z100,z3,z4,z5,z6]),(0,[z1,z422,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z423])]],
   [[(0,[z1,z2,z3,z4,z411,z5,z9]),(0,[z83,z1,z2,z3,z4,z5,z372]),(0,[z1,z2,z3,z163,z4,z5,z6]),(0,[z1,z285,z2,z3,z4,z85,z9]),(0,[z1,z2,z3,z61,z4,z5,z158]),(0,[z424,z1,z2,z3,z4,z5,z9])],[(0,[z425,z1,z2,z3,z4,z5,z9]),(0,[z52,z1,z2,z3,z4,z5,z39]),(0,[z1,z2,z3,z4,z426,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z427])],[(0,[z1,z2,z3,z4,z44,z5,z6]),(0,[z1,z2,z244,z3,z4,z5,z18])],[(0,[z428,z1,z2,z3,z4,z5,z9]),(1,[z187,z2,z135,z4,z5,z9]),(0,[z1,z2,z429,z3,z4,z5,z9]),(0,[z1,z2,z430,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z232,z9]),(0,[z1,z2,z431,z3,z4,z5,z9]),(0,[z1,z2,z3,z37,z5,z32,z9]),(1,[z1,z2,z3,z4,z5,z18]),(0,[z1,z432,z2,z3,z4,z5,z9])],[(0,[z25,z51,z2,z3,z4,z5,z9])],[(1,[z209,z2,z43,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z433,z9]),(0,[z1,z2,z101,z4,z44,z5,z9]),(0,[z1,z2,z434,z3,z4,z5,z9]),(0,[z1,z435,z2,z3,z4,z5,z9])],[(0,[z65,z2,z11,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z136,z5,z9]),(0,[z1,z3,z4,z68,z5,z85,z9]),(0,[z1,z2,z3,z61,z4,z341,z9]),(0,[z1,z2,z3,z4,z436,z5,z9])]],
   [[(0,[z1,z2,z256,z3,z43,z4,z5]),(0,[z2,z3,z110,z4,z57,z5,z9]),(0,[z1,z2,z437,z3,z4,z5,z9]),(0,[z1,z2,z98,z3,z4,z75,z9])],[(0,[z438,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z4,z5,z9]),(0,[z1,z2,z54,z3,z4,z5,z18])],[(0,[z1,z2,z3,z4,z439,z5,z9])],[(0,[z105,z2,z3,z4,z57,z5,z9]),(0,[z1,z2,z440,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z18,z178]),(0,[z83,z1,z2,z3,z4,z5,z114]),(0,[z1,z2,z3,z4,z5,z9,z346]),(0,[z441,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z442,z4,z5,z9]),(1,[z1,z2,z33,z4,z5,z9])],[(0,[z1,z2,z48,z135,z4,z5,z9]),(0,[z1,z2,z3,z443,z4,z5,z9]),(0,[z83,z1,z2,z3,z4,z58,z9]),(1,[z1,z2,z3,z4,z5,z36])],[(0,[z1,z2,z3,z4,z5,z9,z444]),(0,[z1,z2,z3,z445,z4,z5,z9]),(1,[z1,z2,z53,z4,z5,z17]),(0,[z1,z2,z3,z4,z5,z18,z18])],[(0,[z1,z2,z3,z4,z446,z5,z9]),(0,[z1,z2,z3,z4,z5,z447,z9]),(0,[z1,z2,z3,z4,z448,z5,z9]),(0,[z1,z2,z3,z4,z91,z5,z9]),(0,[z1,z2,z449,z3,z4,z5,z9]),(0,[z1,z450,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z451,z5,z9]),(0,[z1,z452,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z453,z5,z9]),(0,[z1,z2,z280,z3,z4,z5,z18])]],
   [[(0,[z1,z2,z3,z4,z5,z289,z9])],[(0,[z1,z2,z454,z3,z4,z5,z9])],[(0,[z1,z2,z3,z110,z4,z5,z267]),(0,[z1,z2,z3,z4,z455,z5,z9]),(1,[z1,z2,z276,z4,z5,z9]),(0,[z1,z285,z2,z3,z4,z5,z18]),(0,[z1,z2,z456,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z80,z5,z9]),(0,[z1,z2,z3,z457,z4,z5,z9]),(0,[z1,z2,z458,z3,z4,z5,z9])],[(0,[z1,z2,z53,z43,z4,z5,z9]),(0,[z1,z2,z135,z4,z5,z9,z22]),(0,[z63,z52,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z218,z6]),(0,[z1,z2,z3,z4,z459,z5,z6])],[],[(0,[z460,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z461,z4,z5,z9]),(0,[z1,z2,z462,z3,z4,z5,z9])],[(0,[z1,z463,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z464,z9]),(0,[z465,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z466]),(0,[z63,z1,z2,z148,z3,z4,z5])]],
   [[(0,[z467,z1,z2,z3,z4,z5,z9]),(0,[z1,z88,z2,z3,z4,z5,z17]),(0,[z1,z2,z16,z3,z4,z5,z9])],[(0,[z1,z2,z3,z43,z4,z5,z18]),(0,[z468,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z469,z3,z4,z5,z9]),(0,[z87,z1,z2,z55,z3,z4,z5]),(0,[z317,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z470,z3,z4,z5,z9])],[(1,[z1,z440,z3,z4,z5,z9]),(0,[z1,z471,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z39]),(0,[z1,z326,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z166,z5,z9]),(0,[z1,z2,z3,z4,z5,z472,z9])],[(0,[z1,z2,z3,z473,z4,z5,z9]),(0,[z1,z2,z3,z4,z474,z5,z9]),(0,[z475,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z68,z5,z9]),(0,[z1,z2,z476,z3,z4,z5,z9]),(0,[z1,z2,z3,z477,z4,z5,z9])],[(1,[z1,z2,z3,z4,z5,z232]),(0,[z1,z2,z3,z4,z5,z12,z9]),(0,[z1,z2,z98,z3,z4,z5,z18])],[(0,[z209,z1,z2,z43,z4,z5,z9]),(0,[z478,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z283,z4,z5,z9]),(0,[z63,z1,z88,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z479,z5,z9]),(0,[z1,z2,z480,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z481,z5,z9])]],
   [[(1,[z1,z2,z3,z4,z5,z464]),(0,[z87,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z482,z4,z5,z9]),(0,[z1,z2,z483,z3,z4,z5,z9]),(0,[z1,z2,z484,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z191])],[(0,[z485,z1,z2,z3,z4,z5,z9]),(0,[z1,z486,z2,z3,z4,z5,z9])],[(0,[z0,z1,z2,z3,z4,z5,z18]),(0,[z487,z1,z2,z3,z4,z5,z9]),(0,[z1,z198,z2,z3,z4,z5,z9]),(0,[z2,z3,z4,z5,z178,z9,z293]),(0,[z488,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z489,z5,z9]),(0,[z1,z490,z2,z3,z4,z5,z9]),(0,[z1,z2,z491,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z492,z5,z9]),(0,[z1,z2,z493,z3,z4,z5,z9]),(1,[z1,z2,z148,z3,z4,z39])],[(0,[z494,z1,z2,z3,z4,z5,z9]),(0,[z83,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z35,z4,z278,z5,z9])],[(0,[z1,z2,z3,z4,z495,z5,z9]),(1,[z1,z2,z3,z4,z5,z372]),(0,[z1,z2,z3,z4,z5,z496,z9]),(1,[z1,z2,z3,z5,z18,z6])],[(0,[z497,z1,z2,z3,z4,z5,z9]),(0,[z25,z1,z2,z3,z4,z5,z18]),(1,[z246,z2,z3,z4,z5,z9]),(0,[z1,z2,z498,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z37,z216,z9]),(0,[z1,z2,z3,z4,z5,z499,z9]),(0,[z500,z1,z2,z3,z4,z5,z9]),(0,[z501,z1,z2,z3,z4,z5,z9])],[(0,[z502,z1,z2,z3,z4,z5,z9]),(0,[z317,z1,z2,z101,z4,z5,z9]),(0,[z1,z2,z503,z3,z4,z5,z9])]],
   [[(0,[z1,z2,z3,z4,z5,z504,z9]),(0,[z7,z1,z2,z3,z4,z5,z409]),(0,[z1,z2,z3,z4,z5,z18,z6])],[(0,[z1,z65,z2,z3,z4,z5,z6]),(0,[z1,z2,z505,z3,z4,z5,z9]),(0,[z506,z1,z2,z3,z4,z5,z9])],[(0,[z51,z1,z2,z3,z4,z80,z9]),(0,[z1,z2,z3,z4,z221,z5,z18]),(0,[z1,z2,z4,z318,z5,z85,z9]),(0,[z1,z2,z16,z3,z4,z68,z9]),(0,[z1,z2,z3,z4,z5,z18,z29]),(0,[z1,z2,z3,z4,z75,z5,z9]),(0,[z1,z2,z3,z4,z5,z507,z9]),(0,[z1,z2,z148,z98,z3,z4,z9]),(0,[z1,z2,z3,z4,z5,z9,z6])],[(0,[z0,z1,z11,z3,z4,z5,z9]),(0,[z1,z2,z508,z3,z4,z5,z9]),(0,[z509,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z510,z9]),(0,[z1,z88,z2,z3,z4,z286,z9]),(0,[z1,z2,z48,z4,z75,z5,z9]),(0,[z1,z2,z48,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z21,z17]),(0,[z1,z2,z31,z3,z35,z5,z9]),(0,[z1,z2,z3,z4,z5,z511,z9]),(0,[z70,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z512,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z513]),(0,[z7,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z9,z514]),(0,[z1,z2,z3,z4,z5,z9,z29]),(0,[z1,z2,z3,z515,z4,z5,z9]),(0,[z1,z516,z2,z3,z4,z5,z9]),(0,[z1,z2,z31,z3,z4,z5,z150]),(0,[z1,z2,z202,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z38])],[(0,[z2,z3,z4,z80,z5,z216,z9]),(0,[z1,z285,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z166,z68,z9]),(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z61,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z517,z9])],[(0,[z1,z2,z3,z4,z5,z216,z18]),(0,[z1,z2,z3,z4,z80,z5,z464]),(0,[z1,z126,z2,z3,z4,z411,z9])],[(0,[z1,z2,z518,z3,z4,z5,z9]),(0,[z1,z2,z519,z3,z4,z5,z9]),(0,[z63,z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z16,z3,z4,z21,z9]),(1,[z1,z2,z31,z3,z32,z9]),(0,[z520,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z521,z9])]],
   [[(0,[z1,z2,z522,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z210]),(1,[z1,z2,z3,z4,z58,z9]),(0,[z1,z2,z16,z3,z4,z218,z9]),(0,[z1,z523,z2,z3,z4,z5,z9]),(0,[z1,z2,z31,z3,z4,z32,z9]),(0,[z1,z2,z442,z35,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z21,z9])],[(0,[z1,z2,z524,z3,z4,z5,z9]),(0,[z52,z87,z2,z3,z4,z5,z9]),(0,[z87,z1,z2,z3,z4,z5,z21]),(0,[z1,z2,z525,z3,z4,z5,z9]),(0,[z526,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z527]),(0,[z1,z2,z3,z4,z5,z528,z9]),(0,[z1,z2,z3,z4,z529,z5,z9])],[(0,[z1,z530,z2,z3,z4,z5,z9]),(1,[z1,z2,z142,z4,z5,z9]),(0,[z1,z122,z2,z3,z4,z5,z9]),(1,[z153,z2,z3,z4,z5,z9]),(0,[z1,z2,z531,z3,z4,z5,z9]),(0,[z1,z2,z3,z532,z4,z5,z9]),(0,[z1,z2,z3,z4,z166,z21,z9])],[(0,[z1,z2,z3,z4,z5,z9,z533]),(0,[z1,z2,z3,z4,z5,z9,z534]),(0,[z1,z2,z3,z4,z535,z5,z9]),(0,[z1,z2,z536,z3,z4,z5,z9]),(0,[z1,z2,z537,z3,z4,z5,z9]),(0,[z1,z2,z31,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z278,z5,z9]),(0,[z1,z2,z538,z3,z4,z5,z9])],[(1,[z1,z2,z3,z4,z5,z289]),(0,[z1,z2,z3,z4,z539,z5,z9]),(1,[z1,z2,z16,z4,z218,z9]),(0,[z384,z1,z2,z3,z4,z5,z18])],[(0,[z1,z2,z540,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z84,z5,z9])],[(0,[z186,z1,z2,z11,z3,z4,z5]),(0,[z1,z2,z541,z3,z4,z5,z9]),(0,[z83,z1,z2,z3,z163,z5,z9]),(0,[z1,z2,z3,z542,z4,z5,z9]),(1,[z63,z1,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z18,z12]),(0,[z1,z2,z3,z4,z5,z341,z9])],[(0,[z1,z2,z3,z4,z5,z9,z374]),(0,[z1,z2,z543,z3,z4,z5,z9])]],
   [[(0,[z1,z2,z48,z101,z4,z5,z9]),(0,[z1,z2,z3,z4,z544,z5,z9]),(0,[z63,z1,z2,z3,z4,z166,z5]),(0,[z1,z2,z98,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z545,z5,z9]),(0,[z1,z126,z2,z4,z75,z5,z9]),(1,[z1,z2,z3,z4,z5,z427]),(0,[z1,z2,z328,z3,z4,z5,z9])],[(1,[z1,z2,z133,z4,z5,z9]),(0,[z1,z2,z546,z3,z4,z5,z9]),(0,[z1,z126,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z547,z9]),(0,[z1,z2,z16,z98,z4,z5,z9]),(0,[z1,z2,z3,z35,z4,z5,z9]),(0,[z1,z2,z3,z4,z548,z5,z9])],[(0,[z1,z2,z224,z3,z43,z4,z9]),(0,[z1,z2,z3,z4,z5,z549,z9]),(0,[z63,z1,z2,z3,z4,z5,z12])],[(0,[z2,z11,z3,z43,z4,z5,z9]),(0,[z1,z2,z3,z4,z550,z5,z9]),(0,[z1,z2,z359,z11,z3,z4,z5]),(0,[z1,z2,z359,z3,z4,z5,z9]),(0,[z1,z2,z3,z551,z4,z5,z9]),(0,[z1,z2,z3,z4,z552,z5,z9]),(0,[z1,z2,z3,z4,z5,z553,z9]),(0,[z1,z2,z16,z48,z4,z5,z9]),(0,[z1,z2,z55,z4,z5,z9,z22]),(0,[z1,z2,z3,z4,z5,z554,z9]),(0,[z1,z2,z3,z4,z5,z248,z6])],[(0,[z1,z555,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z556,z5,z9]),(0,[z1,z139,z2,z3,z4,z5,z9])],[(0,[z87,z1,z2,z53,z3,z4,z5]),(0,[z1,z2,z3,z557,z4,z5,z9]),(0,[z558,z1,z2,z3,z4,z5,z9]),(0,[z83,z1,z2,z3,z4,z5,z6]),(1,[z1,z103,z3,z163,z5,z9]),(0,[z559,z1,z2,z3,z4,z5,z9])],[(0,[z1,z103,z3,z163,z4,z5,z9]),(0,[z1,z2,z560,z3,z4,z5,z9]),(0,[z1,z2,z148,z3,z4,z5,z18])]],
   [[(0,[z0,z1,z65,z3,z4,z5,z9]),(0,[z1,z2,z11,z3,z4,z5,z9]),(0,[z1,z2,z561,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z318,z5,z9]),(0,[z1,z2,z3,z562,z4,z5,z9]),(1,[z1,z2,z55,z4,z5,z22]),(0,[z1,z2,z3,z4,z5,z563,z9])],[(0,[z2,z11,z3,z4,z5,z178,z9]),(0,[z1,z2,z564,z3,z4,z5,z9]),(0,[z1,z2,z54,z4,z44,z5,z9]),(0,[z1,z2,z565,z3,z4,z5,z9])],[(0,[z1,z2,z566,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z18,z567])],[(0,[z7,z1,z440,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z409]),(0,[z1,z2,z3,z4,z568,z5,z9]),(1,[z1,z2,z3,z4,z5,z346])],[(0,[z1,z2,z3,z4,z238,z5,z9]),(0,[z1,z2,z16,z55,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z569,z9]),(0,[z1,z2,z3,z4,z57,z5,z9]),(0,[z1,z2,z3,z4,z221,z5,z6]),(0,[z1,z2,z16,z3,z4,z75,z9])],[(0,[z1,z2,z3,z4,z5,z9,z81]),(0,[z1,z2,z3,z4,z5,z293,z6]),(0,[z1,z126,z2,z101,z4,z5,z9]),(0,[z570,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z231,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z571,z6])]],
   [[(0,[z1,z2,z53,z135,z4,z5,z9]),(0,[z25,z1,z2,z16,z3,z4,z9]),(1,[z1,z2,z3,z4,z152,z9]),(0,[z1,z2,z16,z3,z4,z85,z9]),(0,[z1,z2,z3,z4,z572,z5,z9]),(0,[z76,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z216,z6]),(0,[z1,z2,z108,z3,z4,z5,z85]),(0,[z1,z573,z2,z3,z4,z5,z9]),(0,[z574,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z423]),(0,[z1,z2,z148,z3,z4,z9,z39])],[(0,[z1,z2,z3,z575,z4,z5,z9]),(0,[z1,z2,z576,z3,z4,z5,z9]),(0,[z1,z2,z3,z577,z4,z5,z9]),(0,[z1,z2,z4,z75,z5,z17,z9])],[(0,[z1,z2,z3,z4,z5,z578,z9]),(0,[z1,z2,z100,z3,z4,z5,z534]),(0,[z1,z2,z3,z4,z166,z85,z9]),(0,[z1,z2,z3,z4,z4,z5,z18])],[(0,[z1,z11,z3,z4,z221,z5,z9]),(0,[z1,z579,z2,z3,z4,z5,z9]),(0,[z1,z2,z580,z3,z4,z5,z9]),(0,[z1,z2,z3,z581,z4,z5,z9]),(0,[z1,z2,z16,z3,z4,z5,z427])],[(0,[z1,z2,z3,z4,z5,z9,z582]),(0,[z1,z2,z43,z4,z75,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z583]),(0,[z1,z2,z202,z3,z5,z9,z6])],[(0,[z584,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z216,z32,z9]),(0,[z87,z1,z2,z142,z4,z5,z9])],[(0,[z585,z1,z2,z3,z4,z5,z9]),(0,[z317,z1,z126,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z586,z5,z9]),(0,[z1,z2,z16,z4,z44,z5,z9])]],
   [[(0,[z8,z2,z3,z110,z4,z5,z9]),(0,[z192,z1,z2,z3,z4,z5,z9]),(0,[z587,z1,z2,z3,z4,z5,z9]),(0,[z392,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z148,z3,z4,z5,z21])],[(0,[z1,z2,z3,z110,z4,z5,z9]),(0,[z1,z126,z2,z16,z4,z5,z9]),(0,[z83,z153,z2,z3,z4,z5,z9])],[(0,[z209,z1,z2,z135,z4,z5,z9]),(0,[z1,z2,z324,z3,z4,z5,z9]),(0,[z588,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z80,z32,z9]),(0,[z317,z1,z2,z100,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z589,z9]),(0,[z1,z2,z3,z4,z5,z9,z590]),(0,[z1,z591,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z592,z4,z5,z9])],[(0,[z1,z2,z3,z593,z4,z5,z9]),(0,[z25,z1,z2,z98,z3,z4,z9]),(0,[z1,z2,z3,z594,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z595]),(0,[z395,z1,z2,z3,z4,z5,z9]),(0,[z87,z2,z3,z4,z5,z9,z293]),(0,[z1,z2,z3,z4,z5,z124,z9]),(1,[z1,z2,z98,z4,z75,z9])],[(0,[z1,z2,z3,z596,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z597,z9]),(1,[z8,z2,z3,z110,z5,z9]),(0,[z1,z2,z3,z4,z80,z5,z18]),(0,[z1,z2,z3,z4,z598,z5,z9]),(0,[z130,z1,z2,z3,z4,z5,z9])],[(0,[z599,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z600,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z601,z9]),(0,[z602,z1,z2,z3,z4,z5,z9])],[(1,[z1,z231,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z93]),(0,[z1,z2,z16,z3,z4,z32,z9])]],
   [[(0,[z603,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z604,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z605,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z571])],[(0,[z1,z2,z3,z4,z5,z606,z9])],[(0,[z187,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z607,z4,z5,z9]),(0,[z8,z1,z2,z3,z110,z5,z9]),(0,[z1,z2,z16,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z22,z39])],[(0,[z1,z2,z3,z4,z608,z5,z9]),(0,[z609,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z339,z3,z4,z9]),(0,[z1,z610,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z68,z32,z9]),(0,[z63,z60,z2,z3,z4,z5,z9])],[(0,[z1,z611,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z267,z9]),(0,[z1,z2,z3,z4,z5,z5,z9]),(0,[z1,z2,z3,z4,z37,z80,z9]),(1,[z305,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z612,z5,z9]),(0,[z613,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z134,z4,z5,z18])],[(0,[z1,z2,z339,z3,z4,z5,z9]),(0,[z8,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z614,z3,z4,z5,z9]),(0,[z615,z1,z2,z3,z4,z5,z9]),(0,[z317,z1,z3,z101,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z616,z9]),(0,[z1,z2,z3,z4,z5,z156,z9]),(0,[z1,z2,z3,z4,z5,z18,z617]),(0,[z1,z2,z3,z4,z166,z5,z18])],[(0,[z1,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z618,z9]),(1,[z1,z2,z256,z3,z4,z5]),(1,[z1,z463,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z619]),(0,[z1,z2,z3,z4,z68,z5,z18])],[(0,[z620,z1,z2,z3,z4,z5,z9]),(0,[z621,z1,z2,z3,z4,z5,z9]),(0,[z622,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z623,z4,z5,z9]),(0,[z1,z2,z624,z3,z4,z5,z9]),(0,[z625,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z626,z9]),(0,[z1,z2,z3,z4,z5,z9,z617])]],
   [[(0,[z1,z2,z3,z163,z4,z5,z9]),(0,[z1,z88,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z627,z4,z5,z9]),(0,[z87,z1,z2,z3,z4,z5,z178]),(0,[z628,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z629,z9]),(0,[z1,z2,z16,z4,z5,z218,z9]),(1,[z1,z2,z3,z4,z9,z251]),(0,[z1,z2,z3,z630,z4,z5,z9])],[(0,[z1,z2,z135,z4,z75,z5,z9]),(0,[z631,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z44,z5,z9]),(0,[z1,z2,z98,z3,z4,z37,z9]),(0,[z1,z2,z632,z3,z4,z5,z9]),(0,[z1,z2,z3,z633,z4,z5,z9]),(0,[z1,z2,z3,z634,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z6])],[(0,[z1,z65,z3,z4,z5,z85,z9]),(0,[z1,z2,z135,z3,z4,z5,z9]),(0,[z1,z2,z48,z100,z4,z5,z9]),(0,[z1,z2,z635,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z238,z9]),(0,[z1,z2,z54,z3,z44,z5,z9]),(0,[z1,z2,z53,z3,z4,z5,z17])],[(0,[z1,z2,z3,z4,z5,z636,z9]),(0,[z51,z1,z2,z3,z4,z5,z9]),(0,[z637,z1,z2,z3,z4,z5,z9]),(0,[z638,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z397,z3,z4,z9]),(0,[z1,z2,z442,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z639,z9]),(0,[z1,z2,z3,z4,z5,z6,z200]),(0,[z1,z2,z3,z4,z5,z9,z39])],[(0,[z1,z2,z3,z640,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z641,z9]),(0,[z1,z2,z642,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z643])],[(0,[z105,z1,z2,z3,z4,z5,z9]),(0,[z2,z11,z3,z4,z57,z5,z9]),(1,[z1,z2,z224,z3,z4,z9]),(0,[z1,z644,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z645,z4,z5,z9]),(0,[z646,z1,z2,z3,z4,z5,z9]),(0,[z1,z285,z3,z4,z5,z85,z9]),(0,[z1,z2,z54,z3,z4,z5,z6])]],
   [[(0,[z647,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z648,z5,z9]),(1,[z1,z2,z3,z4,z5,z210]),(0,[z1,z2,z3,z4,z649,z5,z9]),(0,[z1,z2,z3,z4,z5,z650,z9]),(0,[z1,z2,z3,z4,z68,z9,z39]),(0,[z1,z2,z54,z3,z61,z5,z9]),(0,[z1,z2,z651,z3,z4,z5,z9]),(0,[z1,z2,z53,z3,z4,z5,z9]),(0,[z1,z2,z3,z652,z4,z5,z9])],[(0,[z1,z653,z2,z3,z4,z5,z9]),(0,[z52,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z654,z5,z9]),(0,[z1,z2,z3,z4,z5,z286,z9])],[(0,[z1,z2,z3,z655,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z534])],[(0,[z1,z2,z3,z4,z5,z656,z9]),(0,[z1,z2,z3,z4,z75,z5,z18])],[(0,[z1,z65,z103,z3,z4,z5,z9]),(0,[z187,z209,z2,z3,z4,z5,z9]),(0,[z1,z2,z657,z3,z4,z5,z9]),(0,[z658,z1,z2,z3,z4,z5,z9]),(1,[z67,z1,z3,z4,z68,z9]),(1,[z1,z2,z3,z4,z5,z255]),(0,[z1,z2,z4,z75,z5,z218,z9])],[(1,[z1,z2,z324,z3,z4,z5]),(0,[z7,z1,z2,z66,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z659,z9]),(0,[z1,z2,z660,z3,z4,z5,z9]),(0,[z1,z2,z283,z3,z4,z5,z9]),(0,[z661,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z170]),(0,[z1,z662,z2,z3,z4,z5,z9]),(0,[z1,z2,z202,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z166,z5,z21])],[(0,[z663,z1,z2,z3,z4,z5,z9]),(0,[z1,z88,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z61,z4,z5,z18]),(0,[z1,z2,z664,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z17,z39])]],
   [[(0,[z1,z2,z3,z4,z80,z5,z6]),(0,[z52,z1,z2,z3,z4,z5,z293]),(0,[z1,z304,z2,z3,z4,z5,z9]),(0,[z1,z103,z2,z3,z221,z5,z9]),(0,[z1,z2,z3,z4,z5,z665,z9]),(0,[z1,z2,z666,z3,z4,z5,z9]),(0,[z1,z2,z667,z3,z4,z5,z9]),(0,[z1,z2,z3,z668,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z345])],[(0,[z669,z1,z2,z3,z4,z5,z9]),(0,[z25,z2,z3,z4,z5,z216,z9]),(1,[z1,z285,z3,z4,z85,z9]),(0,[z1,z2,z4,z44,z75,z5,z9]),(0,[z670,z1,z2,z3,z4,z5,z9])],[(0,[z209,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z671]),(0,[z317,z305,z2,z3,z4,z5,z9]),(0,[z83,z122,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z138,z9]),(0,[z1,z2,z3,z4,z5,z567,z9]),(0,[z1,z2,z3,z4,z5,z21,z18])],[(0,[z672,z1,z2,z3,z4,z5,z9]),(0,[z1,z673,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z64,z9])],[(0,[z1,z2,z3,z674,z4,z5,z9]),(0,[z675,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z676,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z218,z9]),(0,[z1,z2,z677,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z459,z5,z9]),(0,[z1,z678,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z679]),(0,[z187,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z397,z3,z4,z9,z22]),(0,[z1,z2,z296,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z680,z5,z9]),(0,[z1,z2,z536,z3,z4,z5,z18])],[(0,[z1,z2,z3,z4,z5,z681,z9]),(0,[z1,z2,z3,z4,z5,z9,z682]),(0,[z1,z2,z3,z4,z5,z9,z366]),(0,[z1,z2,z3,z683,z4,z5,z9])],[(0,[z1,z684,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z43,z4,z5,z6]),(0,[z685,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z686,z4,z5,z9]),(0,[z1,z2,z687,z3,z4,z5,z9]),(0,[z1,z2,z3,z688,z4,z5,z9]),(0,[z67,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z53,z3,z4,z5,z22]),(0,[z1,z2,z3,z134,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z689,z5,z9]),(0,[z317,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z127,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z112,z9])],[(0,[z1,z2,z3,z4,z690,z5,z9]),(0,[z52,z1,z2,z3,z4,z5,z21]),(1,[z83,z1,z3,z221,z5,z9]),(0,[z1,z2,z3,z4,z691,z5,z9]),(0,[z1,z2,z3,z692,z4,z5,z9]),(0,[z1,z2,z3,z35,z4,z32,z9])],[(0,[z1,z2,z3,z101,z4,z5,z9])],[(0,[z1,z2,z693,z3,z4,z5,z9]),(0,[z694,z1,z2,z3,z4,z5,z9]),(0,[z695,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z696,z5,z9]),(0,[z1,z2,z3,z4,z5,z178,z6]),(0,[z1,z126,z2,z3,z4,z5,z18]),(0,[z1,z697,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z35,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z547,z18]),(0,[z1,z2,z3,z4,z548,z5,z18])],[(0,[z1,z2,z3,z4,z5,z9,z698]),(0,[z7,z1,z2,z3,z4,z131,z9]),(0,[z1,z2,z3,z4,z699,z5,z9]),(0,[z1,z2,z3,z4,z700,z5,z9]),(0,[z1,z2,z3,z4,z701,z5,z9])],[(1,[z1,z2,z3,z4,z5,z81]),(0,[z87,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z702,z9]),(0,[z1,z2,z3,z4,z5,z703,z9]),(0,[z1,z2,z480,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z704,z9])],[(0,[z25,z1,z463,z3,z4,z5,z9]),(0,[z1,z2,z705,z3,z4,z5,z9]),(0,[z1,z2,z3,z706,z4,z5,z9])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z440,z3,z4,z5,z409]),(0,[z1,z2,z3,z4,z5,z707]),(0,[z1,z708,z3,z4,z5,z9]),(0,[z1,z2,z709,z4,z5,z6]),(0,[z1,z2,z3,z4,z9,z710])],[(0,[z1,z711,z3,z4,z5,z9]),(0,[z317,z1,z101,z4,z5,z6]),(0,[z1,z2,z712,z4,z5,z9]),(0,[z67,z1,z3,z4,z713,z9]),(0,[z1,z2,z714,z4,z5,z9]),(0,[z1,z2,z3,z5,z6,z369])],[(0,[z1,z2,z339,z3,z4,z9]),(0,[z1,z2,z339,z4,z44,z9]),(0,[z305,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z715])],[(0,[z1,z2,z716,z4,z5,z9]),(0,[z1,z2,z717,z3,z4,z5]),(0,[z2,z3,z4,z5,z718,z9]),(0,[z153,z2,z3,z4,z5,z114]),(0,[z1,z2,z3,z4,z166,z248]),(0,[z384,z2,z3,z4,z5,z112])],[(0,[z1,z463,z3,z4,z5,z18]),(0,[z153,z2,z3,z4,z58,z9]),(0,[z2,z3,z4,z5,z719,z9]),(0,[z1,z2,z4,z91,z318,z5]),(0,[z1,z2,z4,z75,z9,z408]),(0,[z1,z2,z720,z4,z5,z9])],[(0,[z87,z88,z11,z3,z4,z5]),(0,[z1,z721,z3,z4,z5,z9]),(0,[z1,z2,z3,z572,z5,z6]),(0,[z1,z2,z3,z577,z5,z18])],[(0,[z1,z198,z3,z4,z136,z9]),(0,[z7,z2,z66,z57,z5,z9]),(0,[z1,z2,z3,z4,z5,z722]),(0,[z331,z2,z3,z4,z80,z9]),(0,[z1,z2,z16,z4,z152,z9]),(0,[z723,z2,z3,z4,z5,z9]),(0,[z1,z2,z4,z5,z17,z427]),(0,[z1,z2,z3,z4,z18,z251])],[(0,[z1,z2,z3,z4,z5,z724]),(0,[z187,z2,z135,z4,z5,z6]),(0,[z83,z1,z3,z221,z5,z114]),(0,[z1,z2,z283,z4,z5,z18])]],
   [[(0,[z1,z2,z725,z4,z5,z9]),(0,[z726,z2,z3,z4,z5,z9]),(0,[z727,z2,z3,z4,z5,z9]),(0,[z83,z1,z3,z221,z58,z9]),(0,[z728,z2,z3,z4,z5,z9]),(0,[z1,z2,z48,z61,z341,z9]),(0,[z1,z2,z16,z4,z729,z9]),(0,[z1,z2,z3,z4,z9,z251]),(0,[z1,z2,z3,z4,z730,z18]),(0,[z731,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z638,z2,z43,z4,z5,z9]),(0,[z1,z2,z732,z3,z4,z5]),(0,[z1,z2,z3,z4,z238,z18]),(0,[z1,z2,z3,z4,z5,z733])],[(0,[z209,z2,z43,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z734]),(0,[z1,z2,z3,z4,z5,z735]),(0,[z2,z3,z4,z736,z5,z9]),(0,[z2,z3,z4,z5,z718,z293]),(0,[z1,z3,z4,z713,z85,z9]),(0,[z1,z2,z397,z3,z4,z18]),(0,[z1,z2,z3,z4,z5,z170]),(0,[z1,z2,z3,z4,z5,z737])],[(0,[z1,z2,z3,z4,z5,z738]),(0,[z1,z2,z3,z4,z739,z39])],[(0,[z1,z2,z4,z740,z5,z9]),(0,[z1,z2,z3,z5,z18,z196])],[(0,[z1,z2,z3,z4,z5,z741]),(0,[z1,z2,z3,z4,z5,z742]),(0,[z1,z2,z3,z4,z743,z9])],[(0,[z1,z2,z224,z3,z4,z9]),(0,[z1,z2,z744,z4,z5,z9]),(0,[z1,z2,z3,z35,z37,z170]),(0,[z1,z2,z328,z3,z4,z39])],[(0,[z1,z2,z3,z4,z5,z745]),(0,[z1,z2,z4,z746,z5,z9]),(0,[z1,z2,z3,z4,z5,z747]),(0,[z1,z2,z108,z3,z4,z39]),(0,[z1,z2,z16,z4,z218,z427]),(0,[z1,z2,z442,z4,z5,z6]),(0,[z1,z2,z33,z4,z5,z6])]],
   [[(0,[z186,z1,z2,z3,z4,z5]),(0,[z1,z2,z4,z748,z5,z9]),(0,[z317,z305,z101,z4,z5,z9]),(0,[z1,z2,z3,z4,z749,z9]),(0,[z1,z2,z108,z98,z3,z4])],[(0,[z1,z2,z3,z4,z5,z750]),(0,[z1,z2,z55,z397,z4,z9]),(0,[z1,z2,z3,z4,z751,z6])],[(0,[z1,z2,z3,z4,z5,z534]),(0,[z752,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z753]),(0,[z1,z2,z4,z278,z5,z170])],[(0,[z494,z2,z3,z57,z5,z9]),(0,[z1,z2,z3,z4,z136,z270]),(0,[z1,z754,z3,z4,z5,z9]),(0,[z51,z2,z476,z3,z4,z9]),(0,[z1,z2,z3,z4,z755,z9]),(0,[z67,z1,z3,z4,z68,z18]),(0,[z1,z2,z98,z4,z729,z9]),(0,[z1,z2,z148,z3,z4,z193])],[(0,[z1,z756,z3,z4,z5,z9]),(0,[z1,z2,z324,z4,z5,z22]),(0,[z1,z2,z3,z4,z84,z9]),(0,[z1,z2,z202,z3,z5,z6])],[(0,[z1,z757,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z758]),(0,[z1,z2,z324,z3,z4,z5]),(0,[z7,z2,z3,z57,z131,z9]),(0,[z1,z2,z3,z4,z5,z759]),(0,[z1,z3,z4,z68,z713,z9]),(0,[z1,z2,z4,z5,z9,z760]),(0,[z1,z2,z3,z4,z761,z18])],[(0,[z105,z230,z3,z4,z5,z9]),(0,[z1,z762,z3,z4,z5,z9]),(0,[z1,z2,z276,z4,z5,z6]),(0,[z1,z2,z4,z5,z9,z763]),(0,[z1,z2,z3,z4,z341,z158])],[(0,[z1,z522,z3,z4,z85,z9]),(0,[z1,z126,z100,z4,z5,z9]),(0,[z764,z2,z3,z4,z5,z9]),(0,[z1,z2,z765,z3,z4,z5]),(0,[z1,z2,z148,z4,z38,z39])]],
   [[(0,[z1,z2,z3,z4,z766,z9]),(0,[z1,z2,z3,z4,z5,z767]),(0,[z1,z768,z3,z4,z5,z9]),(0,[z1,z2,z769,z3,z4,z5]),(0,[z770,z2,z3,z4,z5,z9]),(0,[z1,z285,z3,z4,z85,z9]),(0,[z1,z2,z771,z3,z4,z5]),(0,[z1,z2,z3,z4,z138,z18]),(0,[z772,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z773,z9]),(0,[z1,z2,z3,z4,z774,z9]),(0,[z1,z2,z53,z4,z5,z342]),(0,[z1,z2,z3,z4,z136,z9]),(0,[z122,z2,z3,z4,z5,z372]),(1,[z1,z3,z775,z5,z9]),(0,[z1,z2,z3,z4,z5,z776]),(0,[z1,z777,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z778,z9]),(0,[z779,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z780]),(0,[z246,z88,z3,z4,z5,z9]),(0,[z1,z2,z4,z740,z286,z9]),(0,[z1,z2,z54,z44,z5,z9]),(0,[z781,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z782])],[(0,[z1,z2,z142,z4,z5,z18]),(0,[z153,z2,z3,z4,z5,z18]),(0,[z783,z2,z3,z4,z5,z9]),(0,[z63,z1,z3,z4,z5,z366]),(0,[z1,z2,z397,z3,z4,z21])],[(0,[z1,z2,z784,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z785])],[(1,[z2,z3,z736,z5,z9]),(0,[z1,z3,z4,z713,z5,z9]),(0,[z1,z2,z16,z4,z218,z18])],[(0,[z438,z11,z3,z4,z5,z9]),(0,[z1,z2,z4,z5,z9,z786]),(0,[z1,z2,z3,z4,z5,z787]),(0,[z1,z2,z788,z4,z5,z18])],[(0,[z0,z186,z11,z3,z4,z5]),(0,[z1,z440,z3,z4,z5,z6]),(0,[z1,z2,z127,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z789]),(0,[z83,z1,z3,z221,z5,z18]),(0,[z1,z2,z3,z264,z5,z6]),(0,[z1,z2,z3,z4,z166,z21])]],
   [[(0,[z1,z2,z790,z4,z5,z9]),(0,[z1,z2,z3,z791,z5,z9]),(0,[z792,z2,z3,z4,z5,z9]),(0,[z1,z2,z55,z397,z4,z22]),(0,[z1,z2,z3,z4,z492,z21]),(0,[z1,z2,z4,z5,z6,z38])],[(0,[z1,z2,z276,z4,z84,z9]),(0,[z76,z1,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z793])],[(0,[z1,z198,z90,z4,z5,z9]),(0,[z1,z2,z381,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z794]),(0,[z1,z3,z775,z221,z5,z9]),(0,[z1,z2,z3,z4,z5,z795]),(0,[z1,z2,z283,z4,z5,z6]),(0,[z1,z796,z3,z4,z5,z9]),(0,[z797,z2,z3,z4,z5,z9]),(0,[z1,z2,z148,z3,z4,z427])],[(0,[z1,z2,z133,z4,z5,z18]),(0,[z1,z103,z3,z163,z5,z346]),(0,[z1,z2,z3,z4,z5,z798]),(0,[z1,z2,z799,z3,z4,z5]),(0,[z800,z2,z3,z4,z5,z18])],[(0,[z468,z11,z3,z4,z5,z9]),(0,[z1,z2,z801,z3,z4,z9]),(0,[z87,z1,z2,z3,z4,z286]),(0,[z1,z2,z3,z4,z5,z802]),(0,[z122,z2,z3,z4,z5,z114])],[(0,[z1,z2,z3,z4,z5,z803]),(0,[z1,z2,z804,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z81]),(0,[z1,z2,z3,z4,z5,z69]),(0,[z1,z2,z4,z805,z5,z9])],[(0,[z1,z2,z53,z645,z4,z5]),(0,[z1,z2,z806,z3,z4,z5])],[(1,[z1,z3,z4,z713,z9])]],
   [[(0,[z1,z2,z807,z3,z4,z5]),(0,[z1,z2,z3,z4,z808,z9]),(0,[z1,z2,z3,z4,z5,z15])],[(0,[z809,z2,z3,z4,z5,z9]),(0,[z246,z2,z3,z4,z5,z6]),(0,[z1,z2,z35,z278,z37,z9])],[(0,[z488,z11,z3,z4,z5,z9]),(0,[z87,z2,z211,z4,z5,z293]),(0,[z1,z2,z3,z4,z5,z810]),(0,[z1,z285,z3,z4,z713,z9]),(0,[z1,z2,z3,z35,z37,z9]),(0,[z1,z2,z811,z4,z5,z9])],[(0,[z1,z2,z812,z3,z4,z5]),(0,[z87,z2,z470,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z813])],[(0,[z1,z814,z3,z4,z5,z9]),(0,[z52,z246,z2,z3,z4,z5]),(0,[z1,z2,z815,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z816]),(0,[z1,z2,z3,z4,z9,z817]),(1,[z1,z2,z3,z4,z739])],[(0,[z1,z2,z3,z4,z5,z818]),(0,[z1,z2,z3,z4,z819,z9]),(0,[z1,z2,z48,z61,z5,z18]),(0,[z1,z2,z3,z5,z517,z6])],[(0,[z1,z2,z3,z4,z820,z9]),(0,[z2,z3,z4,z5,z178,z718])],[(0,[z1,z2,z66,z4,z5,z18]),(0,[z1,z2,z90,z4,z5,z270]),(0,[z1,z2,z283,z108,z4,z5]),(0,[z1,z2,z3,z4,z286,z17]),(0,[z1,z2,z3,z4,z5,z821]),(0,[z1,z2,z3,z4,z822,z9])]],
   [[(0,[z501,z65,z3,z4,z5,z9]),(0,[z1,z2,z224,z4,z75,z9]),(0,[z122,z3,z4,z221,z5,z9])],[(0,[z1,z2,z3,z4,z5,z823]),(0,[z1,z2,z3,z4,z152,z18]),(0,[z1,z2,z3,z4,z5,z824])],[(0,[z1,z2,z825,z4,z5,z9]),(0,[z7,z2,z3,z57,z136,z9]),(0,[z83,z1,z3,z775,z5,z9])],[(0,[z1,z2,z3,z826,z5,z9]),(0,[z1,z2,z827,z3,z4,z9]),(0,[z1,z2,z3,z4,z84,z372]),(0,[z1,z2,z16,z4,z318,z9]),(0,[z1,z2,z31,z3,z32,z6])],[(0,[z105,z530,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z58,z6]),(0,[z828,z2,z3,z4,z5,z9])],[(0,[z1,z2,z90,z4,z5,z9]),(0,[z1,z10,z3,z4,z5,z18])],[(0,[z1,z2,z142,z4,z5,z6]),(0,[z153,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z91,z5]),(0,[z1,z2,z16,z108,z3,z4]),(0,[z1,z2,z4,z5,z17,z527])],[(0,[z60,z2,z3,z4,z5,z9]),(0,[z1,z2,z324,z4,z75,z5]),(0,[z1,z2,z829,z3,z4,z5]),(0,[z1,z2,z3,z4,z830,z9]),(0,[z1,z2,z343,z3,z32,z9]),(0,[z1,z2,z3,z4,z5,z831]),(0,[z1,z2,z832,z4,z5,z9])]],
   [[(0,[z186,z1,z231,z3,z4,z5]),(0,[z1,z2,z833,z4,z5,z9]),(0,[z1,z2,z16,z4,z218,z6]),(0,[z834,z2,z3,z4,z5,z6])],[(0,[z1,z2,z835,z3,z4,z5]),(0,[z1,z2,z108,z3,z4,z5]),(0,[z1,z2,z442,z4,z37,z9]),(0,[z76,z1,z3,z4,z5,z124])],[(0,[z1,z2,z324,z53,z4,z5]),(0,[z1,z2,z836,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z837]),(0,[z838,z2,z3,z4,z5,z9]),(0,[z839,z2,z3,z4,z5,z9]),(0,[z1,z2,z840,z3,z4,z5])],[(0,[z315,z65,z3,z4,z5,z9]),(0,[z1,z2,z113,z4,z5,z9]),(0,[z1,z2,z841,z3,z4,z5]),(0,[z1,z2,z4,z318,z5,z9])],[(0,[z1,z2,z3,z4,z5,z842]),(0,[z7,z2,z3,z736,z5,z9]),(0,[z1,z843,z3,z4,z5,z9]),(0,[z87,z2,z3,z4,z5,z112]),(0,[z122,z2,z3,z4,z5,z18]),(0,[z63,z1,z3,z4,z5,z844]),(0,[z1,z2,z3,z4,z5,z158])],[(0,[z1,z2,z3,z4,z9,z845]),(0,[z1,z2,z3,z4,z846,z9]),(0,[z1,z2,z3,z4,z5,z847])],[(0,[z1,z2,z3,z4,z5,z848]),(0,[z1,z2,z3,z4,z5,z849]),(0,[z1,z2,z3,z4,z131,z18]),(0,[z8,z2,z3,z110,z5,z18]),(0,[z1,z2,z133,z4,z5,z6]),(0,[z1,z2,z127,z4,z5,z372]),(0,[z1,z2,z3,z4,z84,z114]),(0,[z1,z2,z98,z4,z318,z9]),(0,[z1,z2,z3,z5,z850,z6]),(0,[z192,z1,z3,z4,z5,z366])],[(0,[z65,z756,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z851,z9]),(0,[z1,z2,z397,z43,z4,z9])]],
   [[(0,[z1,z2,z3,z4,z852,z9]),(0,[z1,z88,z231,z3,z4,z5]),(0,[z1,z2,z491,z3,z32,z9]),(0,[z1,z2,z16,z4,z327,z9])],[(0,[z1,z2,z3,z4,z5,z853]),(0,[z1,z2,z4,z854,z5,z9]),(0,[z1,z2,z3,z155,z5,z18]),(0,[z1,z2,z3,z4,z18,z855])],[(0,[z1,z2,z3,z856,z5,z9]),(0,[z1,z2,z16,z133,z4,z9]),(0,[z1,z2,z3,z4,z5,z857]),(0,[z1,z103,z3,z163,z5,z6]),(0,[z1,z3,z4,z5,z844,z9]),(0,[z1,z2,z3,z4,z858,z5])],[(0,[z756,z11,z3,z4,z5,z9]),(0,[z1,z2,z397,z135,z4,z9]),(0,[z1,z2,z3,z4,z9,z855]),(0,[z1,z2,z3,z4,z859,z9]),(0,[z1,z523,z3,z4,z85,z9]),(0,[z63,z1,z3,z4,z5,z347]),(0,[z1,z2,z3,z4,z341,z9]),(0,[z1,z2,z16,z4,z218,z255])],[(0,[z1,z2,z339,z3,z4,z18]),(0,[z1,z2,z53,z4,z5,z571]),(0,[z1,z2,z3,z822,z32,z9]),(0,[z1,z2,z4,z5,z6,z860]),(0,[z1,z2,z861,z3,z4,z9])],[(0,[z1,z2,z3,z4,z5,z862]),(0,[z1,z2,z3,z4,z863,z9]),(0,[z1,z2,z3,z4,z864,z5]),(0,[z1,z2,z3,z4,z5,z865])],[(0,[z1,z440,z66,z4,z5,z9]),(0,[z625,z1,z3,z4,z68,z9]),(0,[z1,z2,z462,z3,z5,z6])],[(0,[z1,z2,z866,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z867]),(0,[z1,z2,z3,z461,z5,z6])]],
   [[(0,[z1,z2,z3,z868,z5,z9]),(0,[z1,z2,z3,z4,z5,z869]),(0,[z1,z2,z3,z4,z5,z870]),(0,[z1,z422,z3,z4,z68,z9]),(0,[z1,z2,z16,z4,z496,z9]),(0,[z1,z871,z3,z4,z5,z9])],[(0,[z1,z2,z43,z4,z5,z427]),(0,[z25,z203,z3,z4,z216,z9]),(0,[z1,z2,z127,z4,z5,z114]),(0,[z1,z697,z3,z4,z85,z9]),(0,[z1,z2,z108,z3,z4,z166])],[(0,[z1,z872,z3,z4,z5,z9]),(0,[z209,z2,z873,z4,z5,z9]),(0,[z122,z2,z276,z4,z5,z9]),(0,[z1,z2,z127,z4,z58,z9]),(0,[z1,z2,z705,z3,z5,z6]),(0,[z1,z2,z725,z4,z5,z18]),(0,[z731,z2,z3,z4,z5,z18])],[(0,[z1,z2,z874,z3,z5,z9]),(0,[z1,z2,z875,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z876]),(0,[z1,z440,z90,z4,z5,z9]),(0,[z1,z2,z16,z161,z4,z9]),(0,[z1,z3,z163,z775,z5,z9]),(0,[z1,z2,z3,z179,z5,z18]),(0,[z1,z2,z3,z4,z5,z850])],[(0,[z186,z246,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z877,z9]),(0,[z1,z2,z48,z627,z5,z9]),(0,[z878,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z152,z6]),(0,[z1,z2,z283,z4,z37,z9]),(0,[z1,z2,z3,z4,z5,z879])],[(0,[z1,z2,z3,z4,z5,z880]),(0,[z1,z2,z98,z133,z4,z9]),(0,[z1,z2,z3,z4,z5,z881])],[(0,[z2,z873,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z882,z9]),(0,[z7,z2,z90,z57,z5,z9]),(0,[z1,z2,z3,z883,z5,z9]),(0,[z1,z2,z3,z4,z5,z884]),(0,[z1,z126,z100,z4,z411,z9]),(0,[z1,z2,z3,z4,z548,z21])],[(0,[z1,z2,z3,z4,z5,z885]),(0,[z1,z2,z3,z4,z886,z9]),(0,[z1,z2,z3,z4,z5,z887]),(0,[z1,z2,z283,z4,z91,z5]),(0,[z1,z88,z2,z397,z3,z4]),(0,[z1,z2,z31,z3,z32,z69])]],
   [[(0,[z0,z11,z3,z4,z5,z9]),(0,[z1,z2,z224,z3,z4,z18]),(0,[z1,z198,z3,z4,z5,z270]),(0,[z888,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z889]),(0,[z1,z2,z4,z44,z138,z9])],[(0,[z51,z2,z3,z4,z80,z9]),(0,[z1,z2,z3,z542,z37,z9])],[(0,[z2,z3,z110,z736,z5,z9]),(0,[z1,z2,z3,z5,z118,z6]),(0,[z1,z890,z3,z4,z5,z9])],[(0,[z1,z2,z891,z3,z4,z5]),(0,[z1,z2,z16,z224,z4,z9]),(0,[z1,z2,z3,z4,z5,z892]),(0,[z1,z893,z3,z4,z5,z9]),(0,[z25,z2,z3,z4,z894,z9]),(0,[z1,z2,z442,z4,z5,z170])],[(0,[z1,z2,z895,z4,z5,z9]),(0,[z52,z2,z3,z4,z5,z178]),(0,[z1,z2,z3,z4,z5,z739])],[(0,[z1,z440,z3,z4,z131,z9]),(0,[z1,z2,z3,z4,z5,z896]),(0,[z1,z2,z3,z4,z5,z897]),(0,[z1,z2,z898,z4,z5,z9]),(0,[z1,z2,z480,z4,z5,z571]),(0,[z899,z2,z3,z4,z5,z6])],[(0,[z1,z198,z3,z4,z5,z9]),(0,[z570,z11,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z900]),(0,[z187,z2,z873,z4,z5,z9]),(0,[z1,z2,z3,z901,z5,z9]),(0,[z1,z2,z3,z4,z5,z902]),(0,[z1,z2,z3,z4,z84,z18]),(0,[z1,z2,z202,z3,z5,z850])],[(0,[z1,z2,z3,z4,z5,z903]),(0,[z1,z285,z3,z4,z91,z85]),(0,[z1,z2,z4,z5,z18,z763])]],
   [[(0,[z373,z2,z135,z4,z5,z9]),(0,[z8,z440,z3,z4,z5,z9]),(0,[z1,z2,z98,z4,z75,z6])],[(0,[z1,z2,z4,z904,z5,z9]),(0,[z8,z2,z3,z110,z5,z6]),(0,[z1,z126,z100,z4,z5,z18]),(0,[z1,z88,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z138,z64])],[(0,[z1,z2,z3,z4,z5,z905]),(0,[z1,z906,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z907,z9]),(0,[z1,z285,z3,z4,z85,z18]),(0,[z1,z285,z108,z3,z4,z85]),(0,[z1,z2,z3,z4,z5,z908])],[(0,[z1,z2,z211,z4,z5,z9]),(0,[z1,z909,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z136,z18]),(0,[z1,z910,z3,z4,z5,z9]),(0,[z87,z1,z2,z33,z4,z5]),(0,[z1,z231,z3,z4,z5,z6]),(0,[z52,z2,z3,z4,z5,z718]),(0,[z1,z2,z3,z4,z911,z9]),(0,[z1,z2,z3,z4,z21,z177])],[(0,[z1,z2,z912,z3,z4,z9]),(0,[z1,z2,z3,z4,z913,z9]),(0,[z1,z2,z54,z44,z5,z18]),(0,[z1,z2,z3,z4,z5,z914])],[(0,[z186,z1,z88,z3,z4,z5]),(0,[z1,z2,z915,z4,z5,z9]),(0,[z1,z2,z916,z3,z4,z5]),(0,[z1,z2,z3,z4,z411,z9]),(0,[z1,z2,z917,z4,z5,z9]),(0,[z1,z2,z31,z3,z822,z9])],[(0,[z1,z918,z3,z4,z5,z9]),(0,[z1,z2,z919,z3,z4,z5]),(0,[z1,z2,z244,z4,z5,z17])],[(0,[z1,z2,z920,z4,z5,z9]),(0,[z1,z2,z339,z3,z4,z6]),(0,[z1,z2,z3,z736,z5,z9]),(0,[z8,z2,z3,z110,z5,z210]),(0,[z1,z2,z16,z4,z407,z9]),(0,[z2,z3,z4,z5,z6,z921])]],
   [[(0,[z321,z2,z135,z4,z5,z9]),(0,[z305,z2,z3,z4,z5,z6]),(0,[z922,z2,z3,z4,z5,z9]),(0,[z1,z2,z709,z4,z5,z9])],[(0,[z1,z2,z3,z4,z923,z9]),(0,[z1,z2,z3,z4,z5,z924]),(0,[z1,z2,z3,z4,z5,z925]),(0,[z2,z3,z4,z894,z216,z9]),(0,[z1,z2,z127,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z150])],[(0,[z62,z11,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z926,z5]),(0,[z1,z463,z3,z4,z5,z6]),(0,[z1,z2,z927,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z928]),(0,[z1,z2,z3,z4,z5,z270]),(0,[z929,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z854,z5,z9]),(0,[z1,z2,z3,z4,z5,z930]),(0,[z1,z3,z4,z5,z6,z931])],[(0,[z1,z2,z3,z4,z5,z932]),(0,[z1,z2,z933,z3,z5,z9]),(0,[z1,z2,z3,z4,z5,z934])],[(0,[z1,z2,z3,z4,z935,z9]),(0,[z1,z936,z3,z4,z5,z9]),(0,[z1,z2,z937,z4,z5,z9]),(0,[z1,z2,z61,z854,z5,z9])],[(0,[z1,z2,z938,z4,z5,z9]),(0,[z1,z126,z939,z4,z5,z9])],[(0,[z187,z2,z135,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z940]),(0,[z1,z2,z3,z4,z5,z941]),(0,[z1,z2,z942,z3,z4,z9]),(0,[z63,z1,z2,z142,z4,z5]),(0,[z1,z2,z3,z4,z943,z9]),(0,[z1,z88,z3,z4,z286,z29]),(0,[z1,z2,z3,z4,z238,z6]),(0,[z63,z60,z3,z4,z5,z12])]],
   [[(0,[z2,z756,z3,z4,z5,z9]),(0,[z1,z203,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z944]),(0,[z1,z3,z939,z4,z5,z9]),(0,[z122,z2,z3,z4,z58,z9]),(0,[z1,z2,z397,z3,z4,z6]),(0,[z1,z2,z3,z4,z945,z9]),(0,[z1,z2,z4,z5,z18,z38])],[(0,[z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z946,z3,z4,z5]),(0,[z1,z2,z3,z4,z947,z9]),(0,[z2,z3,z736,z57,z5,z9]),(0,[z1,z948,z3,z4,z5,z9]),(0,[z392,z2,z3,z4,z5,z293]),(0,[z1,z2,z949,z4,z5,z9]),(0,[z1,z2,z3,z35,z822,z9])],[(0,[z209,z2,z43,z4,z5,z9]),(0,[z1,z2,z3,z4,z950,z9]),(0,[z1,z2,z3,z4,z5,z951]),(0,[z1,z2,z4,z5,z9,z38]),(0,[z1,z2,z55,z4,z5,z617]),(0,[z1,z2,z33,z4,z5,z17])],[(0,[z1,z2,z3,z4,z5,z952]),(0,[z1,z2,z3,z4,z5,z953]),(0,[z1,z2,z224,z3,z4,z6]),(1,[z1,z939,z4,z5,z9]),(0,[z1,z2,z3,z4,z954,z9]),(0,[z1,z2,z3,z4,z955,z9]),(0,[z1,z2,z3,z4,z21,z739])],[(0,[z1,z2,z956,z4,z5,z9]),(0,[z51,z2,z3,z4,z80,z464]),(0,[z957,z2,z3,z4,z5,z9]),(0,[z1,z2,z854,z44,z5,z9]),(0,[z1,z2,z4,z426,z75,z9]),(0,[z1,z2,z3,z35,z37,z18])],[(0,[z1,z2,z3,z4,z5,z267]),(0,[z1,z2,z16,z4,z433,z9])],[(0,[z1,z2,z66,z4,z5,z409]),(1,[z2,z3,z4,z5,z718]),(0,[z1,z2,z3,z4,z5,z958]),(0,[z1,z2,z959,z3,z4,z9]),(0,[z1,z2,z48,z61,z5,z64])],[(0,[z7,z198,z3,z57,z5,z9]),(0,[z1,z2,z33,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z960])]],
   [[(0,[z1,z2,z961,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z962]),(0,[z1,z2,z3,z4,z5,z963])],[(0,[z1,z2,z3,z204,z5,z6]),(0,[z67,z1,z3,z4,z68,z6]),(0,[z1,z88,z3,z4,z5,z567]),(0,[z1,z2,z4,z278,z5,z9]),(0,[z1,z2,z53,z4,z5,z17]),(0,[z1,z2,z3,z4,z751,z9])],[(0,[z1,z2,z3,z4,z5,z964]),(0,[z1,z440,z3,z4,z136,z9]),(0,[z1,z2,z3,z965,z5,z9])],[(0,[z1,z2,z90,z4,z5,z409]),(0,[z966,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z760]),(0,[z1,z2,z442,z35,z37,z9]),(0,[z1,z967,z3,z4,z5,z6])],[(0,[z186,z2,z3,z4,z5,z178]),(0,[z1,z2,z968,z3,z4,z9]),(0,[z2,z3,z4,z80,z894,z9]),(0,[z1,z285,z283,z4,z85,z9]),(0,[z1,z2,z969,z3,z4,z5]),(0,[z1,z2,z3,z35,z37,z36]),(0,[z1,z2,z970,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z971])],[(0,[z1,z972,z3,z4,z5,z9]),(0,[z63,z1,z231,z3,z4,z5]),(0,[z1,z2,z4,z973,z5,z9]),(0,[z1,z285,z3,z4,z85,z6]),(0,[z1,z2,z430,z4,z5,z17])],[(0,[z1,z974,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z9,z975]),(0,[z1,z2,z276,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z844]),(0,[z1,z2,z16,z4,z589,z9]),(0,[z1,z2,z3,z4,z138,z6]),(0,[z1,z777,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z976,z9]),(0,[z1,z2,z90,z4,z5,z18]),(0,[z1,z2,z3,z4,z286,z9]),(0,[z977,z2,z3,z4,z5,z9])]],
   [[(0,[z2,z11,z142,z4,z5,z9]),(0,[z1,z673,z100,z4,z5,z9]),(0,[z978,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z979])],[(0,[z1,z2,z980,z4,z5,z9]),(0,[z1,z2,z981,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z982]),(0,[z1,z2,z983,z4,z5,z9]),(0,[z60,z2,z3,z4,z5,z18]),(0,[z984,z2,z3,z4,z5,z9])],[(0,[z304,z2,z4,z75,z5,z9])],[(0,[z304,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z985]),(0,[z1,z2,z986,z4,z5,z9]),(0,[z87,z2,z3,z4,z5,z293]),(1,[z1,z2,z4,z729,z9])],[(0,[z316,z2,z43,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z987]),(0,[z7,z2,z3,z57,z5,z270]),(0,[z1,z2,z55,z142,z4,z5]),(0,[z1,z2,z127,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z988])],[(0,[z1,z2,z135,z4,z5,z427]),(0,[z1,z2,z3,z4,z131,z409]),(1,[z2,z3,z4,z894,z9]),(0,[z1,z2,z113,z4,z5,z18]),(0,[z989,z2,z3,z4,z5,z9]),(0,[z83,z1,z3,z221,z5,z6]),(0,[z1,z88,z454,z3,z4,z5]),(0,[z1,z2,z536,z4,z5,z617])],[(0,[z1,z2,z990,z4,z5,z9]),(0,[z1,z2,z991,z3,z4,z9]),(0,[z1,z992,z3,z4,z5,z9])],[(0,[z1,z440,z3,z4,z5,z9]),(0,[z1,z993,z3,z4,z5,z9]),(0,[z1,z2,z3,z99,z37,z9]),(0,[z1,z2,z3,z4,z846,z18])]],
   [[(0,[z1,z2,z3,z4,z5,z994]),(0,[z995,z2,z3,z4,z5,z9]),(0,[z1,z2,z53,z4,z5,z760])],[(0,[z187,z2,z400,z4,z5,z9]),(0,[z1,z2,z996,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z232]),(0,[z1,z103,z3,z775,z5,z9]),(0,[z1,z2,z33,z4,z68,z9])],[(0,[z7,z2,z3,z57,z5,z9]),(0,[z1,z2,z4,z997,z5,z9]),(0,[z1,z2,z3,z5,z822,z9]),(0,[z1,z2,z998,z4,z5,z9]),(0,[z1,z2,z999,z4,z5,z9])],[(0,[z1,z1000,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1001]),(0,[z1,z2,z3,z4,z1002,z9]),(0,[z1,z2,z3,z4,z5,z1003]),(0,[z1,z2,z525,z4,z5,z22])],[(0,[z1,z11,z108,z3,z4,z5]),(0,[z1,z2,z1004,z4,z5,z9]),(0,[z1,z2,z3,z4,z1005,z9]),(0,[z153,z2,z3,z4,z84,z9])],[(0,[z1,z2,z3,z4,z5,z1006]),(0,[z1,z2,z3,z4,z341,z18])],[(0,[z1,z2,z3,z4,z1007,z9]),(0,[z51,z2,z133,z4,z80,z9]),(0,[z1,z2,z3,z4,z286,z22]),(0,[z1,z2,z861,z3,z4,z18]),(0,[z1,z2,z33,z4,z21,z9])],[(0,[z1,z2,z48,z854,z5,z9])]],
   [[(0,[z1,z2,z3,z4,z5,z372]),(0,[z1,z88,z3,z4,z5,z704]),(0,[z1,z2,z3,z4,z1008,z9]),(0,[z1,z2,z3,z5,z18,z6]),(0,[z1,z2,z1009,z4,z5,z9])],[(0,[z1,z2,z3,z4,z1010,z9]),(0,[z246,z2,z3,z4,z5,z9]),(0,[z1,z2,z1011,z4,z5,z9]),(0,[z1,z126,z100,z4,z5,z289]),(0,[z1,z2,z3,z4,z5,z1012]),(0,[z1,z2,z280,z3,z4,z193])],[(0,[z11,z3,z4,z5,z618,z9]),(0,[z1,z2,z3,z4,z5,z1013]),(0,[z1,z2,z16,z324,z4,z5]),(0,[z1,z203,z16,z3,z4,z9]),(0,[z1,z2,z3,z5,z18,z514]),(0,[z1,z2,z3,z4,z9,z1014]),(0,[z1,z2,z1015,z4,z5,z9]),(0,[z1,z2,z4,z5,z9,z1016]),(0,[z1,z871,z3,z4,z5,z18])],[(0,[z186,z87,z2,z3,z4,z5]),(0,[z1017,z2,z3,z4,z5,z9]),(0,[z1,z2,z48,z61,z5,z6]),(0,[z1,z2,z31,z3,z32,z150])],[(0,[z1,z2,z1018,z3,z4,z9]),(0,[z1,z2,z1019,z4,z5,z9]),(0,[z87,z246,z2,z3,z4,z5]),(0,[z695,z1,z101,z4,z5,z9]),(0,[z1,z2,z4,z729,z218,z9]),(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z2,z3,z706,z5,z18])],[(0,[z1,z2,z66,z4,z5,z6]),(0,[z25,z2,z3,z4,z216,z9]),(0,[z130,z2,z3,z4,z5,z178]),(0,[z1021,z2,z3,z4,z5,z9]),(0,[z1,z2,z1022,z3,z4,z5])],[(0,[z1,z2,z359,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1023]),(0,[z1,z2,z3,z4,z5,z1024]),(0,[z1025,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1026]),(0,[z1,z2,z1027,z3,z4,z6])],[(0,[z1,z2,z3,z292,z5,z6]),(0,[z0,z359,z11,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1028]),(0,[z153,z2,z127,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1029])]],
   [[(0,[z1,z2,z3,z1030,z4,z9]),(0,[z1,z2,z3,z4,z5,z1031])],[(0,[z1,z2,z1032,z4,z5,z9]),(0,[z130,z2,z3,z4,z5,z194])],[(0,[z0,z11,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z1033,z9]),(0,[z1,z2,z339,z256,z3,z4]),(0,[z304,z2,z16,z4,z5,z9]),(0,[z1,z2,z16,z4,z21,z17])],[(0,[z195,z11,z3,z4,z5,z9]),(0,[z1,z2,z256,z224,z3,z4]),(0,[z51,z2,z3,z4,z80,z18]),(0,[z1,z10,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z114]),(0,[z83,z1,z127,z221,z5,z9]),(0,[z1,z2,z4,z5,z760,z22]),(0,[z1,z2,z31,z3,z32,z9])],[(0,[z1,z2,z3,z1034,z4,z5]),(0,[z1,z198,z3,z4,z5,z409]),(0,[z1,z2,z3,z4,z58,z9]),(0,[z1,z2,z1035,z4,z5,z9]),(0,[z60,z2,z3,z4,z5,z6])],[(0,[z1,z1036,z3,z4,z5,z9]),(0,[z1,z1037,z3,z4,z5,z9]),(0,[z1,z203,z98,z3,z4,z9]),(0,[z1,z2,z276,z4,z5,z372]),(0,[z1,z2,z3,z4,z1038,z5])],[(0,[z1,z1039,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1040]),(0,[z1,z2,z3,z4,z1041,z9])],[(0,[z1,z2,z3,z1042,z5,z9])]],
   [[(0,[z1,z2,z1043,z3,z5,z9]),(0,[z1,z2,z3,z4,z5,z1044]),(0,[z7,z440,z3,z57,z5,z9]),(0,[z1,z198,z3,z4,z5,z18]),(0,[z1,z1045,z2,z3,z4,z5]),(0,[z1,z2,z113,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z289]),(0,[z834,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z548,z156])],[(0,[z1,z65,z108,z3,z4,z5]),(0,[z317,z304,z101,z4,z5,z9]),(0,[z1,z2,z1046,z4,z5,z9])],[(0,[z1,z2,z3,z4,z136,z409]),(0,[z1,z1047,z3,z4,z5,z9]),(0,[z122,z2,z3,z4,z5,z6])],[(0,[z1,z2,z48,z61,z138,z9]),(0,[z1,z2,z55,z4,z251,z22]),(0,[z1,z2,z33,z148,z4,z39])],[(0,[z1,z2,z3,z4,z131,z6]),(0,[z1,z2,z3,z4,z5,z1048]),(0,[z1,z2,z3,z351,z37,z9]),(0,[z1,z2,z3,z4,z5,z1049]),(1,[z1,z2,z3,z822,z9]),(0,[z1,z2,z185,z3,z5,z6])],[(0,[z1,z2,z3,z4,z1050,z9]),(0,[z1051,z1,z2,z3,z4,z5]),(0,[z1,z2,z211,z4,z5,z18]),(0,[z1,z126,z100,z4,z152,z9]),(0,[z1,z2,z3,z775,z5,z9]),(0,[z1,z2,z1052,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z427]),(0,[z1,z2,z3,z592,z32,z9])],[(0,[z1,z2,z1053,z4,z5,z9]),(0,[z1,z3,z4,z5,z12,z844]),(0,[z1054,z1,z3,z4,z5,z9])],[(0,[z1,z2,z4,z5,z9,z1055]),(0,[z1,z2,z3,z4,z411,z18]),(0,[z1,z2,z3,z4,z1056,z5]),(0,[z1,z2,z33,z4,z85,z9]),(0,[z1,z2,z55,z4,z5,z760])]],
   [[(0,[z105,z65,z3,z4,z5,z9]),(0,[z186,z1,z3,z4,z5,z12]),(0,[z1,z2,z53,z142,z4,z5]),(0,[z1,z2,z276,z4,z5,z114]),(0,[z1,z2,z3,z4,z5,z1057]),(0,[z1058,z2,z3,z4,z5,z9])],[(0,[z1,z1059,z3,z4,z5,z9]),(0,[z1,z2,z276,z4,z58,z9]),(0,[z1,z2,z4,z1060,z5,z9]),(0,[z1,z3,z4,z5,z844,z29])],[(0,[z1,z2,z1061,z3,z4,z5]),(0,[z1,z2,z3,z162,z5,z6]),(0,[z1,z103,z3,z163,z5,z9]),(0,[z1062,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1063]),(0,[z1,z2,z3,z4,z1064,z5])],[(0,[z1,z2,z339,z48,z4,z9]),(0,[z1,z2,z324,z224,z3,z4]),(0,[z1,z2,z3,z4,z1065,z9]),(0,[z1,z2,z4,z5,z1066,z9]),(0,[z1,z2,z1067,z4,z5,z9]),(0,[z1,z2,z33,z4,z5,z427]),(0,[z1,z2,z397,z3,z4,z39]),(0,[z1,z2,z4,z5,z18,z1068])],[(0,[z1,z2,z1069,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1070]),(0,[z87,z2,z431,z3,z4,z5]),(0,[z317,z1,z101,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1071]),(0,[z1,z2,z55,z4,z5,z22])],[(0,[z1,z3,z4,z1072,z5,z9]),(0,[z1,z1073,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z166,z286]),(0,[z1,z2,z16,z651,z4,z9]),(0,[z1,z2,z4,z5,z9,z1068])],[(0,[z1,z2,z3,z4,z5,z1074]),(0,[z1,z2,z3,z4,z5,z1075]),(0,[z1,z2,z1076,z3,z4,z9]),(0,[z52,z231,z3,z4,z5,z178]),(0,[z1,z2,z3,z260,z5,z18]),(0,[z1,z2,z3,z4,z5,z1077])],[(0,[z1,z2,z1078,z4,z5,z9]),(0,[z424,z2,z43,z4,z5,z9]),(0,[z1,z2,z3,z4,z1079,z9]),(0,[z1,z2,z3,z4,z5,z409]),(0,[z1,z1080,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1081]),(0,[z1,z2,z3,z4,z5,z346])]],
   [[(0,[z1,z326,z3,z4,z5,z567])],[(0,[z187,z2,z135,z4,z5,z18]),(0,[z1,z2,z3,z4,z138,z158]),(0,[z1,z2,z296,z4,z5,z200])],[(0,[z1,z203,z3,z4,z5,z18]),(0,[z231,z3,z4,z5,z178,z9])],[(0,[z1,z2,z3,z4,z5,z18]),(0,[z966,z304,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z713,z9]),(0,[z1,z2,z949,z4,z5,z18])],[(0,[z209,z2,z43,z4,z5,z18]),(0,[z1,z2,z1082,z3,z4,z5]),(0,[z1,z2,z1083,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1084]),(0,[z1,z2,z3,z4,z5,z1085]),(0,[z1,z139,z3,z4,z5,z29]),(0,[z63,z1,z3,z4,z701,z5]),(0,[z1,z2,z3,z319,z5,z6])],[(0,[z1,z2,z48,z482,z5,z9]),(0,[z1,z3,z4,z5,z9,z931]),(0,[z888,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1086,z9]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z51,z2,z3,z4,z80,z6]),(0,[z1,z2,z3,z4,z257,z39]),(0,[z1,z2,z1088,z4,z5,z9]),(0,[z1,z2,z442,z4,z32,z9])],[(0,[z1,z2,z1089,z4,z5,z9]),(0,[z1,z2,z1090,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1091]),(0,[z1,z2,z3,z4,z68,z427]),(0,[z1,z2,z3,z5,z386,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1092]),(0,[z0,z756,z3,z4,z5,z9]),(0,[z105,z2,z142,z4,z5,z9]),(0,[z1,z2,z3,z4,z1093,z9]),(0,[z1,z2,z3,z4,z5,z718]),(0,[z122,z2,z127,z4,z5,z9]),(0,[z1,z2,z3,z4,z1094,z9]),(0,[z1,z2,z1095,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1096]),(0,[z1,z2,z33,z4,z5,z18])],[(0,[z1,z2,z442,z4,z5,z9])],[(0,[z190,z11,z3,z4,z5,z9]),(0,[z105,z611,z3,z4,z5,z9]),(1,[z2,z873,z4,z5,z9]),(0,[z1097,z1,z2,z3,z4,z5]),(0,[z1,z198,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z58,z372]),(0,[z1,z2,z98,z4,z9,z40]),(0,[z1,z2,z3,z4,z5,z36]),(0,[z1,z2,z4,z278,z5,z18])],[(0,[z2,z11,z324,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1098]),(0,[z1,z2,z142,z4,z5,z39]),(0,[z1,z2,z3,z455,z5,z18]),(0,[z1,z2,z3,z4,z84,z6]),(0,[z1,z2,z3,z4,z21,z427])],[(0,[z1,z2,z1099,z4,z5,z9]),(0,[z1,z2,z1100,z4,z5,z9]),(0,[z1,z2,z16,z4,z104,z9])],[(0,[z1,z2,z3,z4,z5,z1101])],[(0,[z494,z1,z3,z221,z5,z9]),(0,[z52,z2,z3,z4,z5,z345]),(0,[z1,z126,z100,z4,z5,z6]),(0,[z1,z88,z3,z4,z238,z29]),(0,[z1,z2,z3,z4,z1102,z9]),(0,[z1,z1103,z3,z4,z5,z9])]],
   [[(0,[z1,z2,z211,z4,z5,z6]),(0,[z1,z2,z276,z4,z5,z18]),(0,[z1,z2,z98,z4,z75,z9]),(0,[z1,z2,z16,z4,z115,z9])],[(0,[z1,z2,z3,z4,z136,z6]),(0,[z1,z2,z1104,z4,z5,z9]),(0,[z1,z2,z3,z4,z286,z18]),(0,[z1,z2,z3,z4,z5,z1105]),(0,[z1,z2,z3,z4,z5,z1106]),(0,[z1,z2,z3,z4,z5,z1107]),(0,[z1,z2,z3,z4,z459,z248])],[(0,[z1,z103,z3,z163,z5,z232]),(0,[z1,z2,z54,z44,z5,z6]),(0,[z1108,z2,z3,z4,z5,z9])],[(0,[z1,z231,z3,z4,z5,z9]),(0,[z1,z2,z3,z1109,z5,z9]),(0,[z87,z2,z3,z4,z5,z718]),(0,[z1,z2,z54,z854,z5,z9]),(0,[z1,z2,z4,z278,z5,z36])],[(0,[z67,z1,z3,z4,z41,z9]),(0,[z1,z440,z3,z4,z5,z270]),(0,[z1,z2,z3,z4,z1110,z9]),(0,[z1,z2,z3,z37,z822,z9])],[(0,[z8,z2,z3,z110,z5,z267]),(0,[z2,z3,z4,z5,z894,z9]),(0,[z304,z2,z3,z4,z5,z18]),(0,[z317,z1,z456,z4,z5,z9]),(0,[z1,z450,z3,z4,z85,z9]),(0,[z1,z2,z3,z4,z251,z6])],[(0,[z1,z1111,z3,z4,z5,z9]),(0,[z1,z2,z1112,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1113]),(0,[z1,z2,z3,z4,z58,z114]),(0,[z1,z2,z48,z61,z5,z158]),(0,[z1,z2,z3,z263,z5,z18]),(0,[z1,z3,z4,z5,z9,z971])],[(0,[z1,z2,z3,z4,z894,z9]),(0,[z1,z2,z3,z4,z1114,z9])]],
   [[(0,[z305,z2,z3,z4,z5,z9]),(0,[z485,z11,z3,z4,z5,z9]),(0,[z7,z2,z3,z57,z5,z409]),(0,[z1,z2,z1076,z142,z4,z9]),(0,[z1,z126,z100,z4,z5,z534]),(0,[z1,z2,z4,z318,z5,z18]),(0,[z1,z2,z33,z148,z4,z9])],[(0,[z1,z440,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z1115]),(0,[z1,z2,z4,z318,z152,z9]),(0,[z1116,z2,z3,z4,z5,z9]),(0,[z1,z2,z283,z4,z32,z9]),(0,[z1,z2,z3,z4,z5,z1117]),(0,[z1,z2,z33,z4,z5,z22])],[(0,[z1,z463,z3,z4,z5,z9]),(0,[z1,z11,z3,z4,z286,z9]),(0,[z1,z2,z256,z3,z4,z5]),(0,[z1,z2,z1118,z142,z4,z9])],[(0,[z1,z2,z3,z4,z1119,z9]),(0,[z1,z2,z66,z4,z131,z9]),(0,[z1,z2,z3,z4,z5,z1120])],[(0,[z7,z2,z3,z57,z5,z18]),(0,[z1,z2,z3,z4,z5,z1121]),(0,[z52,z1,z2,z3,z4,z286]),(0,[z1,z88,z3,z4,z5,z844]),(0,[z1,z2,z3,z5,z18,z643])],[(0,[z1,z2,z3,z4,z5,z1122]),(0,[z1,z2,z224,z133,z4,z9]),(0,[z1,z203,z3,z4,z5,z6]),(0,[z1,z2,z283,z4,z5,z9]),(0,[z1,z2,z3,z4,z1123,z9]),(0,[z1,z2,z16,z652,z4,z9]),(0,[z1,z2,z3,z4,z945,z6]),(0,[z1,z2,z3,z4,z9,z739])],[(0,[z1,z2,z4,z1124,z5,z9]),(0,[z1125,z1,z2,z3,z4,z5]),(0,[z87,z231,z3,z4,z5,z9]),(0,[z1,z939,z101,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1126]),(0,[z1,z2,z3,z4,z730,z9]),(0,[z2,z3,z4,z5,z9,z988]),(0,[z1,z2,z3,z4,z341,z64])],[(0,[z1,z2,z339,z324,z3,z4]),(0,[z1,z2,z3,z4,z5,z464]),(0,[z1,z2,z3,z4,z238,z9]),(0,[z1,z2,z148,z3,z4,z286]),(0,[z63,z1,z2,z397,z3,z4]),(0,[z1,z2,z3,z4,z1127,z9])]],
   [[(0,[z1,z2,z90,z4,z131,z9]),(0,[z1,z2,z3,z4,z5,z1128]),(0,[z1,z2,z397,z3,z4,z9])],[(0,[z1,z2,z1129,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1130]),(0,[z1,z2,z55,z4,z5,z427]),(0,[z395,z2,z3,z4,z5,z345]),(0,[z1,z2,z148,z3,z4,z39])],[(0,[z1,z1131,z3,z4,z5,z9]),(0,[z51,z2,z3,z4,z80,z81]),(0,[z1,z126,z4,z605,z5,z9]),(0,[z83,z153,z3,z221,z5,z9]),(0,[z1,z2,z127,z4,z84,z9]),(0,[z1,z2,z108,z3,z4,z286]),(0,[z1,z2,z3,z35,z37,z6]),(0,[z1,z2,z1009,z4,z5,z18])],[(0,[z1,z2,z16,z4,z636,z9]),(0,[z83,z1,z3,z221,z84,z9]),(0,[z246,z2,z3,z4,z5,z18])],[(0,[z1,z2,z1132,z3,z4,z9]),(0,[z1,z2,z1133,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1134]),(0,[z1,z2,z3,z4,z5,z210]),(0,[z1135,z2,z3,z4,z5,z9]),(0,[z1,z2,z1136,z4,z5,z9]),(0,[z1,z2,z3,z453,z5,z6]),(0,[z1,z2,z3,z5,z9,z850]),(0,[z392,z2,z3,z4,z5,z374])],[(0,[z1,z2,z1137,z4,z5,z9]),(0,[z52,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z85,z427]),(0,[z1,z3,z4,z1138,z5,z9]),(0,[z1,z2,z3,z512,z5,z18])],[(0,[z1,z2,z3,z4,z5,z1139]),(0,[z209,z2,z339,z43,z4,z9]),(0,[z1,z2,z1140,z3,z4,z5]),(0,[z1,z2,z4,z278,z5,z6])],[(0,[z25,z2,z3,z4,z216,z18]),(0,[z1,z2,z16,z4,z650,z9])]],
   [[(0,[z1,z2,z3,z320,z5,z6]),(0,[z1,z2,z20,z44,z5,z9]),(0,[z1,z2,z3,z4,z9,z1141]),(0,[z1,z2,z3,z4,z5,z1142])],[(0,[z209,z2,z256,z43,z4,z5]),(0,[z1,z2,z3,z4,z1143,z9]),(0,[z1,z2,z3,z4,z5,z1144]),(0,[z1,z2,z3,z4,z5,z1145]),(0,[z1,z2,z3,z4,z5,z1146]),(0,[z67,z1,z3,z4,z68,z9]),(0,[z1,z2,z3,z4,z5,z255]),(0,[z1,z2,z4,z5,z9,z860])],[(1,[z756,z3,z4,z5,z9]),(0,[z559,z65,z3,z4,z5,z9]),(0,[z1,z88,z184,z3,z4,z5]),(0,[z1,z2,z1147,z4,z5,z9])],[(0,[z1,z2,z3,z4,z761,z9]),(0,[z1,z2,z146,z4,z5,z17]),(0,[z1,z967,z3,z4,z5,z9])],[(0,[z1148,z304,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z286,z6]),(0,[z1,z2,z970,z4,z5,z9])],[(0,[z1,z2,z90,z4,z5,z6]),(0,[z1,z2,z3,z4,z649,z21]),(0,[z1,z2,z1149,z3,z4,z9]),(0,[z1,z2,z3,z4,z5,z1150]),(0,[z1,z2,z98,z4,z169,z9]),(0,[z1,z2,z31,z3,z32,z18])],[(0,[z1,z2,z3,z4,z5,z1151]),(0,[z1,z2,z1152,z3,z4,z5]),(0,[z1,z2,z3,z4,z58,z18]),(0,[z63,z246,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z138,z9]),(0,[z1,z2,z296,z4,z5,z22]),(0,[z984,z2,z3,z4,z5,z6])],[(0,[z1,z65,z3,z4,z286,z9]),(0,[z1153,z1,z2,z3,z4,z5])]],
   [[(0,[z304,z2,z3,z4,z5,z6]),(0,[z2,z1154,z3,z4,z5,z9])],[(0,[z153,z2,z3,z4,z5,z9]),(0,[z1,z2,z1155,z4,z5,z9]),(0,[z1,z88,z3,z4,z5,z189]),(0,[z1,z2,z142,z4,z5,z9]),(0,[z250,z2,z135,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1156]),(0,[z87,z2,z3,z4,z5,z380]),(0,[z1,z2,z54,z44,z5,z15]),(0,[z1,z2,z148,z3,z4,z739])],[(0,[z209,z2,z224,z43,z4,z9]),(0,[z1,z198,z66,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1157]),(0,[z1,z2,z3,z4,z5,z1158]),(0,[z1,z2,z3,z5,z116,z6])],[(0,[z1,z103,z3,z303,z5,z9]),(0,[z317,z1,z939,z4,z5,z9]),(0,[z1,z2,z4,z318,z5,z6]),(0,[z1,z2,z16,z4,z218,z9])],[(0,[z1,z2,z788,z4,z5,z9]),(0,[z1,z2,z1159,z4,z5,z9]),(0,[z1160,z2,z3,z4,z5,z9]),(0,[z1,z2,z4,z5,z17,z760])],[(0,[z1,z2,z3,z4,z5,z1161]),(0,[z1,z2,z3,z4,z5,z1162]),(0,[z83,z1,z3,z221,z5,z9]),(0,[z63,z1,z3,z4,z5,z12])],[(0,[z52,z10,z3,z4,z5,z178]),(0,[z122,z103,z3,z4,z5,z9]),(0,[z1,z2,z1163,z4,z5,z9])],[(0,[z7,z2,z3,z57,z5,z6]),(0,[z1148,z1,z2,z3,z4,z5]),(0,[z1164,z2,z3,z4,z5,z9]),(0,[z1,z100,z939,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1165]),(0,[z1,z2,z4,z5,z729,z9]),(0,[z1,z2,z998,z4,z5,z6])]],
   [[(0,[z1,z2,z66,z4,z136,z9]),(0,[z51,z2,z113,z4,z80,z9]),(0,[z1,z2,z3,z4,z5,z1166]),(0,[z1,z2,z3,z4,z166,z295]),(0,[z1,z2,z1147,z4,z286,z9])],[(0,[z209,z2,z324,z43,z4,z5]),(0,[z1,z2,z360,z44,z5,z9]),(0,[z1,z2,z133,z4,z5,z9]),(0,[z51,z2,z3,z4,z894,z9]),(0,[z1,z2,z108,z4,z318,z5]),(0,[z1,z2,z244,z4,z5,z547]),(0,[z800,z2,z3,z4,z5,z9])],[(0,[z105,z65,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z1167]),(0,[z1,z2,z1168,z3,z4,z9]),(0,[z1,z2,z1169,z3,z4,z5]),(0,[z1,z2,z3,z4,z166,z702]),(0,[z1,z2,z3,z4,z1170,z9]),(0,[z1,z2,z3,z4,z6,z817])],[(0,[z613,z2,z43,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1171]),(0,[z1,z2,z3,z4,z341,z6]),(0,[z1,z2,z3,z5,z18,z49])],[(0,[z1172,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1173,z9]),(0,[z1,z2,z3,z4,z5,z1174]),(0,[z1,z2,z3,z4,z5,z1175]),(0,[z1,z103,z3,z163,z5,z18])],[(0,[z1,z2,z90,z4,z136,z9]),(0,[z1176,z2,z3,z4,z5,z9])],[(0,[z25,z463,z3,z4,z216,z9]),(0,[z317,z1,z101,z4,z5,z18]),(0,[z83,z122,z3,z221,z5,z9]),(0,[z153,z2,z276,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1177])],[(0,[z1,z2,z3,z4,z1178,z9]),(0,[z1,z2,z3,z4,z5,z1179]),(0,[z440,z3,z4,z57,z5,z9]),(0,[z1,z2,z66,z4,z5,z270]),(0,[z1,z2,z3,z4,z5,z1180]),(0,[z1,z2,z54,z44,z5,z93])]],
   [[(0,[z1,z2,z3,z4,z5,z1181]),(0,[z1,z1045,z203,z3,z4,z5]),(0,[z122,z2,z3,z4,z84,z9]),(0,[z1,z432,z3,z4,z68,z9])],[(0,[z1182,z1,z2,z3,z4,z5]),(0,[z1,z198,z3,z4,z131,z9]),(0,[z1,z2,z142,z4,z5,z21]),(0,[z1,z2,z3,z1183,z5,z9]),(0,[z1,z2,z3,z4,z5,z1184])],[(0,[z25,z2,z3,z4,z216,z6]),(0,[z83,z1,z276,z221,z5,z9]),(0,[z1,z285,z4,z318,z85,z9]),(0,[z1,z2,z3,z300,z5,z6]),(0,[z1,z1185,z3,z4,z5,z9]),(0,[z1,z139,z3,z4,z5,z191])],[(0,[z105,z756,z3,z4,z5,z9]),(0,[z87,z2,z142,z4,z5,z293]),(0,[z1,z2,z1118,z3,z4,z9]),(0,[z52,z2,z362,z3,z4,z5]),(0,[z1,z2,z48,z61,z5,z9])],[(0,[z105,z2,z324,z3,z4,z5]),(0,[z1,z2,z324,z142,z4,z5]),(0,[z1186,z2,z3,z4,z5,z9]),(0,[z1,z2,z4,z5,z9,z1187]),(0,[z1,z2,z3,z4,z5,z64]),(0,[z2,z3,z4,z5,z9,z921])],[(0,[z1,z2,z66,z4,z5,z9]),(0,[z1,z2,z3,z4,z1188,z5]),(0,[z1051,z1,z203,z3,z4,z5]),(0,[z1,z2,z3,z4,z1189,z9]),(0,[z1,z2,z3,z4,z5,z1190]),(1,[z1,z2,z854,z5,z9]),(0,[z1,z2,z3,z4,z5,z1191])],[(0,[z1,z2,z4,z75,z152,z9]),(0,[z1,z2,z1027,z3,z4,z9]),(0,[z1,z2,z3,z4,z1192,z9]),(0,[z1,z2,z1193,z4,z5,z9])],[(0,[z1,z2,z1194,z4,z5,z9]),(0,[z1,z2,z3,z4,z1195,z9]),(0,[z1,z2,z3,z4,z5,z1196]),(0,[z1,z2,z3,z4,z1197,z5]),(0,[z1,z88,z2,z142,z4,z5]),(0,[z1,z2,z3,z4,z152,z9]),(0,[z1,z2,z939,z4,z5,z9])]],
   [[(0,[z0,z11,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1198,z5]),(0,[z1,z2,z3,z4,z1199,z9]),(0,[z1,z2,z1200,z4,z5,z9]),(0,[z1,z2,z3,z557,z5,z6]),(0,[z1,z2,z3,z4,z5,z1201]),(0,[z1,z2,z4,z75,z729,z9])],[(0,[z1,z2,z3,z4,z5,z1202]),(0,[z1,z2,z3,z4,z5,z1203]),(0,[z1,z2,z3,z4,z729,z9])],[(0,[z8,z2,z3,z19,z5,z9]),(0,[z1,z2,z3,z4,z5,z1204]),(0,[z1,z2,z3,z4,z5,z1205]),(1,[z1,z3,z4,z5,z844]),(0,[z1,z2,z328,z3,z4,z423])],[(0,[z1,z10,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1206,z5]),(0,[z1,z2,z3,z4,z5,z93]),(0,[z1,z1207,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z1208]),(0,[z1,z2,z3,z4,z1209,z9]),(0,[z1,z2,z4,z1210,z5,z9]),(0,[z1,z2,z1211,z4,z5,z9]),(0,[z1,z3,z4,z775,z5,z9]),(0,[z246,z3,z4,z5,z12,z9]),(0,[z1,z2,z442,z4,z5,z18])],[(0,[z1,z2,z873,z4,z5,z9]),(0,[z8,z2,z3,z736,z5,z9]),(0,[z1,z2,z3,z4,z5,z1212]),(0,[z1,z2,z397,z4,z17,z9])],[(0,[z1,z2,z3,z4,z131,z270]),(0,[z1,z2,z623,z44,z5,z9]),(0,[z1,z2,z48,z351,z5,z9])],[]],
   [[(0,[z1213,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z1214,z5,z9]),(0,[z1,z2,z3,z4,z5,z1215]),(0,[z153,z2,z3,z4,z5,z372]),(0,[z899,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z1216,z9]),(0,[z25,z2,z354,z3,z4,z9]),(0,[z1,z2,z3,z552,z5,z6]),(0,[z1,z1103,z3,z4,z5,z18])],[(0,[z122,z2,z3,z4,z5,z9]),(0,[z2,z873,z43,z4,z5,z9]),(0,[z1217,z1,z3,z4,z5,z9]),(0,[z2,z135,z873,z4,z5,z9]),(0,[z1,z2,z3,z4,z1218,z9]),(0,[z1,z2,z3,z4,z5,z1219]),(0,[z1,z2,z48,z4,z138,z9]),(0,[z1,z2,z98,z4,z75,z18]),(0,[z1,z2,z3,z4,z166,z739])],[(0,[z1,z2,z3,z4,z1220,z5]),(0,[z87,z2,z3,z4,z5,z595]),(0,[z1,z1221,z2,z3,z4,z5]),(0,[z52,z1,z2,z33,z4,z5]),(0,[z1,z2,z3,z4,z1222,z5]),(0,[z1,z2,z3,z4,z5,z1223]),(0,[z1,z2,z3,z4,z5,z1224]),(0,[z1,z910,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z131,z9]),(0,[z8,z2,z3,z110,z5,z9]),(0,[z1,z2,z1225,z4,z5,z9]),(0,[z1,z2,z3,z4,z1226,z9]),(0,[z83,z1,z3,z221,z5,z372]),(0,[z1,z2,z397,z3,z4,z427]),(0,[z1,z2,z3,z4,z1227,z9]),(0,[z1,z2,z442,z4,z5,z36]),(0,[z1,z2,z1228,z4,z5,z9])],[(0,[z105,z65,z3,z4,z5,z6]),(0,[z1,z2,z3,z421,z5,z6]),(0,[z1,z231,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z411,z6]),(1,[z1,z2,z4,z5,z760])],[(0,[z11,z3,z4,z292,z5,z9]),(0,[z1,z1229,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1230]),(0,[z1,z1059,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z18,z710])],[(0,[z1,z2,z3,z4,z1231,z9]),(0,[z661,z2,z3,z4,z216,z9])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 531) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 531).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1058).take 193) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1251)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [531, 527, 193] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 105).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 105).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 219).take 37).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [105, 114, 37] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

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

end PEqualNP.Outside.L_meta_38879

theorem PEqualNP.Outside.L_meta_38879 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38879.solve