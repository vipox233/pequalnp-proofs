import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41006

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4243122176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x01041856221b86e9#64 ++ 0x0004106158886e1b#64 ++ 0x033cf8fe223f8ffe#64 ++ 0x8c0cf3e3f888fe3f#64 : BitVec 256),
   (0x0c514b300ec5b172#64 ++ 0x0431452cc03b16c5#64 ++ 0x1cd34f303fc7f1fd#64 ++ 0xf4734d3cc0ff1fc7#64 : BitVec 256),
   (0x60a28dc0c368da3c#64 ++ 0x09828a37030da368#64 ++ 0xe0e38fc3c3f8fe3b#64 ++ 0xdf838e3f0f0fe3f8#64 : BitVec 256),
   (0xb703f00374006d80#64 ++ 0x12dc0fc00dd001b6#64 ++ 0xff03f003fc00fff7#64 ++ 0xfbfc0fc00ff003ff#64 : BitVec 256),
   (0xdbfc0003b9b60000#64 ++ 0x236ff0000ee6d800#64 ++ 0xfffc0003ffff002f#64 ++ 0xbffff0000ffffc00#64 : BitVec 256),
   (0xfefbe6a800000000#64 ++ 0x03fbef9aa0000000#64 ++ 0xfffffffc0000001f#64 ++ 0xe3fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [7, 12]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x033cf8fe223f8ffe 0x8c0cf3e3f888fe3f

def z1 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cd34f303fc7f1fd 0xf4734d3cc0ff1fc7

def z2 : W := mkw 0x2002858040405814 0x08800a1601010160 0x0003070000007000 0x40000c1c000001c0

def z3 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0e38fc3c3f8fe3b 0xdf838e3f0f0fe3f8

def z4 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff03f003fc00fff7 0xfbfc0fc00ff003ff

def z5 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffc0003ffff002f 0xbffff0000ffffc00

def z6 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfffffffc0000001f 0xe3fffffff0000000

def z7 : W := mkw 0x60a28dd0cfedfb7e 0x0d828a37433fb7ed 0xe0e38fc3fffffffb 0xdf838e3f0fffffff

def z8 : W := mkw 0x0100100220000480 0x0004004008800012 0x0300f00220008ff6 0x880c03c00880023f

def z9 : W := mkw 0xb603e00154006900 0x12d80f80055001a4 0xfc030001dc007001 0x73f00c00077001c0

def z10 : W := mkw 0x0401400004002100 0x0010050000100084 0x1c0340003c00f1f5 0xf0700d0000f003c7

def z11 : W := mkw 0x2002800040004800 0x00800a0001000120 0xe0038003c000fe33 0xdb800e000f0003f8

def z12 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1c134f303c07f1d4 0x60704d3cc0f01fc7

def z13 : W := mkw 0x00001854020986e9 0x000000615008261b 0x0020f8fe02388ffa 0x8c0083e3f808e23f

def z14 : W := mkw 0x9e59622800000000 0x02796588a0000000 0x1f3cf8fc0000001e 0xa07cf3e3f0000000

def z15 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x00000002223f8fe0 0x0c0000000888fe3f

def z16 : W := mkw 0xfefbe00000000000 0x03fbef8000000000 0xfffff0000000001f 0xe3ffffc000000000

def z17 : W := mkw 0x97057017341325c1 0x125c15c05cd04c97 0x1f1c703c3c0701c4 0x207c71c0f0f01c07

def z18 : W := mkw 0x01041003fdb66d80 0x300410400ff6d9b6 0x00000003ffffffe0 0x1c0000000fffffff

def z19 : W := mkw 0x40a00dc08368923c 0x09028037020da248 0x00e00fc003f80008 0x0403803f000fe000

def z20 : W := mkw 0x0000100044006d80 0x10000040011001b6 0x000000000000ffc0 0x00000000000003ff

def z21 : W := mkw 0xfefbeee802088228 0x03fbefbba0082208 0xfffffffe02388e3f 0xeffffffff808e238

def z22 : W := mkw 0x0000084002088228 0x0000002100082208 0x002088c202388e3a 0x8c0082230808e238

def z23 : W := mkw 0x61a69dd6e37bdefd 0x09869a775b8def7b 0xe3ffffffe3ffffff 0xdf8fffffff8fffff

def z24 : W := mkw 0x0000100000000480 0x0000004000000012 0x0000f00000008fd0 0x000003c00000023f

def z25 : W := mkw 0x0104000220120000 0x0004100008804800 0x033c0002223f002e 0x8c0cf0000888fc00

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c30f0000000019 0xc0030c3c00000000

def z27 : W := mkw 0x0c51422000000000 0x0031450880000000 0x1c10403000000004 0x20704100c0000000

def z28 : W := mkw 0x9300000330000000 0x024c00000cc00000 0x1f0000003c000004 0x207c000000f00000

def z29 : W := mkw 0x01040842221a8228 0x0004102108886a08 0x033c88c2223f8e3e 0x8c0cf2230888fe38

def z30 : W := mkw 0x0000081002018060 0x0000002040080601 0x00104830220781fc 0x84004120c0881e07

def z31 : W := mkw 0x0d555b762edfb7fb 0x0435556dd8bb7edf 0x1ffffffe3fffffff 0xfc7ffffff8ffffff

def z32 : W := mkw 0x60a29dd4c369defd 0x09828a77530da77b 0xe0e3ffffc3f8fffb 0xdf838fffff0fe3ff

def z33 : W := mkw 0xb703f6ab74006d80 0x12dc0fdaadd001b6 0xff03fffffc00fff7 0xfbfc0ffffff003ff

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0x033cf8fc0000001e 0x800cf3e3f0000000

def z35 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xfc030003fc00ffe1 0x7bf00c000ff003ff

def z36 : W := mkw 0xf2aaa4c8c1284a0c 0x0bcaaa932304a128 0xe32cb0cfc0380e02 0x0b8cb2c33f00e038

def z37 : W := mkw 0xf3a28dc3f368da3c 0x0bce8a370fcda368 0xffe38fc3fff8fe3f 0xffff8e3f0fffe3f8

def z38 : W := mkw 0x00001854020986e9 0x000000615008261b 0x0000f8fc00008fd0 0x000003e3f000023f

def z39 : W := mkw 0xdaf8000199a40000 0x236be00006669000 0xfcc00001ddc00001 0x33f3000007770000

def z40 : W := mkw 0xfffff003fdb66d80 0x33ffffc00ff6d9b6 0xfffff003ffffffff 0xffffffc00fffffff

def z41 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff3ff8fffc00ffff 0xfbfcffe3fff003ff

def z42 : W := mkw 0x9b5c000338960000 0x226d70000ce25800 0x1f1c00003c070004 0x207c700000f01c00

def z43 : W := mkw 0xfbfe8dc3fbfeda3c 0x2beffa370feffb68 0xffff8fc3fffffe3f 0xfffffe3f0ffffff8

def z44 : W := mkw 0x60a28cc0c328ca2c 0x09828a33030ca328 0xe02088c3c2388e3a 0x8f8082230f08e238

def z45 : W := mkw 0xd3ac0003b1320000 0x234eb0000ec4c800 0xff2c0003fc380027 0xbbfcb0000ff0e000

def z46 : W := mkw 0x05055b76265bb7fb 0x0414156dd8996edf 0x033ffffe223ffffe 0xcc0cfffff888ffff

def z47 : W := mkw 0x0c5143300cc53152 0x0431450cc03314c5 0x1cd347303dc771c5 0x70734d1cc0f71dc7

def z48 : W := mkw 0xffffe6aa20120000 0x03ffff9aa8804800 0xfffffffe223f003f 0xeffffffff888fc00

def z49 : W := mkw 0x0850000008840000 0x0021400000221000 0x1cd000003fc7002d 0xb473400000ff1c00

def z50 : W := mkw 0xd3ac0003b1320000 0x234eb0000ec4c800 0xe32c0003c0380002 0x0b8cb0000f00e000

def z51 : W := mkw 0x00000dc00248923c 0x0800003700092248 0x00000fc000000000 0x0000003f00000000

def z52 : W := mkw 0x0850023008850042 0x04214008c0221401 0x0010003000070000 0x00004000c0001c00

def z53 : W := mkw 0xfefbe6e8c1284a0c 0x0bfbef9ba304a128 0xffffffffc0380e1f 0xebffffffff00e038

def z54 : W := mkw 0x01041046201a0689 0x000410411880681a 0x032cf0ce20388ff6 0x880cb3c33880e23f

def z55 : W := mkw 0x4cf14ff08fedb37e 0x0d33c53fc23fb6cd 0x1cf34ff03ffff1fd 0xf473cd3fc0ffffc7

def z56 : W := mkw 0x2403e6a800000000 0x00900f9aa0000000 0x0003fffc00000010 0x40000ffff0000000

def z57 : W := mkw 0xfefbefe8c368da3c 0x0bfbefbfa30da368 0xffffffffc3f8fe3f 0xffffffffff0fe3f8

def z58 : W := mkw 0xb707f00374126d80 0x12dc1fc00dd049b6 0xff3ff003fe3fffff 0xfffcffc00ff8ffff

def z59 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffcf8ffffff003f 0xbffff3e3fffffc00

def z60 : W := mkw 0x68fe8dc0cbfeda3c 0x29a3fa37032ffb68 0xe0ff8fc3c3fffe3b 0xdf83fe3f0f0ffff8

def z61 : W := mkw 0x01041016201304c1 0x0004104058804c13 0x031c703c200701c4 0x000c71c0f0801c07

def z62 : W := mkw 0x60a28580c1605814 0x09828a1603058160 0xe0c30701c1c07001 0x53830c1c070701c0

def z63 : W := mkw 0x4cfd4b308ff7b172 0x2533f52cc23fdec5 0x1cff4f303ffff1fd 0xf473fd3cc0ffffc7

def z64 : W := mkw 0xb603f00044006d80 0x12d80fc0011001b6 0xff03f0000000ffd7 0xe3fc0fc0000003ff

def z65 : W := mkw 0x60a284c0c1284a0c 0x09828a130304a128 0xe0e080c3c3f80e2b 0x9f8382030f0fe038

def z66 : W := mkw 0x40a00dc08368923c 0x09028037020da248 0x00e08fc203f88e3a 0x8c03823f080fe238

def z67 : W := mkw 0x2403e6a800000000 0x00900f9aa0000000 0x033ffffc0000001e 0xc00cfffff0000000

def z68 : W := mkw 0xfffffefe221b86e9 0x03fffffbf8886e1b 0xfffffffe223f8fff 0xeffffffff888fe3f

def z69 : W := mkw 0x60a2848000000000 0x01828a1200000000 0xe0e38fc00000001b 0xc3838e3f00000000

def z70 : W := mkw 0x00000940c368da3c 0x08000025030da368 0x00000003c3f8fe20 0x1c0000000f0fe3f8

def z71 : W := mkw 0xfffbffbb7ec5fdf2 0x17ffeffeedfb17f7 0xffffffffffc7ffff 0xffffffffffff1fff

def z72 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x031c703e223f8fe4 0x0c0c71c0f888fe3f

def z73 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfcc3070000000001 0x63f30c1c00000000

def z74 : W := mkw 0x0401622800000000 0x00100588a0000000 0x0000703c00000000 0x000001c0f0000000

def z75 : W := mkw 0x61a69cd6e33bceed 0x09869a735b8cef3b 0xe33cf8ffe23f8ffe 0x8f8cf3e3ff88fe3f

def z76 : W := mkw 0x000009100641b172 0x04000024401906c5 0x000000000000f1c0 0x00000000000003c7

def z77 : W := mkw 0xf7a3fdc3f768ffbc 0x1bde8ff70fdda3fe 0xffe3ffc3fff8ffff 0xffff8fff0fffe3ff

def z78 : W := mkw 0x6cf3cfb0cfe5f976 0x0db3cf3ec33f97e5 0xfcd34f31ffc7f1fd 0xf7f34d3cc7ff1fc7

def z79 : W := mkw 0x2403f00044006d80 0x10900fc0011001b6 0x0003f0000000ffd0 0x40000fc0000003ff

def z80 : W := mkw 0x0c515b740ecdb7fb 0x0431456dd03b36df 0x1cd3fffc3fc7fffd 0xf4734ffff0ff1fff

def z81 : W := mkw 0x0100100374006d80 0x100400400dd001b6 0x0300f003fc00fff6 0x980c03c00ff003ff

def z82 : W := mkw 0xdef9422000000000 0x037be50880000000 0xffff4f300000001f 0xe3fffd3cc0000000

def z83 : W := mkw 0xdaf8000008840000 0x036be00000221000 0xfffc00003fc7002f 0xb7fff00000ff1c00

def z84 : W := mkw 0x085009100ec5b172 0x04214024403b16c5 0x1cd000003fc7f1ed 0xb473400000ff1fc7

def z85 : W := mkw 0x01041046201a0689 0x000410411880681a 0x032cb0ce00380e02 0x080cb2c33800e038

def z86 : W := mkw 0x0c5143200cc43112 0x0431450c803310c4 0x1cc307001dc07001 0x70730c1c007701c0

def z87 : W := mkw 0xdafc000199b60000 0x236bf0000666d800 0xfcfc0001dfff0009 0x37f3f000077ffc00

def z88 : W := mkw 0x05055856261ba7e9 0x0014156158986e9f 0x1f3ff8fe3e3fffff 0xfc7cffe3f8f8ffff

def z89 : W := mkw 0x49fc1efe221b86e9 0x0127f07bf8886e1b 0x03fcfffe223f8ffe 0x8c0ff3fff888fe3f

def z90 : W := mkw 0x40a0000081200000 0x0102800002048000 0x00e0000003f80008 0x04038000000fe000

def z91 : W := mkw 0x6cf3cff0cfedfb7e 0x0db3cf3fc33fb7ed 0xfcf3cff3ffffffff 0xfff3cf3fcfffffff

def z92 : W := mkw 0x0104100620120481 0x0004104018804812 0x030c300c00000000 0x000c30c030000000

def z93 : W := mkw 0x0d555b362ed7b5f3 0x0435556cd8bb5ed7 0x1fdf7f3c3fc7f1fd 0xf47f7dfcf0ff1fc7

def z94 : W := mkw 0x60a2848000000000 0x01828a1200000000 0xe02080c000000002 0x0380820300000000

def z95 : W := mkw 0x04014b300641b172 0x0410052cc01906c5 0x00034f300000f1d0 0x40000d3cc00003c7

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000800200008e32 0x8800020008000238

def z97 : W := mkw 0x60a284c0c1284a0c 0x09828a130304a128 0xe02080c3c0380e02 0x0b8082030f00e038

def z98 : W := mkw 0xdbfc0857bbbf8269 0x236ff0215eeefe09 0xfffc08ffffff002f 0xbffff023fffffc00

def z99 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe3ffffffc3f8fe3f 0xdf8fffffff0fe3f8

def z100 : W := mkw 0x01041056201b06c9 0x0004104158806c1b 0x033cf0fe203f0fc6 0x080cf3c3f880fc3f

def z101 : W := mkw 0xd3a00003b1200000 0x034e80000ec48000 0xffe00003fff8002f 0xbfff80000fffe000

def z102 : W := mkw 0x0000084002088228 0x0000002100082208 0x033cf8fe02388e3e 0x8c0cf3e3f808e238

def z103 : W := mkw 0xf3aea48bb1320000 0x23ceba922ec4c800 0xe32cb0cfc0380002 0x0b8cb2c33f00e000

def z104 : W := mkw 0x0000000154006900 0x10000000055001a4 0x00000001dc007000 0x10000000077001c0

def z105 : W := mkw 0x60a2848000000000 0x01828a1200000000 0xe3fffffc0000001f 0xc38ffffff0000000

def z106 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfcc00003ffff0021 0x3ff300000ffffc00

def z107 : W := mkw 0x64a3cff0c769fb7e 0x0d928f3fc31da7ed 0xe0e3cff3c3f8fffb 0xdf838f3fcf0fe3ff

def z108 : W := mkw 0x000009100ec5b172 0x04000024403b16c5 0x000000003fc7f1e0 0x1400000000ff1fc7

def z109 : W := mkw 0x0100100220000480 0x0004004008800012 0x03007000200001c4 0x000c01c000800007

def z110 : W := mkw 0x2403c00044006900 0x00900f00011001a4 0xfc03c003fc00fff7 0xfbf00f000ff003ff

def z111 : W := mkw 0x0401400000000000 0x0010050000000000 0x1c03400000000015 0xe0700d0000000000

def z112 : W := mkw 0x000009408368923c 0x08000025020da248 0x0000000003f80000 0x04000000000fe000

def z113 : W := mkw 0x00001854020986e9 0x000000615008261b 0x033cf8fc00008fde 0x800cf3e3f000023f

def z114 : W := mkw 0x40a00940c368da3c 0x09028025030da368 0xe0e00003c3f8fe2b 0x9f8380000f0fe3f8

def z115 : W := mkw 0x0000090002409030 0x0000002400090240 0x0000000003c0f020 0x14000000000f03c0

def z116 : W := mkw 0xfefbeff8cfedfb7e 0x0ffbefbfe33fb7ed 0xffffffffffffffff 0xffffffffffffffff

def z117 : W := mkw 0x40a0000081200000 0x0102800002048000 0xe0e00003c3f8002b 0x9f8380000f0fe000

def z118 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x0000f8fe223f8ff0 0x0c0003e3f888fe3f

def z119 : W := mkw 0x01041956e37bdefd 0x080410655b8def7b 0x033cf8ffe3fffffe 0x9c0cf3e3ff8fffff

def z120 : W := mkw 0x48fc000089b60000 0x2123f0000226d800 0x00fc000003ff0008 0x0403f000000ffc00

def z121 : W := mkw 0x60a2848081200000 0x01828a1202048000 0xe0e38fc3c3f8003b 0xdf838e3f0f0fe000

def z122 : W := mkw 0x20028dc04248da3c 0x08800a3701092368 0x00238fc20238fe3a 0xcc008e3f0808e3f8

def z123 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cc307003fc7f1e1 0x74730c1c00ff1fc7

def z124 : W := mkw 0x9f5d723e201304c1 0x027d75c8f8804c13 0x1f1c703c200701c4 0x207c71c0f0801c07

def z125 : W := mkw 0x2403cff04649fb7e 0x0c900f3fc11927ed 0x0003cff00000ffd0 0x40000f3fc00003ff

def z126 : W := mkw 0x01041846221a86a9 0x0004106118886a1a 0x032cb8ce02388e3a 0x8c0cb2e33808e238

def z127 : W := mkw 0x0000000004002100 0x0000000000100084 0x000000003c00f1e0 0x1000000000f003c7

def z128 : W := mkw 0xdffd4b33bff7b172 0x277ff52cceffdec5 0xffff4f33fffff1ff 0xfffffd3ccfffffc7

def z129 : W := mkw 0x9300000330000000 0x024c00000cc00000 0xff000003fc000027 0xbbfc00000ff00000

def z130 : W := mkw 0x0104000220120000 0x0004100008804800 0x033cf8fe223f003e 0x8c0cf3e3f888fc00

def z131 : W := mkw 0x0c5142300c852142 0x04314508c0321485 0x1c1040303c0701c4 0x20704100c0f01c07

def z132 : W := mkw 0x60a28580c1605814 0x09828a1603058160 0xe0c38703c1c0fe33 0xdb830e1c0f0703f8

def z133 : W := mkw 0x6df7dff6efffffff 0x0db7df7fdbbfffff 0xffffffffffffffff 0xffffffffffffffff

def z134 : W := mkw 0x9a58000118840000 0x2269600004621000 0x1c0000001c000000 0x2070000000700000

def z135 : W := mkw 0x60a284c0c1284a0c 0x09828a130304a128 0xe02380c3c038fe33 0xdb808e030f00e3f8

def z136 : W := mkw 0x9e5962380c852142 0x06796588e0321485 0x1f1c703c3c0701c4 0x207c71c0f0f01c07

def z137 : W := mkw 0x00000940c368da3c 0x08000025030da368 0x00c30f03c3f8fe39 0xdc030c3c0f0fe3f8

def z138 : W := mkw 0xdef966a800000000 0x037be59aa0000000 0x1ffc7ffc0000000c 0x207ff1fff0000000

def z139 : W := mkw 0x01040003b9b60000 0x200410000ee6d800 0x00000003ffff0020 0x1c0000000ffffc00

def z140 : W := mkw 0x0000081002018060 0x0000002040080601 0x00004830000081d0 0x00000120c0000207

def z141 : W := mkw 0xdaf8000199a40000 0x236be00006669000 0xfcd00001ffc7002d 0xb7f3400007ff1c00

def z142 : W := mkw 0x01041016201304c1 0x0004104058804c13 0x033cf8fc200701de 0x800cf3e3f0801c07

def z143 : W := mkw 0xfefbe6a954006900 0x13fbef9aa55001a4 0xfffffffddc00701f 0xf3fffffff77001c0

def z144 : W := mkw 0xffffe6abb9b60000 0x23ffff9aaee6d800 0xffff0703ffff002f 0xfffffc1c0ffffc00

def z145 : W := mkw 0xd3ac0003b1320000 0x234eb0000ec4c800 0xe3ec0003c3f8002b 0x9f8fb0000f0fe000

def z146 : W := mkw 0xfefbefb80641b172 0x07fbefbee01906c5 0xfffffffc0000f1df 0xe3fffffff00003c7

def z147 : W := mkw 0x0c51422000000000 0x0031450880000000 0x1cd34f300000001d 0xe0734d3cc0000000

def z148 : W := mkw 0x01001842220886a8 0x000400610888221a 0x0320f8c222388ffe 0x8c0c83e30888e23f

def z149 : W := mkw 0x20028940c368da3c 0x08800a25030da368 0xe0038003c3f8fe33 0xdf800e000f0fe3f8

def z150 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xff3cf0fc00000006 0x23fcf3c3f0000000

def z151 : W := mkw 0xdffd4233bdb72142 0x277ff508cef6dc85 0xfffc4033ffff01ef 0xbffff100cffffc07

def z152 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0e08fc3c3f80e0a 0x0f83823f0f0fe038

def z153 : W := mkw 0x48f806a800000000 0x0123e01aa0000000 0x00fc0ffc00000008 0x0003f03ff0000000

def z154 : W := mkw 0xfefbefb80ec5b172 0x07fbefbee03b16c5 0xfffffffc3fc7f1ff 0xf7fffffff0ff1fc7

def z155 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x033c0002223f8fee 0x8c0cf0000888fe3f

def z156 : W := mkw 0x0501500224002580 0x0014054008900096 0x1f03f0023c00fff7 0xf87c0fc008f003ff

def z157 : W := mkw 0x0000090002409030 0x0000002400090240 0x00c30f0003c0f039 0xd4030c3c000f03c0

def z158 : W := mkw 0x00000950cfedfb7e 0x0c000025433fb7ed 0x00000003ffffffe0 0x1c0000000fffffff

def z159 : W := mkw 0xb703f9037640fdb0 0x12dc0fe40dd903f6 0xffc3ff03ffc0ffff 0xffff0ffc0fff03ff

def z160 : W := mkw 0xf2aaa48800000000 0x03caaa9220000000 0xe32cb0cc00000002 0x038cb2c330000000

def z161 : W := mkw 0xffffe6abb9b60000 0x23ffff9aaee6d800 0xffffffffffff003f 0xfffffffffffffc00

def z162 : W := mkw 0xfefbe6a999a40000 0x23fbef9aa6669000 0xfffffffdddc0001f 0xf3fffffff7770000

def z163 : W := mkw 0xfefbe6a881200000 0x03fbef9aa2048000 0xffffffffc3f8003f 0xffffffffff0fe000

def z164 : W := mkw 0x20028dc04248da3c 0x08800a3701092368 0x00038fc00000fe10 0x40000e3f000003f8

def z165 : W := mkw 0xb603e00000000000 0x02d80f8000000000 0xff03f00000000017 0xe3fc0fc000000000

def z166 : W := mkw 0xd2a8000000000000 0x034aa00000000000 0xe32c000000000002 0x038cb00000000000

def z167 : W := mkw 0x085c000008960000 0x2021700000225800 0x001c000000070000 0x0000700000001c00

def z168 : W := mkw 0x000006a800000000 0x0000001aa0000000 0x00000ffc00000000 0x0000003ff0000000

def z169 : W := mkw 0x40a0090083609030 0x01028024020d8240 0xe0e30f03c3f8f03b 0xdf838c3c0f0fe3c0

def z170 : W := mkw 0x48f8000000000000 0x0123e00000000000 0x00fc000000000008 0x0003f00000000000

def z171 : W := mkw 0x2403f6a844006d80 0x10900fdaa11001b6 0x0003fffc0000ffd0 0x40000ffff00003ff

def z172 : W := mkw 0x64a3efe8c368da3c 0x09928fbfa30da368 0xe0e3ffffc3f8fe3b 0xdf838fffff0fe3f8

def z173 : W := mkw 0xb707f857761befe9 0x12dc1fe15dd86fbf 0xff3ff8fffe3fffff 0xfffcffe3fff8ffff

def z174 : W := mkw 0xb302b00370004c80 0x12cc0ac00dc00132 0xe303b003c000fe33 0xdb8c0ec00f0003f8

def z175 : W := mkw 0x00040854021b8269 0x0000102150086e09 0x003c48fc223f81fc 0x8400f123f088fe07

def z176 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xffec0003ddf80003 0x3bffb0000f77e000

def z177 : W := mkw 0x0100000220000000 0x0004000008800000 0x0300000220000026 0x880c000008800000

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0x000300000000f031 0xd0000c00000003c0

def z179 : W := mkw 0xb302b00374006d80 0x12cc0ac00dd001b6 0xe300b003fc00ffe2 0x1b8c02c00ff003ff

def z180 : W := mkw 0xb703fdc37648ffbc 0x1adc0ff70dd923fe 0xff03ffc3fc00fff7 0xfbfc0fff0ff003ff

def z181 : W := mkw 0x0c514b300641b172 0x0431452cc01906c5 0x1cd34f300000f1dd 0xe0734d3cc00003c7

def z182 : W := mkw 0x01041956e37bdefd 0x080410655b8def7b 0x00000003e3ffffe0 0x1c0000000f8fffff

def z183 : W := mkw 0xfffbf6ab74006d80 0x13ffefdaadd001b6 0xfffffffffc00ffff 0xfbfffffffff003ff

def z184 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0c30703c3f8fe21 0x5f830c1c0f0fe3f8

def z185 : W := mkw 0x0c5143200cc43112 0x0431450c803310c4 0x1cd34f301dc0701d 0xf0734d3cc07701c0

def z186 : W := mkw 0x40a0000000000000 0x0102800000000000 0xe0e000000000000b 0x8383800000000000

def z187 : W := mkw 0xb703f00334002580 0x12dc0fc00cd00096 0xff03f0003c0001d7 0xe3fc0fc000f00007

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x001000002207002c 0x8400400000881c00

def z189 : W := mkw 0x010419562edfb7fb 0x0404106558bb7edf 0x000000023fffffe0 0x1c00000008ffffff

def z190 : W := mkw 0x01041816221384e1 0x0004106058884e13 0x031c783c220781fc 0x840c71e0f0881e07

def z191 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x00d34f3003c7f1d8 0x44034d3cc00f1fc7

def z192 : W := mkw 0x0100100374006d80 0x100400400dd001b6 0x00000003fc00ffe0 0x180000000ff003ff

def z193 : W := mkw 0x2507fefe221b86e9 0x00941ffbf8886e1b 0x033ffffe223f8ffe 0xcc0cfffff888fe3f

def z194 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cd30f301fc77009 0x74734c3cc07f1dc0

def z195 : W := mkw 0x2403fefc020986e9 0x00900ffbf008261b 0x0003fffc00008fd0 0x40000ffff000023f

def z196 : W := mkw 0x48f0000089a40000 0x0123c00002269000 0xfcf00003ffff002f 0xbff3c0000ffffc00

def z197 : W := mkw 0x2403f00044006d80 0x10900fc0011001b6 0x1c03f0003c00fff5 0xf0700fc000f003ff

def z198 : W := mkw 0xb703f9137ec5fdf2 0x16dc0fe44dfb17f7 0xff03f003ffc7fff7 0xfffc0fc00fff1fff

def z199 : W := mkw 0x0d515b337ec5fdf2 0x1435456ccdfb17f7 0x1cd34f33ffc7fffd 0xfc734d3ccfff1fff

def z200 : W := mkw 0xb703f8577609efe9 0x12dc0fe15dd827bf 0xff03f8fffc00fff7 0xfbfc0fe3fff003ff

def z201 : W := mkw 0xdaf8000000000000 0x036be00000000000 0xfcc0000000000001 0x23f3000000000000

def z202 : W := mkw 0x41a41856a33b86e9 0x010690615a8cee1b 0xe3fcf8ffe3ff8fff 0x9f8ff3e3ff8ffe3f

def z203 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x002088c2223f8ffa 0x8c0082230888fe3f

def z204 : W := mkw 0xdaf8000000000000 0x036be00000000000 0xfffcf8fc0000001f 0xa3fff3e3f0000000

def z205 : W := mkw 0x20028dc0c368da3c 0x08800a37030da368 0x00038fc3c3f8fe30 0x5c000e3f0f0fe3f8

def z206 : W := mkw 0xdbfc1857bbbf86e9 0x236ff0615eeefe1b 0xfffcf8ffffff8fff 0xbffff3e3fffffe3f

def z207 : W := mkw 0xfefbefb80ec5b172 0x07fbefbee03b16c5 0xfcd34f303fc7f1fd 0xf7f34d3cc0ff1fc7

def z208 : W := mkw 0xfefbefa802409030 0x03fbefbea0090240 0xfffffffc03c0f03f 0xf7fffffff00f03c0

def z209 : W := mkw 0xfff3fff3ffedfffe 0x1fffcfffcfffb7ff 0xfff3fff3ffffffff 0xffffcfffcfffffff

def z210 : W := mkw 0x000009100ec5b172 0x04000024403b16c5 0x00c30f003fc7f1f9 0xd4030c3c00ff1fc7

def z211 : W := mkw 0x0401432004403112 0x0410050c801100c4 0x0003070000007000 0x40000c1c000001c0

def z212 : W := mkw 0x48f00ff08bed927e 0x0d23c03fc22fb649 0x00f00ff003ff0008 0x0403c03fc00ffc00

def z213 : W := mkw 0xffffcff3fffffb7e 0x2fffff3fcfffffed 0xffffcff3ffffffff 0xffffff3fcfffffff

def z214 : W := mkw 0xfffffdc3fffeffbc 0x3bfffff70ffffbfe 0xffffffc3ffffffff 0xffffffff0fffffff

def z215 : W := mkw 0x9701700334002580 0x125c05c00cd00096 0xff007003fc0001e7 0xbbfc01c00ff00007

def z216 : W := mkw 0xdaf8000199a40000 0x236be00006669000 0xfffc0001ddc0000f 0xb3fff00007770000

def z217 : W := mkw 0x6cf3c7a0cde47916 0x0db3cf1e833791e4 0xfcc30701ddc07001 0x73f30c1c077701c0

def z218 : W := mkw 0xb302b00370004c80 0x12cc0ac00dc00132 0xe300b003c0000e02 0x0b8c02c00f000038

def z219 : W := mkw 0xfefbe6a808840000 0x03fbef9aa0221000 0xfffffffc3fc7003f 0xf7fffffff0ff1c00

def z220 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x031cf8fc20078fd4 0x000c73e3f0801e3f

def z221 : W := mkw 0x9701400334002100 0x025c05000cd00084 0xff034003fc00f1f7 0xfbfc0d000ff003c7

def z222 : W := mkw 0x48fc0b308bf79072 0x2523f02cc22fde41 0x00fc0f3003ff0008 0x0403f03cc00ffc00

def z223 : W := mkw 0x48fc000089b60000 0x2123f0000226d800 0xe0fc0003c3ff002b 0x9f83f0000f0ffc00

def z224 : W := mkw 0x00040854021b8269 0x0000102150086e09 0x003c08fc023f0008 0x0400f023f008fc00

def z225 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0238fc3c038fe12 0x4b808e3f0f00e3f8

def z226 : W := mkw 0x9200000000000000 0x0248000000000000 0xff00000000000007 0xa3fc000000000000

def z227 : W := mkw 0xf3a2bdc3f368debc 0x1bce8af70fcda37a 0xe3e3bfc3c3f8fe3b 0xdf8f8eff0f0fe3f8

def z228 : W := mkw 0x08500b300ac59072 0x0421402cc02b1641 0x00d30f3003c7f039 0xd4034c3cc00f1fc0

def z229 : W := mkw 0x68fa86a800000000 0x01a3ea1aa0000000 0xe0ff8ffc0000001b 0xc383fe3ff0000000

def z230 : W := mkw 0xd2a8000191200000 0x234aa00006448000 0xe0000001c0000000 0x0380000007000000

def z231 : W := mkw 0xb603e00154006900 0x12d80f80055001a4 0xfc038003dc00fe33 0xfbf00e000f7003f8

def z232 : W := mkw 0xdaf8000000000000 0x036be00000000000 0xfffc00000000000f 0xa3fff00000000000

def z233 : W := mkw 0x0c514a3002018060 0x00314528c0080601 0x1cd34f30220781fd 0xe4734d3cc0881e07

def z234 : W := mkw 0x00000b3002419072 0x0400002cc0090641 0x00000f3000000000 0x0000003cc0000000

def z235 : W := mkw 0x60a285c0c1685a1c 0x09828a170305a168 0xe0e387c3c1f87e03 0x5b838e1f0f07e1f8

def z236 : W := mkw 0xbf57fb777edffffb 0x16fd5fedddfb7fff 0xffffffffffffffff 0xffffffffffffffff

def z237 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xffff07000000000f 0xe3fffc1c00000000

def z238 : W := mkw 0x0850000008840000 0x0021400000221000 0x1c1000003c070004 0x2070400000f01c00

def z239 : W := mkw 0xf6abe48800000000 0x03daaf9220000000 0xff2ff0cc00000017 0xe3fcbfc330000000

def z240 : W := mkw 0xdffd7003bdb62580 0x337ff5c00ef6d896 0xfffc7003ffff01ef 0xbffff1c00ffffc07

def z241 : W := mkw 0xf3aab48b70004c80 0x13ceaad22dc00132 0xe32cb0cfc0000e02 0x0b8cb2c33f000038

def z242 : W := mkw 0x01041857761befe9 0x100410615dd86fbf 0x033cf8fffe3ffffe 0x9c0cf3e3fff8ffff

def z243 : W := mkw 0x0401400004002100 0x0010050000100084 0x000340000000f1d0 0x40000d00000003c7

def z244 : W := mkw 0x08500b300ac59072 0x0421402cc02b1641 0x00d00f3003c70008 0x0403403cc00f1c00

def z245 : W := mkw 0x40a0048000000000 0x0102801200000000 0x00e00fc000000008 0x0003803f00000000

def z246 : W := mkw 0xdffd622bb9b60000 0x237ff588aee6d800 0xfffc703fffff002f 0xbffff1c0fffffc00

def z247 : W := mkw 0x0c51422008840000 0x0031450880221000 0x1cd34f303fc7003d 0xf4734d3cc0ff1c00

def z248 : W := mkw 0x0401400004002100 0x0010050000100084 0x1c0300001c007001 0x70700c00007001c0

def z249 : W := mkw 0xf6a3edc1d768fb3c 0x1bda8fb7075da3ec 0xfce38fc3dff8fe3b 0xfff38e3f0f7fe3f8

def z250 : W := mkw 0x01041857bbbf86e9 0x200410615eeefe1b 0x00000003ffff8fe0 0x1c0000000ffffe3f

def z251 : W := mkw 0x01041016201304c1 0x0004104058804c13 0x033c703e223f01ee 0x8c0cf1c0f888fc07

def z252 : W := mkw 0xfafa8dc0c368da3c 0x0bebea37030da368 0xffff8fc3c3f8fe3f 0xfffffe3f0f0fe3f8

def z253 : W := mkw 0x48f806a800000000 0x0123e01aa0000000 0x03fcfffc0000001e 0x800ff3fff0000000

def z254 : W := mkw 0x60a28580c1605814 0x09828a1603058160 0xe0e38fc1c1c0701b 0xd3838e3f070701c0

def z255 : W := mkw 0x4cf94fb80ec5b172 0x0533e53ee03b16c5 0x1cff4ffc3fc7f1fd 0xf473fd3ff0ff1fc7

def z256 : W := mkw 0xb703f8137601ede0 0x12dc0fe04dd807b7 0xff13f833fe07ffff 0xfffc4fe0cff81fff

def z257 : W := mkw 0x61a29dc2e368debc 0x09868a770b8da37a 0xe3e3ffc3e3f8ffff 0xdf8f8fff0f8fe3ff

def z258 : W := mkw 0x2403e6a800000000 0x00900f9aa0000000 0x0003070000000000 0x40000c1c00000000

def z259 : W := mkw 0xfefbe6b80c852142 0x07fbef9ae0321485 0xfffffffc3c0701df 0xe3fffffff0f01c07

def z260 : W := mkw 0xfefbe6a804002100 0x03fbef9aa0100084 0xfffffffc3c00f1ff 0xf3fffffff0f003c7

def z261 : W := mkw 0x09541b762adf96fb 0x0425506dd8ab7e5b 0x03fcfffe23ff8ffe 0x8c0ff3fff88ffe3f

def z262 : W := mkw 0x41a40002a1320000 0x010690000a84c800 0xe3fc0003e3ff002f 0x9f8ff0000f8ffc00

def z263 : W := mkw 0x21069856621bcee9 0x00841a6159886f3b 0xe33ff8ffe23fffff 0xdf8cffe3ff88ffff

def z264 : W := mkw 0x0c514b70cfedfb7e 0x0c31452dc33fb7ed 0x1cd34f33fffffffd 0xfc734d3ccfffffff

def z265 : W := mkw 0xb603e00004002100 0x02d80f8000100084 0xff03f0003c00f1f7 0xf3fc0fc000f003c7

def z266 : W := mkw 0x0501500374006d80 0x101405400dd001b6 0x1c034003fc00fff5 0xf8700d000ff003ff

def z267 : W := mkw 0xdbf8000330000000 0x036fe0000cc00000 0xfffc0003fc00002f 0xbbfff0000ff00000

def z268 : W := mkw 0x60a284c0c1284a0c 0x09828a130304a128 0xe0e38fc3c0380e1b 0xcb838e3f0f00e038

def z269 : W := mkw 0x60a28000c1204800 0x01828a0003048120 0xe0e38003c3f8fe3b 0xdf838e000f0fe3f8

def z270 : W := mkw 0xdffd4323bdf63112 0x277ff50c8ef7d8c4 0xffff0703ffff702f 0xfffffc1c0ffffdc0

def z271 : W := mkw 0xdbfc1017b9b704c1 0x236ff0405ee6dc13 0xfffc703fffff01ef 0xbffff1c0fffffc07

def z272 : W := mkw 0x9701700334002580 0x125c05c00cd00096 0x1f00f0023c008ff6 0xa87c03c008f0023f

def z273 : W := mkw 0xb603f00154006d80 0x12d80fc0055001b6 0xfc03f001dc00ffd1 0x73f00fc0077003ff

def z274 : W := mkw 0x01041956225b96f9 0x0004106558896e5b 0x03fffffe23ffffff 0xdc0ffffff88fffff

def z275 : W := mkw 0xdbfc0dc3bbfe923c 0x2b6ff0370eeffa48 0xfffc0fc3ffff002f 0xbffff03f0ffffc00

def z276 : W := mkw 0xbe5be22800000000 0x02f96f88a0000000 0xff1ff03c00000017 0xe3fc7fc0f0000000

def z277 : W := mkw 0x04014b300641b172 0x0410052cc01906c5 0x1c034f303c00f1f5 0xf0700d3cc0f003c7

def z278 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xffc3f70000000017 0xe3ff0fdc00000000

def z279 : W := mkw 0xfafa8581d9e45814 0x2bebea1607679160 0xfcc30701ddc07001 0x73f30c1c077701c0

def z280 : W := mkw 0xdbfc06abb9b60000 0x236ff01aaee6d800 0xfffc0fffffff002f 0xbffff03ffffffc00

def z281 : W := mkw 0x0000000000000000 0x0000000000000000 0x032cb0cc00000002 0x000cb2c330000000

def z282 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfce38fc00000001b 0xe3f38e3f00000000

def z283 : W := mkw 0x2002a48800000000 0x00800a9220000000 0x0000b0cc00000000 0x000002c330000000

def z284 : W := mkw 0x9601600000000000 0x0258058000000000 0x1f00700000000004 0x207c01c000000000

def z285 : W := mkw 0xfffbe6ab30000000 0x03ffef9aacc00000 0xfffffffffc00003f 0xfbfffffffff00000

def z286 : W := mkw 0x000009100ac59072 0x04000024402b1641 0x0000000003c70000 0x04000000000f1c00

def z287 : W := mkw 0x6cfbe6a800000000 0x01b3ef9aa0000000 0x00fffffc00000018 0x4003fffff0000000

def z288 : W := mkw 0x04014b300ec5b172 0x0410052cc03b16c5 0x00034f303fc7f1f0 0x54000d3cc0ff1fc7

def z289 : W := mkw 0x0c51422000000000 0x0031450880000000 0x1ffffffc0000001f 0xe07ffffff0000000

def z290 : W := mkw 0xf2aaa48800000000 0x03caaa9220000000 0xe000000000000000 0x0380000000000000

def z291 : W := mkw 0xbf53f3237cc47d92 0x16fd4fcc8df311f6 0xffc3f703fdc0fff7 0xfbff0fdc0ff703ff

def z292 : W := mkw 0x9b5c000338960000 0x226d70000ce25800 0xff1c0003fc070027 0xbbfc70000ff01c00

def z293 : W := mkw 0x9e59622800000000 0x02796588a0000000 0x1f1c703c00000004 0x207c71c0f0000000

def z294 : W := mkw 0x095418562a9f86e9 0x0025506158aa7e1b 0x1ffcf8fe3fff8fff 0xbc7ff3e3f8fffe3f

def z295 : W := mkw 0xdbfc1003fdb66d80 0x336ff0400ff6d9b6 0xfffc0003ffffffef 0xbffff0000fffffff

def z296 : W := mkw 0x000000100c852142 0x0400000040321485 0x000000003c0701c0 0x0000000000f01c07

def z297 : W := mkw 0xfbfe8483b9b60000 0x23effa120ee6d800 0xffff8fc3ffff003f 0xfffffe3f0ffffc00

def z298 : W := mkw 0x0104100220120480 0x0004104008804812 0x033cf002223f8ffe 0x8c0cf3c00888fe3f

def z299 : W := mkw 0xb603e00154006900 0x12d80f80055001a4 0xfc034001fc00f1f5 0xf3f00d0007f003c7

def z300 : W := mkw 0xb703f00220000480 0x02dc0fc008800012 0xff03f00220008ff7 0xebfc0fc00880023f

def z301 : W := mkw 0x2002800040004800 0x00800a0001000120 0xe0008003c0000e02 0x0b8002000f000038

def z302 : W := mkw 0xdbfc1047b9be0689 0x236ff0411ee6f81a 0xfffcb0cfffff0e2f 0xbffff2c33ffffc38

def z303 : W := mkw 0xfefbefe8c368da3c 0x0bfbefbfa30da368 0xfce38fc3c3f8fe3b 0xfff38e3f0f0fe3f8

def z304 : W := mkw 0x0000104400080689 0x000000411000201a 0x0000b0cc00000e00 0x000002c330000038

def z305 : W := mkw 0x64a3cdc0c768fb3c 0x09928f37031da3ec 0xfce3cfc3fff8ffff 0xfff38f3f0fffe3ff

def z306 : W := mkw 0x0c514b300ac59072 0x0431452cc02b1641 0x1cd34f3003c7001d 0xe4734d3cc00f1c00

def z307 : W := mkw 0xd3ac0003b1320000 0x234eb0000ec4c800 0xe33c0003e23f002e 0x8f8cf0000f88fc00

def z308 : W := mkw 0x9b5c18573a9f86e9 0x226d70615cea7e1b 0x1f3cf8fe3e3f8ffe 0xac7cf3e3f8f8fe3f

def z309 : W := mkw 0xbf53fb337ec5fdf2 0x16fd4feccdfb17f7 0xffd3ff33ffc7ffff 0xffff4ffccfff1fff

def z310 : W := mkw 0xf2aaadc8c368da3c 0x0bcaaab7230da368 0xe3efbfcfc3f8fe3b 0xdf8fbeff3f0fe3f8

def z311 : W := mkw 0xfefbe001dda46900 0x33fbef80077691a4 0xfcc30001ddc07001 0x73f30c00077701c0

def z312 : W := mkw 0x60a28dc08368923c 0x09828a37020da248 0xe0e38fc003f8001b 0xc7838e3f000fe000

def z313 : W := mkw 0xdbfc0813bbb78060 0x236ff0204eeede01 0xfffc4833ffff81ff 0xbffff120cffffe07

def z314 : W := mkw 0x0004000000120000 0x0000100000004800 0x003c0000023f0008 0x0400f0000008fc00

def z315 : W := mkw 0x01040913bff7b172 0x240410244effdec5 0x00000003fffff1e0 0x1c0000000fffffc7

def z316 : W := mkw 0xfefbf6a844006d80 0x13fbefdaa11001b6 0xfffffffc0000ffdf 0xe3fffffff00003ff

def z317 : W := mkw 0x00040044001a0209 0x0000100110006808 0x002c00cc00380000 0x0000b0033000e000

def z318 : W := mkw 0x9300100374006d80 0x124c00400dd001b6 0xff000003fc00ffe7 0xbbfc00000ff003ff

def z319 : W := mkw 0xfffff6be201304c1 0x03ffffdaf8804c13 0xfffffffc200701df 0xe3fffffff0801c07

def z320 : W := mkw 0x0c5143200cc43112 0x0431450c803310c4 0x1cc347003dc0f1f5 0xf0730d1c00f703c7

def z321 : W := mkw 0x40a00dc08368923c 0x09028037020da248 0x00e30fc003f8f039 0xd4038c3f000fe3c0

def z322 : W := mkw 0x0000000008840000 0x0000000000221000 0x000000003fc70020 0x1400000000ff1c00

def z323 : W := mkw 0x0104000338960000 0x200410000ce25800 0x000000003c070000 0x0000000000f01c00

def z324 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x033cb8fe023f0e0a 0x0c0cf2e3f808fc38

def z325 : W := mkw 0xf3ae8dc3f37ada3c 0x2bceba370fcdeb68 0xe3ef8fc3c3f8fe3b 0xdf8fbe3f0f0fe3f8

def z326 : W := mkw 0x93041857321b86e9 0x024c10615cc86e1b 0xff3cf8fffe3f8fff 0xbffcf3e3fff8fe3f

def z327 : W := mkw 0x08540b740adf927b 0x0421502dd02b7e49 0x00fc0ffc03ff0008 0x0403f03ff00ffc00

def z328 : W := mkw 0x9701700334002580 0x125c05c00cd00096 0x1f0370003c00f1f5 0xf07c0dc000f003c7

def z329 : W := mkw 0x2002b00040004c80 0x10800ac001000132 0x0000b00000000e00 0x000002c000000038

def z330 : W := mkw 0x9f5d70033c962580 0x327d75c00cf25896 0x1f1c70003c0701c4 0x207c71c000f01c07

def z331 : W := mkw 0x60a28dd0c369da7c 0x09828a37430da769 0xe0f3cff3e3ffffff 0xdf83cf3fcf8fffff

def z332 : W := mkw 0xdbfc0843bbbe8228 0x236ff0210eeefa08 0xfffc88c3ffff8e3f 0xbffff2230ffffe38

def z333 : W := mkw 0xf6abe6a800000000 0x03daaf9aa0000000 0xe32ffffc00000012 0x438cbffff0000000

def z334 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xe303f003c000ffd2 0x4b8c0fc00f0003ff

def z335 : W := mkw 0xb703fb337641fdf2 0x16dc0feccdd907f7 0xff03ff33fc00fff7 0xfbfc0ffccff003ff

def z336 : W := mkw 0x93040003b9b60000 0x224c10000ee6d800 0xff000003ffff0027 0xbffc00000ffffc00

def z337 : W := mkw 0x0c51422004002100 0x0031450880100084 0x1cd34f303c00f1fd 0xf0734d3cc0f003c7

def z338 : W := mkw 0xbe5be6a800000000 0x02f96f9aa0000000 0x1f1ffffc00000014 0x607c7ffff0000000

def z339 : W := mkw 0xfefbe6a840004800 0x03fbef9aa1000120 0xffffffffc000fe3f 0xfbffffffff0003f8

def z340 : W := mkw 0x00040854021b8269 0x0000102150086e09 0x033cf8fc023f001e 0x840cf3e3f008fc00

def z341 : W := mkw 0x0000000000000000 0x0000000000000000 0x00004000200081f4 0x8000010000800207

def z342 : W := mkw 0x2403efb80641b172 0x04900fbee01906c5 0x0003fffc0000f1d0 0x40000ffff00003c7

def z343 : W := mkw 0x40a0084083288228 0x01028021020ca208 0xe0e088c3c3f88e3b 0x9f8382230f0fe238

def z344 : W := mkw 0xfafaa6a800000000 0x03ebea9aa0000000 0xe3fcbffc0000000a 0x038ff2fff0000000

def z345 : W := mkw 0x0000081002018060 0x0000002040080601 0x033cf8fc220781fe 0x840cf3e3f0881e07

def z346 : W := mkw 0x2c53efb80ec5b172 0x04b14fbee03b16c5 0x1cd3fffc3fc7f1fd 0xf4734ffff0ff1fc7

def z347 : W := mkw 0xbf5ff0037c966d80 0x32fd7fc00df259b6 0xff1ff003fc07fff7 0xfbfc7fc00ff01fff

def z348 : W := mkw 0xbf53f2337c856dc2 0x16fd4fc8cdf215b7 0xff13f033fc07fff7 0xfbfc4fc0cff01fff

def z349 : W := mkw 0x4cf946a800000000 0x0133e51aa0000000 0x1cff4ffc0000001d 0xe073fd3ff0000000

def z350 : W := mkw 0x48f806a800000000 0x0123e01aa0000000 0x00c0070000000000 0x0003001c00000000

def z351 : W := mkw 0x01001856220986e9 0x000400615888261b 0x0300f8fe20008ff6 0x880c03e3f880023f

def z352 : W := mkw 0x2c53cb304ec5f972 0x04b14f2cc13b17e5 0xfcd3cf33ffc7ffff 0xfff34f3ccfff1fff

def z353 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x003c08fe223f8fe8 0x0c00f023f888fe3f

def z354 : W := mkw 0x0104081222138060 0x0004102048884e01 0x033c4832223f81fe 0x8c0cf120c888fe07

def z355 : W := mkw 0x00001854020986e9 0x000000615008261b 0x0010f8fc22078ffc 0x840043e3f0881e3f

def z356 : W := mkw 0x48f80fb80ac59072 0x0523e03ee02b1641 0x00fc0ffc03c70008 0x0403f03ff00f1c00

def z357 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1c1040303fc7f1e4 0x34704100c0ff1fc7

def z358 : W := mkw 0xfffbf00374006d80 0x13ffefc00dd001b6 0xfffff003fc00ffff 0xfbffffc00ff003ff

def z359 : W := mkw 0x0850000008840000 0x0021400000221000 0x00d0000003c70008 0x04034000000f1c00

def z360 : W := mkw 0x085009000ac49030 0x00214024002b1240 0x1cd30f003fc7f03d 0xf4734c3c00ff1fc0

def z361 : W := mkw 0x0d5552362c9725c3 0x04355548d8b25c97 0x1f1c703c3c0701c4 0x207c71c0f0f01c07

def z362 : W := mkw 0x0850032008c41012 0x0421400c80231040 0x00c0070001c00000 0x0003001c00070000

def z363 : W := mkw 0xb302b00370004c80 0x12cc0ac00dc00132 0xe300f003e0008ff6 0x8b8c03c00f80023f

def z364 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0e30fc1c3f87009 0x57838c3f070fe1c0

def z365 : W := mkw 0x9200000110000000 0x0248000004400000 0xfc000001dc000001 0x33f0000007700000

def z366 : W := mkw 0xdffd4003bdb62100 0x237ff5000ef6d884 0xffff4003fffff1ff 0xfffffd000fffffc7

def z367 : W := mkw 0xf7aff003f5326d80 0x33debfc00fd4c9b6 0xff2ff003fc38fff7 0xfbfcbfc00ff0e3ff

def z368 : W := mkw 0xfefbe7a80cc43112 0x07fbef9ea03310c4 0xfcc307001dc07001 0x73f30c1c007701c0

def z369 : W := mkw 0x61a68dc3fbfeda3c 0x29869a370feffb68 0xe0e38fc3fffffe3b 0xdf838e3f0ffffff8

def z370 : W := mkw 0xb703f8437608efa8 0x12dc0fe10dd823be 0xff23f8c3fe38ffff 0xfffc8fe30ff8e3ff

def z371 : W := mkw 0x0000084002088228 0x0000002100082208 0x002008c002380008 0x040080230008e000

def z372 : W := mkw 0xdbf80003b9a40000 0x236fe0000ee69000 0xffc00003fdc00027 0xbbff00000ff70000

def z373 : W := mkw 0xf6a3edc0c368da3c 0x0bda8fb7030da368 0xffe3ffc3c3f8fe3f 0xffff8fff0f0fe3f8

def z374 : W := mkw 0x0c514b700ecdb37a 0x0431452dc03b36cd 0x1cf3cff23fffffff 0xfc73cf3fc8ffffff

def z375 : W := mkw 0x60a2848040004800 0x01828a1201000120 0xe0e38fc3c000fe3b 0xdb838e3f0f0003f8

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0x001048300000001c 0x80004120c0000000

def z377 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff00f003fc000fc6 0x2bfc03c00ff0003f

def z378 : W := mkw 0xbf53f0037c846d80 0x12fd4fc00df211b6 0xffd3f003ffc7ffff 0xffff4fc00fff1fff

def z379 : W := mkw 0xbf5bf22b74006d80 0x12fd6fc8add001b6 0xff1ff03ffc00fff7 0xfbfc7fc0fff003ff

def z380 : W := mkw 0x49fc1856abbf86e9 0x2127f0615aaefe1b 0x03fcf8fe23ff8ffe 0x8c0ff3e3f88ffe3f

def z381 : W := mkw 0xbe53e22000000000 0x02f94f8880000000 0xffd3ff300000001f 0xe3ff4ffcc0000000

def z382 : W := mkw 0x09540003b9b60000 0x202550000ee6d800 0x1cd00003ffff002d 0xbc7340000ffffc00

def z383 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff03b003dc007e03 0x7bfc0ec00f7001f8

def z384 : W := mkw 0x0d554b322ed7b172 0x0435552cc8bb5ec5 0x1fff4f323ffff1ff 0xfc7ffd3cc8ffffc7

def z385 : W := mkw 0xdbfc0903bbf69030 0x236ff0240eefda40 0xffff0f03fffff03f 0xfffffc3c0fffffc0

def z386 : W := mkw 0x2403fb304641fdf2 0x14900fecc11907f7 0x0003ff300000ffd0 0x40000ffcc00003ff

def z387 : W := mkw 0x0850022000000000 0x0021400880000000 0x00d00f3000000008 0x0003403cc0000000

def z388 : W := mkw 0x01040943fbfeda3c 0x280410250feffb68 0x00000003fffffe20 0x1c0000000ffffff8

def z389 : W := mkw 0x0000080002008020 0x0000002000080200 0x0000080002008038 0x8400002000080200

def z390 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xe3fc0003c3ff000a 0x0f8ff0000f0ffc00

def z391 : W := mkw 0x000009404248da3c 0x0800002501092368 0x000000000000fe00 0x00000000000003f8

def z392 : W := mkw 0x2403f00044006d80 0x10900fc0011001b6 0xe003f003c000fff3 0xdb800fc00f0003ff

def z393 : W := mkw 0x2507f856661befe9 0x10941fe159986fbf 0x033ff8fe223ffffe 0xcc0cffe3f888ffff

def z394 : W := mkw 0x0850000008840000 0x0021400000221000 0x1cc000001dc00001 0x3073000000770000

def z395 : W := mkw 0x2403f8544609efe9 0x10900fe1511827bf 0x0003f8fc0000ffd0 0x40000fe3f00003ff

def z396 : W := mkw 0xfffbf6aa20000480 0x03ffefdaa8800012 0xfffffffe20008fff 0xebfffffff880023f

def z397 : W := mkw 0x9b5c000338960000 0x226d70000ce25800 0x1fdc00003fc7002d 0xb47f700000ff1c00

def z398 : W := mkw 0x68f28dc0cbecda3c 0x09a3ca37032fb368 0xfcf38fc3fffffe3f 0xfff3ce3f0ffffff8

def z399 : W := mkw 0xbe53eb315ec5f972 0x16f94facc57b17e5 0xfcd34f31ffc7f1fd 0xf7f34d3cc7ff1fc7

def z400 : W := mkw 0x200284c040084a0c 0x08800a1301002128 0x000080c000000e00 0x0000020300000038

def z401 : W := mkw 0xf7a3f48374006d80 0x13de8fd20dd001b6 0xffe3ffc3fc00ffff 0xfbff8fff0ff003ff

def z402 : W := mkw 0x0c5142300c852142 0x04314508c0321485 0x1cd34f303c0701dd 0xe0734d3cc0f01c07

def z403 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z404 : W := mkw 0x2002800000000000 0x00800a0000000000 0xe003800000000013 0xc3800e0000000000

def z405 : W := mkw 0x0100100334002580 0x100400400cd00096 0x000000003c0001c0 0x0000000000f00007

def z406 : W := mkw 0x48fc0dc08bfe923c 0x2923f037022ffa48 0x00fc0fc003ff0008 0x0403f03f000ffc00

def z407 : W := mkw 0x00000100c1605814 0x0800000403058160 0x00000001c1c07000 0x10000000070701c0

def z408 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1ffffffc3fc7f1ff 0xf47ffffff0ff1fc7

def z409 : W := mkw 0x60a28d8002409030 0x01828a3600090240 0xe0e38fc003c0f03b 0xd7838e3f000f03c0

def z410 : W := mkw 0x48fc08548bbf8269 0x2123f021522efe09 0x00fc08fc03ff0008 0x0403f023f00ffc00

def z411 : W := mkw 0x0000090002409030 0x0000002400090240 0x00030f000000f010 0x40000c3c000003c0

def z412 : W := mkw 0xdafc000089b60000 0x236bf0000226d800 0xfffc000003ff000f 0xa7fff000000ffc00

def z413 : W := mkw 0x04014b300641b172 0x0410052cc01906c5 0x00134f302207f1fc 0xc4004d3cc0881fc7

def z414 : W := mkw 0x0d555a76221b86e9 0x00355569d8886e1b 0x1ffffffe223f8fff 0xec7ffffff888fe3f

def z415 : W := mkw 0xf7a7fdd7f77bfffd 0x1bde9ff75fddefff 0xffffffffffffffff 0xffffffffffffffff

def z416 : W := mkw 0x49fc0002a9b60000 0x2127f0000aa6d800 0x03fc000223ff002e 0x8c0ff000088ffc00

def z417 : W := mkw 0xfefbefe88368923c 0x0bfbefbfa20da248 0xfffffffc03f8001f 0xe7fffffff00fe000

def z418 : W := mkw 0x040149100ec5b172 0x04100524403b16c5 0x1c0340003fc7f1f5 0xf4700d0000ff1fc7

def z419 : W := mkw 0xdffd5b77bfffb7fb 0x277ff56ddefffedf 0xffffffffffffffff 0xffffffffffffffff

def z420 : W := mkw 0x40a0000081200000 0x0102800002048000 0xe0200003c0380002 0x0b8080000f00e000

def z421 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xffefb7cc00000003 0x63ffbedf30000000

def z422 : W := mkw 0xb302b00370004c80 0x12cc0ac00dc00132 0xff00b003fc000e27 0xbbfc02c00ff00038

def z423 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xffdf773c00000005 0x63ff7ddcf0000000

def z424 : W := mkw 0x9701700334002580 0x125c05c00cd00096 0x1f0070003c0001c4 0x207c01c000f00007

def z425 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff037001fc0071c5 0x73fc0dc007f001c7

def z426 : W := mkw 0xfbfeb003f9b64c80 0x33effac00fe6d932 0xfffcb003ffff0e2f 0xbffff2c00ffffc38

def z427 : W := mkw 0xb302800370004800 0x02cc0a000dc00120 0xff038003fc00fe37 0xfbfc0e000ff003f8

def z428 : W := mkw 0x9f5d4b333ed7b172 0x267d752cccfb5ec5 0x1fdf4f303fc7f1fd 0xf47f7d3cc0ff1fc7

def z429 : W := mkw 0x000001000cc43112 0x04000004003310c4 0x000000001dc07000 0x10000000007701c0

def z430 : W := mkw 0x40a0000081200000 0x0102800002048000 0xe0c00001c1c00001 0x1383000007070000

def z431 : W := mkw 0x68f28ff0cbedda7e 0x0da3ca3fc32fb769 0xe0f38ff3c3fffe3b 0xdf83ce3fcf0ffff8

def z432 : W := mkw 0x0004000089b60000 0x200010000226d800 0x0000000003ff0000 0x04000000000ffc00

def z433 : W := mkw 0xfbfe84c3f9be4a0c 0x2beffa130fe6f928 0xfffc80c3ffff0e2f 0xbffff2030ffffc38

def z434 : W := mkw 0x2c53e6a800000000 0x00b14f9aa0000000 0x1cd3fffc0000001d 0xe0734ffff0000000

def z435 : W := mkw 0xffffefebfbfeda3c 0x2bffffbfafeffb68 0xfffffffffffffe3f 0xfffffffffffffff8

def z436 : W := mkw 0x68fa8fe8c368da3c 0x09a3ea3fa30da368 0xe0ff8fffc3f8fe3b 0xdf83fe3fff0fe3f8

def z437 : W := mkw 0x040148100601a160 0x0010052040180685 0x1c1348303e07f1fd 0xf4704d20c0f81fc7

def z438 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0x00e38fc003f8fe18 0x44038e3f000fe3f8

def z439 : W := mkw 0xdaf8000199a40000 0x236be00006669000 0xfce00003dff8002b 0xbff380000f7fe000

def z440 : W := mkw 0x6cf3c6a000000000 0x01b3cf1a80000000 0xfcf3cff00000001f 0xe3f3cf3fc0000000

def z441 : W := mkw 0x0401423004012142 0x04100508c0100485 0x00004030000001c0 0x00000100c0000007

def z442 : W := mkw 0x2102900260004c80 0x00840a4009800132 0xe303f003e000fff7 0xdb8c0fc00f8003ff

def z443 : W := mkw 0x2002848000000000 0x00800a1200000000 0x00038fc000000010 0x40000e3f00000000

def z444 : W := mkw 0x2403efe84248da3c 0x08900fbfa1092368 0x0003fffc0000fe10 0x40000ffff00003f8

def z445 : W := mkw 0xdbfc1003b9b60480 0x236ff0400ee6d812 0xfffcf003ffff8fff 0xbffff3c00ffffe3f

def z446 : W := mkw 0xdbfc000220120000 0x036ff00008804800 0xfffc0002223f002f 0xaffff0000888fc00

def z447 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfcd34f300000001d 0xe3f34d3cc0000000

def z448 : W := mkw 0x0d555a762e9fa7eb 0x04355569d8ba7e9f 0x1f3cf8fe3e3f8ffe 0xac7cf3e3f8f8fe3f

def z449 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c0000003c000025 0xb070000000f00000

def z450 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x032cb0ce223f8fe2 0x0c0cb2c33888fe3f

def z451 : W := mkw 0xb707f01774136dc1 0x12dc1fc05dd04db7 0xff1ff03ffc07fff7 0xfbfc7fc0fff01fff

def z452 : W := mkw 0x010419562edfb7fb 0x0404106558bb7edf 0x033cf8fe3ffffffe 0x9c0cf3e3f8ffffff

def z453 : W := mkw 0x0100100220000480 0x0004004008800012 0x0300b00200000e02 0x080c02c008000038

def z454 : W := mkw 0xb707f856221b86e9 0x02dc1fe158886e1b 0xff3ff8fe223f8fff 0xeffcffe3f888fe3f

def z455 : W := mkw 0xfffff6ee201a0689 0x03ffffdbb880681a 0xfffffffe00380e1f 0xebfffffff800e038

def z456 : W := mkw 0x0c554b740edfb37b 0x0431552dd03b7ecd 0x1cff4ffc3ffff1fd 0xf473fd3ff0ffffc7

def z457 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfcc3fffc00000011 0x63f30ffff0000000

def z458 : W := mkw 0x01041016201304c1 0x0004104058804c13 0x031cf03e20078ff6 0x880c73c0f8801e3f

def z459 : W := mkw 0xb603e6a800000000 0x02d80f9aa0000000 0xff03fffc00000017 0xe3fc0ffff0000000

def z460 : W := mkw 0x9f5d622b38960000 0x227d7588ace25800 0x1f1c703c3c070004 0x207c71c0f0f01c00

def z461 : W := mkw 0x0c5143200cc43112 0x0431450c803310c4 0x1cd307003fc7702d 0xf4734c1c00ff1dc0

def z462 : W := mkw 0x20028dc04248da3c 0x08800a3701092368 0xe0038fc3c000fe33 0xdb800e3f0f0003f8

def z463 : W := mkw 0x0c5142200c842102 0x0431450880321084 0x1c0000001c000000 0x2070000000700000

def z464 : W := mkw 0x60a28d80c360d834 0x09828a36030d8360 0xe0c30f01c3c0f039 0xd7830c3c070f03c0

def z465 : W := mkw 0x0104000220120000 0x0004100008804800 0x032c000200380002 0x080cb0000800e000

def z466 : W := mkw 0xf7a3f4c3f5286f8c 0x1bde8fd30fd4a1be 0xff23f0c3fc38fff7 0xfbfc8fc30ff0e3ff

def z467 : W := mkw 0x60a28580c1605814 0x09828a1603058160 0xe0e30703c3f8702b 0xdf838c1c0f0fe1c0

def z468 : W := mkw 0x2c53cff04ecdfb7e 0x0cb14f3fc13b37ed 0x1cd3cff03fc7fffd 0xf4734f3fc0ff1fff

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300f00000000016 0x800c03c000000000

def z470 : W := mkw 0xfefbfefc020986e9 0x03fbeffbf008261b 0xfffffffc00008fdf 0xe3fffffff000023f

def z471 : W := mkw 0x9e59622800000000 0x02796588a0000000 0x1fdf7f3c0000001d 0xe07f7dfcf0000000

def z472 : W := mkw 0x0004001400130041 0x0000100050004c01 0x001c003c00070000 0x00007000f0001c00

def z473 : W := mkw 0x2002800040004800 0x00800a0001000120 0xe0030001c0007001 0x53800c00070001c0

def z474 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0x1f03f0003c00ffd4 0x607c0fc000f003ff

def z475 : W := mkw 0x0000084002088228 0x0000002100082208 0x0000000202388e20 0x0c0000000808e238

def z476 : W := mkw 0x0100100370004c80 0x100400400dc00132 0x00000003c0000e00 0x080000000f000038

def z477 : W := mkw 0x01041046201a0689 0x000410411880681a 0x033cb0ce223f0e2e 0x8c0cf2c33888fc38

def z478 : W := mkw 0x48f80fe88368923c 0x0923e03fa20da248 0x00fc0ffc03f80008 0x0403f03ff00fe000

def z479 : W := mkw 0x930c000330120000 0x224c30000cc04800 0x030c000000000000 0x000c300000000000

def z480 : W := mkw 0x01001943f768ffbc 0x180400650fdda3fe 0x00000003fff8ffe0 0x1c0000000fffe3ff

def z481 : W := mkw 0x0000000199a40000 0x2000000006669000 0x00000001ddc00000 0x1000000007770000

def z482 : W := mkw 0xdef9622800000000 0x037be588a0000000 0xfffc703c0000000f 0xa3fff1c0f0000000

def z483 : W := mkw 0x0c5140000c842100 0x0031450000321084 0x1cd340003fc7f1fd 0xf4734d0000ff1fc7

def z484 : W := mkw 0xfafa8dc1dbecda3c 0x2bebea37076fb368 0xfce38fc3dff8fe3b 0xfff38e3f0f7fe3f8

def z485 : W := mkw 0x0000001000010040 0x0000000040000401 0x00104030200701c4 0x00004100c0801c07

def z486 : W := mkw 0x01041046201a0689 0x000410411880681a 0x0000000200380e00 0x080000000800e038

def z487 : W := mkw 0x41a41dd6a37b96fd 0x090690775a8dee5b 0x03fcfffe23ff8ffe 0x8c0ff3fff88ffe3f

def z488 : W := mkw 0x9701700374006d80 0x125c05c00dd001b6 0x1f007003fc00ffe4 0x387c01c00ff003ff

def z489 : W := mkw 0x0100100220000480 0x0004004008800012 0x0000000220008fe0 0x080000000880023f

def z490 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xff3c0003fc3f0006 0x2bfcf0000ff0fc00

def z491 : W := mkw 0xbf53f22374006d80 0x12fd4fc88dd001b6 0xffd3ff33fc00ffff 0xfbff4ffccff003ff

def z492 : W := mkw 0xf2aaa48800000000 0x03caaa9220000000 0xe33cf8fc0000001e 0x838cf3e3f0000000

def z493 : W := mkw 0xfbfe8583f9f65814 0x2beffa160fe7d960 0xffff0703ffff702f 0xfffffc1c0ffffdc0

def z494 : W := mkw 0x0104000220120000 0x0004100008804800 0x00000002223f0020 0x0c0000000888fc00

def z495 : W := mkw 0xffffe6abb1320000 0x23ffff9aaec4c800 0xffffffffc038001f 0xebffffffff00e000

def z496 : W := mkw 0xdbfc0913bff7b172 0x276ff0244effdec5 0xfffc0003fffff1ef 0xbffff0000fffffc7

def z497 : W := mkw 0xfffffffe2edfb7fb 0x07fffffff8bb7edf 0xfffffffe3fffffff 0xfffffffff8ffffff

def z498 : W := mkw 0x000009100ec5b172 0x04000024403b16c5 0x001048303fc7f1fc 0x94004120c0ff1fc7

def z499 : W := mkw 0xd3ac1857b33b86e9 0x234eb0615eccee1b 0xe33cf8ffe23f8ffe 0x8f8cf3e3ff88fe3f

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c0000003c00029 0x94030000000f0000

def z501 : W := mkw 0x9a58000000000000 0x0269600000000000 0x1f1c000000000004 0x207c700000000000

def z502 : W := mkw 0xf7a3f583f5607d94 0x1bde8fd60fd581f6 0xffc3f703fdc0fff7 0xfbff0fdc0ff703ff

def z503 : W := mkw 0x60a2848000000000 0x01828a1200000000 0xe0c3070000000001 0x43830c1c00000000

def z504 : W := mkw 0x01041857761befe9 0x100410615dd86fbf 0x00000003fe3fffe0 0x1c0000000ff8ffff

def z505 : W := mkw 0xfefbe6a954006900 0x13fbef9aa55001a4 0xfcc30701dc007001 0x73f30c1c077001c0

def z506 : W := mkw 0xfffffb33fff7fdf2 0x37ffffeccfffdff7 0xffffff33ffffffff 0xfffffffccfffffff

def z507 : W := mkw 0xfafa848000000000 0x03ebea1200000000 0xffff8fc00000001f 0xe3fffe3f00000000

def z508 : W := mkw 0xfefbe7a80cc43112 0x07fbef9ea03310c4 0xfffffffc1dc0701f 0xf3fffffff07701c0

def z509 : W := mkw 0x40a40dd4837b927d 0x09029037520dee49 0x00fc0ffc03ff0008 0x0403f03ff00ffc00

def z510 : W := mkw 0x01001812220184e0 0x0004006048880613 0x0310f83222078ffe 0x8c0c43e0c8881e3f

def z511 : W := mkw 0xfeffe6a889b60000 0x23fbff9aa226d800 0xfffffffc03ff001f 0xe7fffffff00ffc00

def z512 : W := mkw 0xb603e00154006900 0x12d80f80055001a4 0xff03f001dc007017 0xf3fc0fc0077001c0

def z513 : W := mkw 0x0000000000000000 0x0000000000000000 0x002088c00000001a 0x8000822300000000

def z514 : W := mkw 0xfefbe6a999a40000 0x23fbef9aa6669000 0xfcc30701ddc00001 0x73f30c1c07770000

def z515 : W := mkw 0x0000010000401010 0x0000000400010040 0x00c3070001c07001 0x50030c1c000701c0

def z516 : W := mkw 0x9300300330000480 0x124c00c00cc00012 0x0300300000000000 0x000c00c000000000

def z517 : W := mkw 0x0850000000000000 0x0021400000000000 0x1cd000000000000d 0xa073400000000000

def z518 : W := mkw 0x21069dd6625bdefd 0x08841a7759896f7b 0x033ffffe223ffffe 0xcc0cfffff888ffff

def z519 : W := mkw 0xffffe6ab38960000 0x23ffff9aace25800 0xfffffffc3c07001f 0xe3fffffff0f01c00

def z520 : W := mkw 0x9b5c1017389704c1 0x226d70405ce25c13 0x1f1c703c3c0701c4 0x207c71c0f0f01c07

def z521 : W := mkw 0x9b50000338840000 0x026d40000ce21000 0xffd00003ffc7002f 0xbfff40000fff1c00

def z522 : W := mkw 0x0954000228960000 0x0025500008a25800 0x1ffc00023fff002f 0xbc7ff00008fffc00

def z523 : W := mkw 0x0000081002018060 0x0000002040080601 0x0010083002070008 0x04004020c0081c00

def z524 : W := mkw 0xb306b047701a4e89 0x12cc1ac11dc0693a 0xe32cb0cfc0380e02 0x0b8cb2c33f00e038

def z525 : W := mkw 0xdbfc0003b1320000 0x236ff0000ec4c800 0xfffc0003c038000f 0xabfff0000f00e000

def z526 : W := mkw 0x61a69cd6221b86e9 0x01869a7358886e1b 0xe3fffffe223f8fff 0xcf8ffffff888fe3f

def z527 : W := mkw 0xdbfc0943fbfeda3c 0x2b6ff0250feffb68 0xfffc0003fffffe2f 0xbffff0000ffffff8

def z528 : W := mkw 0xffffefbbbff7b172 0x27ffffbeeeffdec5 0xfffffffffffff1ff 0xffffffffffffffc7

def z529 : W := mkw 0x0000085402098269 0x0000002150082609 0x000008fc00000000 0x00000023f0000000

def z530 : W := mkw 0x2002800040004800 0x00800a0001000120 0x000380000000fe10 0x40000e00000003f8

def z531 : W := mkw 0x0100000330000000 0x000400000cc00000 0x00000003fc000020 0x180000000ff00000

def z532 : W := mkw 0xb703f00370004c80 0x12dc0fc00dc00132 0xff03f003c0000e17 0xebfc0fc00f000038

def z533 : W := mkw 0x60a68dd4c37bda7d 0x09829a37530def69 0xe0ff8fffc3fffe3b 0xdf83fe3fff0ffff8

def z534 : W := mkw 0x200289004240d830 0x00800a2401090360 0xe0c38f03c3c0fe3b 0xdf830e3c0f0f03f8

def z535 : W := mkw 0x61a29dc3f768ffbc 0x19868a770fdda3fe 0xe0e38fc3fff8fffb 0xdf838e3f0fffe3ff

def z536 : W := mkw 0x200288404208ca28 0x00800a2101082328 0xe02388c3c238fe3b 0xdf808e230f08e3f8

def z537 : W := mkw 0x9300100330000480 0x024c00400cc00012 0xff00f003fc008ff7 0xbbfc03c00ff0023f

def z538 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x00104832223f8ffc 0x8c004120c888fe3f

def z539 : W := mkw 0xfbfe8003f9b64800 0x23effa000fe6d920 0xffff8003fffffe3f 0xfffffe000ffffff8

def z540 : W := mkw 0x08500b300ac59072 0x0421402cc02b1641 0x00d04f3023c781fc 0x8403413cc08f1e07

def z541 : W := mkw 0xfffff857ffbfefe9 0x33ffffe15ffeffbf 0xfffff8ffffffffff 0xffffffe3ffffffff

def z542 : W := mkw 0x08500b300ac59072 0x0421402cc02b1641 0x1cd00f303fc7002d 0xb473403cc0ff1c00

def z543 : W := mkw 0x2403fdc04648ffbc 0x18900ff7011923fe 0x0003ffc00000ffd0 0x40000fff000003ff

def z544 : W := mkw 0x04014b300641b172 0x0410052cc01906c5 0x00c34f3003c0f1f9 0xd4030d3cc00f03c7

def z545 : W := mkw 0x2c53fb304ec5fdf2 0x14b14fecc13b17f7 0x1cd3ff303fc7fffd 0xf4734ffcc0ff1fff

def z546 : W := mkw 0x0104000220120000 0x0004100008804800 0x031c000020070004 0x000c700000801c00

def z547 : W := mkw 0xfffbffebf768ffbc 0x1bffefffafdda3fe 0xfffffffffff8ffff 0xffffffffffffe3ff

def z548 : W := mkw 0x9f514b333ec5b172 0x067d452cccfb16c5 0xffd34f33ffc7f1ff 0xffff4d3ccfff1fc7

def z549 : W := mkw 0xb707f047741a6f89 0x12dc1fc11dd069be 0xff2ff0cffc38fff7 0xfbfcbfc33ff0e3ff

def z550 : W := mkw 0xffffe003fdb66900 0x33ffff800ff6d9a4 0xffff0003ffff702f 0xfffffc000ffffdc0

def z551 : W := mkw 0xf2aaa48800000000 0x03caaa9220000000 0xe3efbfcc0000001b 0xc38fbeff30000000

def z552 : W := mkw 0xdaf806a800000000 0x036be01aa0000000 0xfffc0ffc0000000f 0xa3fff03ff0000000

def z553 : W := mkw 0x9601600114002100 0x1258058004500084 0x1c0000001c000000 0x2070000000700000

def z554 : W := mkw 0x0401400004002100 0x0010050000100084 0x1c0040003c0001c4 0x2070010000f00007

def z555 : W := mkw 0xb703f943f768ffbc 0x1adc0fe50fdda3fe 0xff03f003fff8fff7 0xfffc0fc00fffe3ff

def z556 : W := mkw 0xbe53eb300ec5b172 0x06f94facc03b16c5 0xffd3ff303fc7f1ff 0xf7ff4ffcc0ff1fc7

def z557 : W := mkw 0xfefbe7a8c1605814 0x0bfbef9ea3058160 0xfcc30701c1c07001 0x73f30c1c070701c0

def z558 : W := mkw 0x49fc0003b9b60000 0x2127f0000ee6d800 0x00fc0003ffff0028 0x1c03f0000ffffc00

def z559 : W := mkw 0xdef94b319fe5b172 0x277be52cc67f96c5 0xfcd34f31ffc7f1fd 0xf7f34d3cc7ff1fc7

def z560 : W := mkw 0x0000084002088228 0x0000002100082208 0x000088c000008e10 0x0000022300000238

def z561 : W := mkw 0x2503f00264006d80 0x10940fc0099001b6 0x0303f0022000fff6 0xc80c0fc0088003ff

def z562 : W := mkw 0x0858022800000000 0x00216008a0000000 0x001c003c00000000 0x00007000f0000000

def z563 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe02080c3c3f8fe22 0x1f8082030f0fe3f8

def z564 : W := mkw 0xffffe003b9b60000 0x23ffff800ee6d800 0xfffff003ffff003f 0xffffffc00ffffc00

def z565 : W := mkw 0xdef94b300ec5b172 0x077be52cc03b16c5 0xffff4f303fc7f1ff 0xf7fffd3cc0ff1fc7

def z566 : W := mkw 0x085008100a858060 0x00214020402a1601 0x1cd048303fc781fd 0xb4734120c0ff1e07

def z567 : W := mkw 0x41a40003b9b60000 0x210690000ee6d800 0xe0e00003ffff002b 0x9f8380000ffffc00

def z568 : W := mkw 0x0c514b200ec4b132 0x0431452c803b12c4 0x1cc30f001fc0f039 0xf4730c3c007f03c0

def z569 : W := mkw 0x9f5d42333c972142 0x267d7508ccf25c85 0x1f1c40303c0701c4 0x207c7100c0f01c07

def z570 : W := mkw 0x0401700004002580 0x101005c000100096 0x00007000000001c0 0x000001c000000007

def z571 : W := mkw 0xb603e00000000000 0x02d80f8000000000 0xfc03000000000001 0x63f00c0000000000

def z572 : W := mkw 0xb703e00374006900 0x12dc0f800dd001a4 0xff030003fc007027 0xfbfc0c000ff001c0

def z573 : W := mkw 0x9f5d7a7e221b86e9 0x027d75e9f8886e1b 0x1f3cf8fe223f8ffe 0xac7cf3e3f888fe3f

def z574 : W := mkw 0x60a28cc002088228 0x01828a3300082208 0xe0e38fc202388e3b 0xcf838e3f0808e238

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000003c0000023 0x9b8000000f000000

def z576 : W := mkw 0x48f8000089a40000 0x2123e00002269000 0x00c0000001c00000 0x0003000000070000

def z577 : W := mkw 0x0000091002419070 0x0000002440090641 0x00d34f3023c7f1fd 0xd4034d3cc08f1fc7

def z578 : W := mkw 0x0d555b762edfb7fb 0x0435556dd8bb7edf 0x1cd34f323ffffffd 0xfc734d3cc8ffffff

def z579 : W := mkw 0x010019137ec5fdf2 0x140400644dfb17f7 0x00000003ffc7ffe0 0x1c0000000fff1fff

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x002000020238002a 0x8c0080000808e000

def z581 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xffdc0001fdc70005 0x33ff700007f71c00

def z582 : W := mkw 0xdaf8000081200000 0x036be00002048000 0xfffc0003c3f8002f 0xbffff0000f0fe000

def z583 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfcff0ffc00000009 0x63f3fc3ff0000000

def z584 : W := mkw 0x00000940c368da3c 0x08000025030da368 0x002088c3c3f8fe3a 0x9c0082230f0fe3f8

def z585 : W := mkw 0xb603e00040004800 0x02d80f8001000120 0xff03f003c000fe37 0xfbfc0fc00f0003f8

def z586 : W := mkw 0xf3aeb003f1324c80 0x33cebac00fc4c932 0xe32cb003c0380e02 0x0b8cb2c00f00e038

def z587 : W := mkw 0x2403e00044006900 0x10900f80011001a4 0x0003000000007000 0x40000c00000001c0

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x031c703c00000004 0x000c71c0f0000000

def z589 : W := mkw 0xf3ae84c3f13a4a0c 0x2bceba130fc4e928 0xe32c80c3c0380e02 0x0b8cb2030f00e038

def z590 : W := mkw 0xf3aeb4ce201a0689 0x03cebad33880681a 0xe32cb0ce00380e02 0x0b8cb2c33800e038

def z591 : W := mkw 0x9300000330000000 0x024c00000cc00000 0xe3000003c0000002 0x0b8c00000f000000

def z592 : W := mkw 0xfefbeeb802018060 0x03fbefbae0080601 0xfffffffc220781ff 0xe7fffffff0881e07

def z593 : W := mkw 0x0000004000080208 0x0000000100002008 0x002080c200380e02 0x080082030800e038

def z594 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x032cf8fe00388fd2 0x080cb3e3f800e23f

def z595 : W := mkw 0x2403e00000000000 0x00900f8000000000 0x0003f00000000010 0x40000fc000000000

def z596 : W := mkw 0xb306b857721bcee9 0x12cc1ae15dc86f3b 0xe33cf8ffe23f8ffe 0x8f8cf3e3ff88fe3f

def z597 : W := mkw 0xd3ac0003b9b60000 0x234eb0000ee6d800 0xe32c0003ffff0022 0x1f8cb0000ffffc00

def z598 : W := mkw 0x00041854021b86e9 0x0000106150086e1b 0x003cf8fc023f8fd8 0x0400f3e3f008fe3f

def z599 : W := mkw 0x04015b740649b7fb 0x0410056dd01926df 0x0003fffc0000ffd0 0x40000ffff00003ff

def z600 : W := mkw 0xfbfea48bb9b60000 0x23effa922ee6d800 0xfffcb0cfffff002f 0xbffff2c33ffffc00

def z601 : W := mkw 0x9f5172333c8525c2 0x167d45c8ccf21497 0x1f1070303c0701c4 0x207c41c0c0f01c07

def z602 : W := mkw 0x6cf3cfe0c368da3c 0x09b3cf3f830da368 0xfcf3cff3c3f8fe3f 0xfff3cf3fcf0fe3f8

def z603 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0x1ffc00003fff000c 0x247ff00000fffc00

def z604 : W := mkw 0xf6a3e48000000000 0x03da8f9200000000 0xffe3ffc00000001f 0xe3ff8fff00000000

def z605 : W := mkw 0x9f59722b34002580 0x127d65c8acd00096 0x1f1c703c3c0001c4 0x207c71c0f0f00007

def z606 : W := mkw 0x01041857bbbf86e9 0x200410615eeefe1b 0x033cf8ffffff8ffe 0x9c0cf3e3fffffe3f

def z607 : W := mkw 0x9e59622800000000 0x02796588a0000000 0x1c00000000000000 0x2070000000000000

def z608 : W := mkw 0xbe53e3215cc47912 0x16f94f8c857311e4 0xfcc30701ddc07001 0x73f30c1c077701c0

def z609 : W := mkw 0xfefbefb80ac59072 0x07fbefbee02b1641 0xfffffffc03c7001f 0xe7fffffff00f1c00

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000f8fc00000010 0x000003e3f0000000

def z611 : W := mkw 0x01041046201a0689 0x000410411880681a 0x033cf8fe00380e1e 0x880cf3e3f800e038

def z612 : W := mkw 0xfffffeff761befe9 0x13fffffbfdd86fbf 0xfffffffffe3fffff 0xfffffffffff8ffff

def z613 : W := mkw 0xb202a00000000000 0x02c80a8000000000 0xe300b00000000002 0x038c02c000000000

def z614 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x0300f002223f8ff6 0x8c0c03c00888fe3f

def z615 : W := mkw 0x6cf3cfe0cfecfb3e 0x0db3cf3f833fb3ec 0xfce38fc3dff8fe3b 0xfff38e3f0f7fe3f8

def z616 : W := mkw 0x6cf3cfb00ec5b172 0x05b3cf3ec03b16c5 0xfcf3cff03fc7f1ff 0xf7f3cf3fc0ff1fc7

def z617 : W := mkw 0x08500b300ec5b172 0x0421402cc03b16c5 0x00d00f303fc7f1e8 0x1403403cc0ff1fc7

def z618 : W := mkw 0x0100100220000480 0x0004004008800012 0x033cf8fe20008ffe 0x880cf3e3f880023f

def z619 : W := mkw 0xfbfe9dd7fbffdefd 0x2beffa775fefff7b 0xffffffffffffffff 0xffffffffffffffff

def z620 : W := mkw 0x0c514a300e85a162 0x04314528c03a1685 0x1c1048303e0781fc 0xa4704120c0f81e07

def z621 : W := mkw 0xfffbf003fda46d80 0x33ffefc00ff691b6 0xffc3f003fdc0fff7 0xfbff0fc00ff703ff

def z622 : W := mkw 0x9b5c0003b9b60000 0x226d70000ee6d800 0x1f1c0003ffff0024 0x3c7c70000ffffc00

def z623 : W := mkw 0x48fc0efc021b8269 0x0123f03bf0086e09 0x00fc0ffc023f0008 0x0403f03ff008fc00

def z624 : W := mkw 0x9f517b333ec5b5f2 0x167d45ecccfb16d7 0x1fd37f303fc7f1fd 0xf47f4dfcc0ff1fc7

def z625 : W := mkw 0xfffffeffbbbf86e9 0x23fffffbfeeefe1b 0xffffffffffff8fff 0xfffffffffffffe3f

def z626 : W := mkw 0x00001854020986e9 0x000000615008261b 0x0000000000008fc0 0x000000000000023f

def z627 : W := mkw 0xf3aebcde221b86e9 0x03cebaf378886e1b 0xe33cf8fe223f8ffe 0x8f8cf3e3f888fe3f

def z628 : W := mkw 0xfffbf6ab34002580 0x13ffefdaacd00096 0xfffffffc3c0001df 0xe3fffffff0f00007

def z629 : W := mkw 0x64a3e6a800000000 0x01928f9aa0000000 0xe0e3fffc0000001b 0xc3838ffff0000000

def z630 : W := mkw 0x4cf14b308fe5b172 0x0533c52cc23f96c5 0xfcf34f33fffff1ff 0xfff3cd3ccfffffc7

def z631 : W := mkw 0x00040854021b8269 0x0000102150086e09 0x00000000023f0000 0x040000000008fc00

def z632 : W := mkw 0x01040003b9b60000 0x200410000ee6d800 0x033c0003ffff002e 0x9c0cf0000ffffc00

def z633 : W := mkw 0x20028dc04248da3c 0x08800a3701092368 0x00c38fc003c0fe39 0xd4030e3f000f03f8

def z634 : W := mkw 0xfffff6abfdb66d80 0x33ffffdaaff6d9b6 0xffffffffffffffff 0xffffffffffffffff

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x003c08fc00000008 0x0000f023f0000000

def z636 : W := mkw 0x0000000000000000 0x0000000000000000 0x033c00000000000e 0x800cf00000000000

def z637 : W := mkw 0x01040003b1320000 0x200410000ec4c800 0x00000003c0380000 0x080000000f00e000

def z638 : W := mkw 0xf7abf48b74006d80 0x13deafd22dd001b6 0xff2ff0cffc00fff7 0xfbfcbfc33ff003ff

def z639 : W := mkw 0x0000000081200000 0x0000000002048000 0x00000003c3f80020 0x1c0000000f0fe000

def z640 : W := mkw 0x0000081002018060 0x0000002040080601 0x00000000220781e0 0x0400000000881e07

def z641 : W := mkw 0xb202a00150004800 0x12c80a8005400120 0xe0000001c0000000 0x0380000007000000

def z642 : W := mkw 0x00040854021b8269 0x0000102150086e09 0x003c88fe023f8e3a 0x8c00f223f808fe38

def z643 : W := mkw 0x40a8048800000000 0x0102a01220000000 0x002c00cc00000000 0x0000b00330000000

def z644 : W := mkw 0x0401422000000000 0x0010050880000000 0x00034f3000000010 0x40000d3cc0000000

def z645 : W := mkw 0x9b5c000338960000 0x226d70000ce25800 0x1f3c00023e3f002e 0xac7cf00008f8fc00

def z646 : W := mkw 0xfeffeefc021b8269 0x03fbffbbf0086e09 0xfffffffc023f001f 0xe7fffffff008fc00

def z647 : W := mkw 0x0c5142300c852142 0x04314508c0321485 0x1cd040303fc701ed 0xb4734100c0ff1c07

def z648 : W := mkw 0x01041016201304c1 0x0004104058804c13 0x00000000200701c0 0x0000000000801c07

def z649 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x033c78fc223f01cc 0x040cf1e3f088fc07

def z650 : W := mkw 0x9e596b380ec5b172 0x067965ace03b16c5 0x1fdf7f3c3fc7f1fd 0xf47f7dfcf0ff1fc7

def z651 : W := mkw 0x60a28dc04248da3c 0x09828a3701092368 0xe0e38fc00000fe1b 0xc3838e3f000003f8

def z652 : W := mkw 0x0000085002098268 0x0000002140082609 0x0030c8f2223f8ffe 0x8c00c323c888fe3f

def z653 : W := mkw 0x40a00dc0c368da3c 0x09028037030da368 0x00e00fc3c3f8fe28 0x1c03803f0f0fe3f8

def z654 : W := mkw 0xdbfc0b33bbf79072 0x276ff02cceefde41 0xfffc0f33ffff002f 0xbffff03ccffffc00

def z655 : W := mkw 0x60a28480c1204804 0x09828a1203048120 0xe0000001c0000000 0x0380000007000000

def z656 : W := mkw 0xb707f857761befe9 0x12dc1fe15dd86fbf 0xff03f003fe3ffff7 0xfffc0fc00ff8ffff

def z657 : W := mkw 0x040149000640b130 0x00100524001902c4 0x1cc34f003fc0f1fd 0xf4730d3c00ff03c7

def z658 : W := mkw 0x97057857361ba7e9 0x125c15e15cd86e9f 0x1f3cf8fe3e3f8ffe 0xac7cf3e3f8f8fe3f

def z659 : W := mkw 0x2102900374006d80 0x10840a400dd001b6 0xe0038003fc00fff3 0xdb800e000ff003ff

def z660 : W := mkw 0xb703e00330000000 0x02dc0f800cc00000 0xff03f003fc000037 0xfbfc0fc00ff00000

def z661 : W := mkw 0xfafaa48800000000 0x03ebea9220000000 0xfffcb0cc0000000f 0xa3fff2c330000000

def z662 : W := mkw 0x0d554b33bff7b172 0x2435552cceffdec5 0x1cd34f33fffff1fd 0xfc734d3ccfffffc7

def z663 : W := mkw 0x9304000330120000 0x024c10000cc04800 0xff3c0003fe3f002f 0xbffcf0000ff8fc00

def z664 : W := mkw 0xf6a3e581d5607914 0x1bda8f96075581e4 0xfcc30701ddc07001 0x73f30c1c077701c0

def z665 : W := mkw 0xb603e00000000000 0x02d80f8000000000 0xff3ff8fc0000001f 0xe3fcffe3f0000000

def z666 : W := mkw 0xdef943219de43112 0x277be50c867790c4 0xfcc30701ddc07001 0x73f30c1c077701c0

def z667 : W := mkw 0x48fc06a889b60000 0x2123f01aa226d800 0x00fc0ffc03ff0008 0x0403f03ff00ffc00

def z668 : W := mkw 0xfffffffee37bdefd 0x0bfffffffb8def7b 0xffffffffe3ffffff 0xffffffffff8fffff

def z669 : W := mkw 0x61a68dc2e37ada3c 0x09869a370b8deb68 0xe3ff8fc3e3fffe3f 0xdf8ffe3f0f8ffff8

def z670 : W := mkw 0xf3a2b4c3f1284e8c 0x1bce8ad30fc4a13a 0xe320b0c3c0380e02 0x0b8c82c30f00e038

def z671 : W := mkw 0x20029dd44249defd 0x08800a775109277b 0x0003fffc0000ffd0 0x40000ffff00003ff

def z672 : W := mkw 0x40a0058081601014 0x0902801602058040 0x00c0070001c00000 0x0003001c00070000

def z673 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cd04f303fc701cc 0x2473413cc0ff1c07

def z674 : W := mkw 0x40a004c08128020c 0x090280130204a008 0x002000c000380000 0x000080030000e000

def z675 : W := mkw 0x0c514b2002409030 0x0031452c80090240 0x1cd34f3003c0f03d 0xf4734d3cc00f03c0

def z676 : W := mkw 0x61a694c6e13a4e8d 0x09869a531b84e93a 0xe32cb0cfc0380e02 0x0b8cb2c33f00e038

def z677 : W := mkw 0x0c51422000000000 0x0031450880000000 0x1cc3070000000001 0x60730c1c00000000

def z678 : W := mkw 0x40ac000081320000 0x2102b0000204c800 0x002c000000380000 0x0000b0000000e000

def z679 : W := mkw 0xb707f003fdb66d80 0x32dc1fc00ff6d9b6 0xff03f003fffffff7 0xfffc0fc00fffffff

def z680 : W := mkw 0x0000090002409030 0x0000002400090240 0x00c00f0003c00008 0x0403003c000f0000

def z681 : W := mkw 0x48fc000089b60000 0x2123f0000226d800 0x1cfc00003fff002d 0xb473f00000fffc00

def z682 : W := mkw 0x40a00dc08368923c 0x09028037020da248 0xe0e00fc3c3f8002b 0x9f83803f0f0fe000

def z683 : W := mkw 0x0c5142300c852142 0x04314508c0321485 0x1c1340303c07f1f5 0xf0704d00c0f01fc7

def z684 : W := mkw 0x0d515b322ec5b5f2 0x0435456cc8bb16d7 0x1fd3ff323fc7ffff 0xfc7f4ffcc8ff1fff

def z685 : W := mkw 0xfefbe7a8c1605814 0x0bfbef9ea3058160 0xfffffffdc1c0701f 0xf3fffffff70701c0

def z686 : W := mkw 0x00000040c1284a0c 0x080000010304a128 0x00000003c0380e00 0x080000000f00e038

def z687 : W := mkw 0x64a3fdc0c768ffbc 0x19928ff7031da3fe 0xe0e3ffc3c3f8fffb 0xdf838fff0f0fe3ff

def z688 : W := mkw 0x0000094002489238 0x0000002500092248 0x00e38fc203f8fe3b 0xdc038e3f080fe3f8

def z689 : W := mkw 0x00001014000104c1 0x0000004050000413 0x0000703c000001c0 0x000001c0f0000007

def z690 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cc34f301dc0f1d1 0x70730d3cc07703c7

def z691 : W := mkw 0x0000000040004800 0x0000000001000120 0x00000003c000fe20 0x180000000f0003f8

def z692 : W := mkw 0x01040856221b8269 0x0004102158886e09 0x033c08fe223f002e 0x8c0cf023f888fc00

def z693 : W := mkw 0x61a69dc6e37adebd 0x09869a771b8deb7a 0xe3efbfcfc3f8fe3b 0xdf8fbeff3f0fe3f8

def z694 : W := mkw 0x9208200800000000 0x0248208020000000 0x030c300c00000000 0x000c30c030000000

def z695 : W := mkw 0x2503f00374006d80 0x10940fc00dd001b6 0x0003f003fc00fff0 0x58000fc00ff003ff

def z696 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0c38fc1c1c0fe11 0x53830e3f070703f8

def z697 : W := mkw 0xdbfc1857bbbf86e9 0x236ff0615eeefe1b 0xfffc0003ffff8fef 0xbffff0000ffffe3f

def z698 : W := mkw 0xdffd4223b9b60000 0x237ff5088ee6d800 0xffff4f33ffff003f 0xfffffd3ccffffc00

def z699 : W := mkw 0xdbfc000338960000 0x236ff0000ce25800 0xfffc00003c07000f 0xa3fff00000f01c00

def z700 : W := mkw 0xfefbefe84248da3c 0x0bfbefbfa1092368 0xfffffffc0000fe1f 0xe3fffffff00003f8

def z701 : W := mkw 0x61a69dd6e37bdefd 0x09869a775b8def7b 0xe0e38fc3e3fffffb 0xdf838e3f0f8fffff

def z702 : W := mkw 0xfffbf6ab74006d80 0x13ffefdaadd001b6 0xffc3f703fc00fff7 0xfbff0fdc0ff003ff

def z703 : W := mkw 0xd3ac1047b13a0689 0x234eb0411ec4e81a 0xe32cb0cfc0380e02 0x0b8cb2c33f00e038

def z704 : W := mkw 0xfffbf6ab70004c80 0x13ffefdaadc00132 0xffffffffc0000e1f 0xebffffffff000038

def z705 : W := mkw 0xf7a3f003f5206d80 0x13de8fc00fd481b6 0xffe3f003fff8ffff 0xffff8fc00fffe3ff

def z706 : W := mkw 0xdbfc1856221b86e9 0x036ff06158886e1b 0xfffcf8fe223f8fff 0xaffff3e3f888fe3f

def z707 : W := mkw 0xfefbe6a804002100 0x03fbef9aa0100084 0xfffffffc3c0001df 0xe3fffffff0f00007

def z708 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0e387c3c3f8fe23 0x5f838e1f0f0fe3f8

def z709 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff03b003fc00ffe3 0x7bfc0ec00ff003ff

def z710 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff03f001fc00ffd5 0x73fc0fc007f003ff

def z711 : W := mkw 0xf2aaad980ec5b172 0x07caaab6603b16c5 0xe32cb0cc3fc7f1e2 0x178cb2c330ff1fc7

def z712 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0e38fc3c3f87e0b 0x5f838e3f0f0fe1f8

def z713 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff037003fc00ffe5 0x7bfc0dc00ff003ff

def z714 : W := mkw 0xdbfc06abb9b60000 0x236ff01aaee6d800 0xfffcffffffff003f 0xbffff3fffffffc00

def z715 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x033cf8fe023f8fda 0x0c0cf3e3f808fe3f

def z716 : W := mkw 0x49f816ab74006d80 0x1127e05aadd001b6 0x00fc0ffffc00ffe8 0x1803f03ffff003ff

def z717 : W := mkw 0x200289404248da38 0x00800a2501092368 0xe0e38fc3c3f8fe3b 0xdf838e3f0f0fe3f8

def z718 : W := mkw 0xdbfc1003b9b60480 0x236ff0400ee6d812 0xfffcb003ffff0e2f 0xbffff2c00ffffc38

def z719 : W := mkw 0xdbfc1003b9b60480 0x236ff0400ee6d812 0xfffc7003ffff01ef 0xbffff1c00ffffc07

def z720 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0xfcd34f33ffc7f1ff 0xfff34d3ccfff1fc7

def z721 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfffffffe0238003f 0xeffffffff808e000

def z722 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe3ff8fc3c3f8fe3f 0xdf8ffe3f0f0fe3f8

def z723 : W := mkw 0xf6abe6a800000000 0x03daaf9aa0000000 0xe3effffc0000001b 0xc38fbffff0000000

def z724 : W := mkw 0x40a0048000000000 0x0102801200000000 0x03fcfffc0000001e 0x800ff3fff0000000

def z725 : W := mkw 0xdaf818559bad86e9 0x236be061566eb61b 0xfcc0f8fdddc08fd1 0x33f303e3f777023f

def z726 : W := mkw 0x0c5143300cc53152 0x0431450cc03314c5 0x1cc307003dc771c1 0x70730c1c00f71dc7

def z727 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xffdffffc00000015 0x63ff7ffff0000000

def z728 : W := mkw 0x9300100374006d80 0x124c00400dd001b6 0xfc000003fc00ffe1 0x3bf000000ff003ff

def z729 : W := mkw 0xb703f6ab74006d80 0x12dc0fdaadd001b6 0xff3ffffffc00ffff 0xfbfcfffffff003ff

def z730 : W := mkw 0x0c516b380ec5b172 0x043145ace03b16c5 0x1cd37f3c3fc7f1fd 0xf4734dfcf0ff1fc7

def z731 : W := mkw 0xf3a6b4c7f13a4e8d 0x1bce9ad31fc4e93a 0xe32cb0cfc0380e02 0x0b8cb2c33f00e038

def z732 : W := mkw 0x2403fff04649fffe 0x1c900fffc11927ff 0x0003fff00000ffd0 0x40000fffc00003ff

def z733 : W := mkw 0x60a28dd0c369da7c 0x09828a37430da769 0xe3ffffffe3ffffff 0xdf8fffffff8fffff

def z734 : W := mkw 0x01041056201b06c9 0x0004104158806c1b 0x033cf0fe223f0fee 0x8c0cf3c3f888fc3f

def z735 : W := mkw 0x085009100ac59070 0x00214024402b1641 0x1cd34f303fc7f1fd 0xf4734d3cc0ff1fc7

def z736 : W := mkw 0xbb52bb337ac5dcf2 0x16ed4aeccdeb1773 0xe3d0bf33c3c70e0a 0x0f8f42fccf0f1c38

def z737 : W := mkw 0xd7a17dc3b768b7bc 0x1b5e85f70edda2de 0x1fe07fc03ff801cc 0x247f81ff00ffe007

def z738 : W := mkw 0x6cf3c6f0cdad6b4e 0x0db3cf1bc336b5ad 0xfc30c0f3fc3f0fc6 0x2bf0c303cff0fc3f

def z739 : W := mkw 0xf3aeb48bf1324c80 0x33cebad22fc4c932 0xe32cb0cfc0380e02 0x0b8cb2c33f00e038

def z740 : W := mkw 0x2507e6abb9b60000 0x20941f9aaee6d800 0x0003ffffffff0030 0x5c000ffffffffc00

def z741 : W := mkw 0x48fc0b748bff927b 0x2523f02dd22ffe49 0x00fc0ffc03ff0008 0x0403f03ff00ffc00

def z742 : W := mkw 0xb603f00154006d80 0x12d80fc0055001b6 0xfc03f001fc00fff5 0xf3f00fc007f003ff

def z743 : W := mkw 0x01041956225b96f9 0x0004106558896e5b 0x0000000223ffffe0 0x1c000000088fffff

def z744 : W := mkw 0x0000000000000000 0x0000000000000000 0x03fffffc0000001f 0xc00ffffff0000000

def z745 : W := mkw 0x0c5149000ec4b130 0x00314524003b12c4 0x1cd34f003fc7f1fd 0xf4734d3c00ff1fc7

def z746 : W := mkw 0xf3aeb4c3f13a4e8c 0x3bcebad30fc4e93a 0xe32cb0c3c0380e02 0x0b8cb2c30f00e038

def z747 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe3e3ffc3c3f8fe3f 0xdf8f8fff0f0fe3f8

def z748 : W := mkw 0xdbfc022bb9b60000 0x236ff008aee6d800 0xfffc003fffff002f 0xbffff000fffffc00

def z749 : W := mkw 0xdbfc06abb9b60000 0x236ff01aaee6d800 0xfffc0703ffff002f 0xbffff01c0ffffc00

def z750 : W := mkw 0xfffffefe221b86e9 0x03fffffbf8886e1b 0xfcc30702223f8fe1 0x6ff30c1c0888fe3f

def z751 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffc4003ffff81ff 0xbffff1000ffffe07

def z752 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffc8003ffff8e3f 0xbffff2000ffffe38

def z753 : W := mkw 0xfafa848000000000 0x03ebea1200000000 0xfffffffc0000001f 0xe3fffffff0000000

def z754 : W := mkw 0x64a3e6a800000000 0x01928f9aa0000000 0xe3fffffc0000001f 0xc38ffffff0000000

def z755 : W := mkw 0xb607e855561beb69 0x12d81fa155586fad 0xfc3f08fdde3f7009 0x77f0fc23f778fdc0

def z756 : W := mkw 0x0401422000000000 0x0010050880000000 0x033ffffc0000001e 0xc00cfffff0000000

def z757 : W := mkw 0x6cfff000cdb66d80 0x31b3ffc00336d9b6 0x00fff00003ffffd8 0x4403ffc0000fffff

def z758 : W := mkw 0x9e596b68c368da3c 0x0a7965ada30da368 0x1f1c703fc3f8fe24 0x3c7c71c0ff0fe3f8

def z759 : W := mkw 0x60a28dd0c369da7c 0x09828a37430da769 0xe0e3cff3c3f8fffb 0xdf838f3fcf0fe3ff

def z760 : W := mkw 0xb707f00374126d80 0x12dc1fc00dd049b6 0xff1ff003fc07fff7 0xfbfc7fc00ff01fff

def z761 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0e38fc3c3f8fe1a 0x4f838e3f0f0fe3f8

def z762 : W := mkw 0x010419562adf96fb 0x0404106558ab7e5b 0x0000000223ff8fe0 0x0c000000088ffe3f

def z763 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0x1ffffffc0000001c 0x607ffffff0000000

def z764 : W := mkw 0xbe5be6a800000000 0x02f96f9aa0000000 0xff1ffffc00000017 0xe3fc7ffff0000000

def z765 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0e3cfc3e3f8ffff 0xdf838f3f0f8fe3ff

def z766 : W := mkw 0x0c5143300cc53152 0x0431450cc03314c5 0x1cd347303fc771ed 0xf4734d1cc0ff1dc7

def z767 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff1ff03ffc00fff7 0xfbfc7fc0fff003ff

def z768 : W := mkw 0xfefbe6a840004800 0x03fbef9aa1000120 0xfffffffdc000701f 0xf3fffffff70001c0

def z769 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xe3fffffc0000001a 0x438ffffff0000000

def z770 : W := mkw 0xfefbe6a840004800 0x03fbef9aa1000120 0xfffffffc0000fe1f 0xe3fffffff00003f8

def z771 : W := mkw 0xfefbe6a80c842100 0x03fbef9aa0321084 0xfffffffc3fc7f1ff 0xf7fffffff0ff1fc7

def z772 : W := mkw 0xdbfc1007b9b60481 0x236ff0401ee6d812 0xfffc300fffff002f 0xbffff0c03ffffc00

def z773 : W := mkw 0x61a69596e1735cd5 0x09869a565b85cd73 0xe3df773de1c771c5 0x538f7ddcf7871dc7

def z774 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff3ff003fc00ffff 0xfbfcffc00ff003ff

def z775 : W := mkw 0x0104100220120480 0x0004104008804812 0x033cf8fe223f8ffe 0x8c0cf3e3f888fe3f

def z776 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfffffffc2207003f 0xe7fffffff0881c00

def z777 : W := mkw 0xb70bf00b74006d80 0x12dc2fc02dd001b6 0xff0ff00ffc00fff7 0xfbfc3fc03ff003ff

def z778 : W := mkw 0xbe5be6a800000000 0x02f96f9aa0000000 0x1fdffffc0000001d 0xe07f7ffff0000000

def z779 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x1f3cf8fe3e3f8fff 0xbc7cf3e3f8f8fe3f

def z780 : W := mkw 0x60a2adc8c368da3c 0x09828ab7230da368 0xe0e3bfcfc3f8fe3b 0xdf838eff3f0fe3f8

def z781 : W := mkw 0xfefbe6a881200000 0x03fbef9aa2048000 0xfffffffc03f8001f 0xe7fffffff00fe000

def z782 : W := mkw 0xdbfc0483b9b60000 0x236ff0120ee6d800 0xfffc0fc3ffff002f 0xbffff03f0ffffc00

def z783 : W := mkw 0xb707f00374126d80 0x12dc1fc00dd049b6 0xff2ff003fc38fff7 0xfbfcbfc00ff0e3ff

def z784 : W := mkw 0xb603e6a800000000 0x02d80f9aa0000000 0xff3ffffc0000001f 0xe3fcfffff0000000

def z785 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x033ff8fe223fffff 0xdc0cffe3f888ffff

def z786 : W := mkw 0xb60be6a800000000 0x02d82f9aa0000000 0x030ffffc00000010 0x400c3ffff0000000

def z787 : W := mkw 0x9b54000338960000 0x026d50000ce25800 0xfffc0003ffff002f 0xbffff0000ffffc00

def z788 : W := mkw 0x49f40002a9b60000 0x0127d0000aa6d800 0xfffc0003ffff002f 0xbffff0000ffffc00

def z789 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xffff7ffc0000000d 0x63fffdfff0000000

def z790 : W := mkw 0x0c5143300cc53152 0x0431450cc03314c5 0x1cd347303dc7f1f5 0xf0734d1cc0f71fc7

def z791 : W := mkw 0x0c5143300cc53152 0x0431450cc03314c5 0x1cd34f303dc771dd 0xf0734d3cc0f71dc7

def z792 : W := mkw 0xd3a40003b1320000 0x034e90000ec4c800 0xfffc0003ffff002f 0xbffff0000ffffc00

def z793 : W := mkw 0x2403fdd44649fffd 0x18900ff7511927ff 0x0003fffc0000ffd0 0x40000ffff00003ff

def z794 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0e30fc3c3f8fe29 0x5f838c3f0f0fe3f8

def z795 : W := mkw 0xdbfc0223b9b60000 0x236ff0088ee6d800 0xfffc0f33ffff002f 0xbffff03ccffffc00

def z796 : W := mkw 0x68fa86a800000000 0x01a3ea1aa0000000 0xe3fffffc0000001f 0xc38ffffff0000000

def z797 : W := mkw 0x60a28dd4c369da7d 0x09828a37530da769 0xe0e38fffc3f8fe3b 0xdf838e3fff0fe3f8

def z798 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0xe33cf8ffe23f8fff 0x9f8cf3e3ff88fe3f

def z799 : W := mkw 0xbb5e8dc37adeda3c 0x2aed7a370deb7b68 0x1f1f8fc03c07fe14 0x607c7e3f00f01ff8

def z800 : W := mkw 0x2403e6a800000000 0x00900f9aa0000000 0x032ffffc00000012 0x400cbffff0000000

def z801 : W := mkw 0x20028940c368da3c 0x08800a25030da368 0xe0c38f03c3f8fe3b 0xdf830e3c0f0fe3f8

def z802 : W := mkw 0x01041957f77bfffd 0x180410655fddefff 0x00000003ffffffe0 0x1c0000000fffffff

def z803 : W := mkw 0x93040003b9b60000 0x224c10000ee6d800 0xfc000003ffff0021 0x3ff000000ffffc00

def z804 : W := mkw 0x2503d00374006d80 0x10940f400dd001b6 0xfc03c003fc00fff7 0xfbf00f000ff003ff

def z805 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfffffffc0000f03f 0xf3fffffff00003c0

def z806 : W := mkw 0x0850022000000000 0x0021400880000000 0x03fcfffc0000001e 0x800ff3fff0000000

def z807 : W := mkw 0xfefbe6a918840000 0x23fbef9aa4621000 0xfffffffc1c00001f 0xe3fffffff0700000

def z808 : W := mkw 0x2403f00044006d80 0x10900fc0011001b6 0xfc03f003fc00fff7 0xfbf00fc00ff003ff

def z809 : W := mkw 0xfefbe6a8c1204800 0x03fbef9aa3048120 0xffffffffc3f8fe3f 0xffffffffff0fe3f8

def z810 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffc0001ffff000d 0x37fff00007fffc00

def z811 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cf34f323ffff1ff 0xfc73cd3cc8ffffc7

def z812 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xffeffffc00000013 0x63ffbffff0000000

def z813 : W := mkw 0x48fc000089b60000 0x2123f0000226d800 0xfcfc0003ffff002f 0xbff3f0000ffffc00

def z814 : W := mkw 0xfefbe6a808840000 0x03fbef9aa0221000 0xfffffffc03c7001f 0xe7fffffff00f1c00

def z815 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cd3cf323fc7ffff 0xfc734f3cc8ff1fff

def z816 : W := mkw 0xfefbe6a808840000 0x03fbef9aa0221000 0xfffffffc3c07001f 0xe3fffffff0f01c00

def z817 : W := mkw 0xd3ac0003b9b60000 0x234eb0000ee6d800 0xff2c0003ffff0027 0xbffcb0000ffffc00

def z818 : W := mkw 0xd7ad4b33b773b172 0x275eb52cceddcec5 0xe32f4f33c038f1d2 0x4b8cbd3ccf00e3c7

def z819 : W := mkw 0x60a28dd0c369da7c 0x09828a37430da769 0xe0f38ff3c3fffe3b 0xdf83ce3fcf0ffff8

def z820 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cc347003fc7f1f5 0xf4730d1c00ff1fc7

def z821 : W := mkw 0x60aa8dc8c368da3c 0x0982aa37230da368 0xe0ef8fcfc3f8fe3b 0xdf83be3f3f0fe3f8

def z822 : W := mkw 0x9b5c0003b9b60000 0x226d70000ee6d800 0xff1c0003ffff0027 0xbffc70000ffffc00

def z823 : W := mkw 0xfefbe6a9dda46900 0x33fbef9aa77691a4 0xfffffffdddc0701f 0xf3fffffff77701c0

def z824 : W := mkw 0xb703f48b74006d80 0x12dc0fd22dd001b6 0xff03f0cffc00fff7 0xfbfc0fc33ff003ff

def z825 : W := mkw 0xfefbe6a991200000 0x23fbef9aa6448000 0xfffffffdc000001f 0xe3fffffff7000000

def z826 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0ff8fffc3f8fe3b 0xdf83fe3fff0fe3f8

def z827 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffc0003ffff000e 0x2ffff0000ffffc00

def z828 : W := mkw 0xfafaa6a800000000 0x03ebea9aa0000000 0xe3ffbffc0000001b 0xc38ffefff0000000

def z829 : W := mkw 0x9f5572373c9725c3 0x167d55c8dcf25c97 0x1f1c703c3c0701c4 0x207c71c0f0f01c07

def z830 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xffc00003ffff0027 0xbfff00000ffffc00

def z831 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff03f003fc00ffd6 0x6bfc0fc00ff003ff

def z832 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0e38fc3c1f8fe13 0x5b838e3f0f07e3f8

def z833 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffcb0cfffff002f 0xbffff2c33ffffc00

def z834 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff03f8fffc00fff7 0xfbfc0fe3fff003ff

def z835 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfffffffc03c0003f 0xf7fffffff00f0000

def z836 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfffffffc3c00003f 0xf3fffffff0f00000

def z837 : W := mkw 0xd3a40003b9b60000 0x234e90000ee6d800 0xffe00003ffff002f 0xbfff80000ffffc00

def z838 : W := mkw 0x0d5553662cde379b 0x0435554d98b378de 0x1fefb7ce1df87e03 0x787fbedf3877e1f8

def z839 : W := mkw 0xdafc000199b60000 0x236bf0000666d800 0xfcfc0003dfff002b 0xbff3f0000f7ffc00

def z840 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x033cf8fe203f8fd6 0x080cf3e3f880fe3f

def z841 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xffffffffc000003f 0xfbffffffff000000

def z842 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfffffffc200081ff 0xe3fffffff0800207

def z843 : W := mkw 0x60a285c0c1685a1c 0x09828a170305a168 0xe0e387c3c3f87e2b 0xdf838e1f0f0fe1f8

def z844 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff23f8c3fc00ffff 0xfbfc8fe30ff003ff

def z845 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cd30f303fc7f1e9 0x74734c3cc0ff1fc7

def z846 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0c38703c3f8fe33 0xdf830e1c0f0fe3f8

def z847 : W := mkw 0x0c514b700ecdb37a 0x0431452dc03b36cd 0x1cd3cff03fc7fffd 0xf4734f3fc0ff1fff

def z848 : W := mkw 0xdbfc1003b9b60480 0x236ff0400ee6d812 0xfffcf8ffffff8fff 0xbffff3e3fffffe3f

def z849 : W := mkw 0x01041956efffffff 0x0c0410655bbfffff 0x00000003ffffffe0 0x1c0000000fffffff

def z850 : W := mkw 0xb707f00774126d81 0x12dc1fc01dd049b6 0xff0ff00ffc00fff7 0xfbfc3fc03ff003ff

def z851 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffc0003dfff000b 0x3ffff0000f7ffc00

def z852 : W := mkw 0xb703f6ab74006d80 0x12dc0fdaadd001b6 0xff03f703fc00fff7 0xfbfc0fdc0ff003ff

def z853 : W := mkw 0xb70ff00374126d80 0x32dc3fc00dd049b6 0xff0ff003fc00fff7 0xfbfc3fc00ff003ff

def z854 : W := mkw 0x00041854021b86e9 0x0000106150086e1b 0x033cf8fc023f8fde 0x840cf3e3f008fe3f

def z855 : W := mkw 0xb707f00374126d80 0x12dc1fc00dd049b6 0xff3ff8fffe3fffff 0xfffcffe3fff8ffff

def z856 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xffdc0003ffff0025 0x3fff70000ffffc00

def z857 : W := mkw 0xfefbe6a999a40000 0x23fbef9aa6669000 0xffffffffdff8003f 0xffffffffff7fe000

def z858 : W := mkw 0xdbfc200bb9b60000 0x236ff0802ee6d800 0xfffc300fffff002f 0xbffff0c03ffffc00

def z859 : W := mkw 0x01041957bfffb7fb 0x240410655efffedf 0x00000003ffffffe0 0x1c0000000fffffff

def z860 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x03fcf8fe23ff8fff 0x9c0ff3e3f88ffe3f

def z861 : W := mkw 0x2403eff84649fb7e 0x0c900fbfe11927ed 0x0003fffc0000ffd0 0x40000ffff00003ff

def z862 : W := mkw 0x48f40ff48bff927f 0x0d23d03fd22ffe49 0x00fc0ffc03ff0008 0x0403f03ff00ffc00

def z863 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xffff0003fffff03f 0xfffffc000fffffc0

def z864 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xff3ffffc00000016 0x63fcfffff0000000

def z865 : W := mkw 0x48fc0ff08bff927e 0x2d23f03fc22ffe49 0x00fc0ff003ff0008 0x0403f03fc00ffc00

def z866 : W := mkw 0xfefbe7a8cde47916 0x0ffbef9ea33791e4 0xfcc30701ddc07001 0x73f30c1c077701c0

def z867 : W := mkw 0xf6a3e48000000000 0x03da8f9200000000 0xfffffffc0000001f 0xe3fffffff0000000

def z868 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x033cf8fe223f0fce 0x0c0cf3e3f888fc3f

def z869 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x033cf0fe223f8fe6 0x0c0cf3c3f888fe3f

def z870 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cc30f003fc7f1f9 0xf4730c3c00ff1fc7

def z871 : W := mkw 0xdbfc1003b9b60480 0x236ff0400ee6d812 0xfffc0003ffff8fef 0xbffff0000ffffe3f

def z872 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe3efbfcfc3f8fe3b 0xdf8fbeff3f0fe3f8

def z873 : W := mkw 0xfefbe6a80c842102 0x07fbef9aa0321084 0xfffffffc1c00001f 0xe3fffffff0700000

def z874 : W := mkw 0xfefbe6a808840000 0x03fbef9aa0221000 0xfffffffc1dc0001f 0xf3fffffff0770000

def z875 : W := mkw 0xb703f22b74006d80 0x12dc0fc8add001b6 0xff03f03ffc00fff7 0xfbfc0fc0fff003ff

def z876 : W := mkw 0x9f5d52373c9725c3 0x267d7548dcf25c97 0x1f1c703c3c0701c4 0x207c71c0f0f01c07

def z877 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xfc038003fc00fff3 0xfbf00e000ff003ff

def z878 : W := mkw 0x60a28480c1204800 0x01828a1203048120 0xe0e38fc3c3f8fe3b 0xdf838e3f0f0fe3f8

def z879 : W := mkw 0x60a28dd0c369da7c 0x09828a37430da769 0xe0e38fc3e3fffffb 0xdf838e3f0f8fffff

def z880 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xfc034003fc00fff5 0xfbf00d000ff003ff

def z881 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xffc3f003ffc0ffff 0xffff0fc00fff03ff

def z882 : W := mkw 0xb302b00374006d80 0x12cc0ac00dd001b6 0xff00b003fc00ffe7 0xbbfc02c00ff003ff

def z883 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cd3fffc3fc7f1fd 0xf4734ffff0ff1fc7

def z884 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xffc3ff03fc00ffff 0xfbff0ffc0ff003ff

def z885 : W := mkw 0xdaf826a800000000 0x036be09aa0000000 0x03fc3ffc00000008 0x000ff0fff0000000

def z886 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfcd00003ffff002d 0xbff340000ffffc00

def z887 : W := mkw 0xf2aaa48800000000 0x03caaa9220000000 0xe3fffffc0000001f 0xc38ffffff0000000

def z888 : W := mkw 0x2403e6a800000000 0x00900f9aa0000000 0x031ffffc00000014 0x400c7ffff0000000

def z889 : W := mkw 0x40a0094083689238 0x01028025020da248 0xe0e38fc3c3f8fe3b 0xdf838e3f0f0fe3f8

def z890 : W := mkw 0x48f806a800000000 0x0123e01aa0000000 0x03fc7ffc0000000c 0x000ff1fff0000000

def z891 : W := mkw 0xfefbe6a881200000 0x03fbef9aa2048000 0xfffffffdc1c0001f 0xf3fffffff7070000

def z892 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff030003fc00ffe7 0xfbfc0c000ff003ff

def z893 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cf3cff03fc7f1ff 0xf473cf3fc0ff1fc7

def z894 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffc703fffff002f 0xbffff1c0fffffc00

def z895 : W := mkw 0x01041956225b96f9 0x0004106558896e5b 0x033cf8fe23fffffe 0x9c0cf3e3f88fffff

def z896 : W := mkw 0xb302900374006d80 0x12cc0a400dd001b6 0xff038003fc00fff7 0xfbfc0e000ff003ff

def z897 : W := mkw 0x0c514b700ecdb37a 0x0431452dc03b36cd 0x1ffffffe3fffffff 0xfc7ffffff8ffffff

def z898 : W := mkw 0xfafaa6a800000000 0x03ebea9aa0000000 0xe3fcfffc0000001e 0x838ff3fff0000000

def z899 : W := mkw 0xbe5be6a800000000 0x02f96f9aa0000000 0x1f3ffffc0000001e 0xe07cfffff0000000

def z900 : W := mkw 0xfefbe6a844006900 0x03fbef9aa11001a4 0xfffffffffc00ffff 0xfbfffffffff003ff

def z901 : W := mkw 0x01041956265bb7fb 0x0404106558996edf 0x00000002223fffe0 0x0c0000000888ffff

def z902 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cc34f303fc7f1f1 0x74730d3cc0ff1fc7

def z903 : W := mkw 0xdbfc3003b9b60480 0x336ff0c00ee6d812 0xfffc3003ffff002f 0xbffff0c00ffffc00

def z904 : W := mkw 0x01041956a37b96fd 0x080410655a8dee5b 0x0000000223ff8fe0 0x0c000000088ffe3f

def z905 : W := mkw 0xb603e00044006900 0x02d80f80011001a4 0xff03f003fc00fff7 0xfbfc0fc00ff003ff

def z906 : W := mkw 0xdbfc048bb9b60000 0x236ff0122ee6d800 0xfffc00cfffff002f 0xbffff0033ffffc00

def z907 : W := mkw 0xfefbe6a999a40000 0x23fbef9aa6669000 0xfffffffdffc7003f 0xf7fffffff7ff1c00

def z908 : W := mkw 0x01041956225b96f9 0x0004106558896e5b 0x03fcfffe23ff8ffe 0x8c0ff3fff88ffe3f

def z909 : W := mkw 0xdafc000199b60000 0x236bf0000666d800 0xfcc00001dfff0001 0x37f30000077ffc00

def z910 : W := mkw 0x40a00940c368da3c 0x09028025030da368 0xe0e30f03c3f8fe3b 0xdf838c3c0f0fe3f8

def z911 : W := mkw 0x01041857321b86e9 0x000410615cc86e1b 0x033cf8fffe3f8ffe 0x9c0cf3e3fff8fe3f

def z912 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xffec0003ffff0023 0x3fffb0000ffffc00

def z913 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0c30f03c3f8fe39 0xdf830c3c0f0fe3f8

def z914 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff00f003fc00ffe6 0x3bfc03c00ff003ff

def z915 : W := mkw 0xdbf00003b9a40000 0x036fc0000ee69000 0xfff00003ffff002f 0xbfffc0000ffffc00

def z916 : W := mkw 0xfefbe6a8c1204804 0x0bfbef9aa3048120 0xfffffffdc000001f 0xe3fffffff7000000

def z917 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffcf003ffff003f 0xbffff3c00ffffc00

def z918 : W := mkw 0x49f40003b9b60000 0x2127d0000ee6d800 0xfcf00003ffff002f 0xbff3c0000ffffc00

def z919 : W := mkw 0xfefbe6a914002100 0x13fbef9aa4500084 0xfffffffc1c00001f 0xe3fffffff0700000

def z920 : W := mkw 0x48fc0dd48bff927d 0x2923f037522ffe49 0x00fc0ffc03ff0008 0x0403f03ff00ffc00

def z921 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1fd3ff303fc7f1ff 0xf47f4ffcc0ff1fc7

def z922 : W := mkw 0x9701700374006d80 0x125c05c00dd001b6 0xff007003fc00ffe7 0xbbfc01c00ff003ff

def z923 : W := mkw 0x2403fb744649fffb 0x14900fedd11927ff 0x0003fffc0000ffd0 0x40000ffff00003ff

def z924 : W := mkw 0x9300100374006d80 0x124c00400dd001b6 0xff00f003fc00fff7 0xbbfc03c00ff003ff

def z925 : W := mkw 0xfefbe6a889a40000 0x03fbef9aa2269000 0xffffffffffff003f 0xfffffffffffffc00

def z926 : W := mkw 0xf6abe6a800000000 0x03daaf9aa0000000 0xe33ffffc0000001e 0xc38cfffff0000000

def z927 : W := mkw 0x0c514b700ecdb37a 0x0431452dc03b36cd 0x1cd34f323ffffffd 0xfc734d3cc8ffffff

def z928 : W := mkw 0xf3ae94c7f13a4e8d 0x2bceba531fc4e93a 0xe32cb0cfc0380e02 0x0b8cb2c33f00e038

def z929 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cd307003fc7f1ed 0xf4734c1c00ff1fc7

def z930 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cd34f303fc7f1dc 0x64734d3cc0ff1fc7

def z931 : W := mkw 0x0c5142200c842100 0x0031450880321084 0x1cd34f303fc7f1fd 0xf4734d3cc0ff1fc7

def z932 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cff4ffc3fc7f1fd 0xf473fd3ff0ff1fc7

def z933 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfffcfffc0000000e 0x23fff3fff0000000

def z934 : W := mkw 0x2002848000000000 0x00800a1200000000 0x033ffffc0000001e 0xc00cfffff0000000

def z935 : W := mkw 0x9701500374006d80 0x125c05400dd001b6 0xff034003fc00fff7 0xfbfc0d000ff003ff

def z936 : W := mkw 0x48f80ff88bed927e 0x0d23e03fe22fb649 0x00fc0ffc03ff0008 0x0403f03ff00ffc00

def z937 : W := mkw 0xfefbe6a881200000 0x03fbef9aa2048000 0xffffffffc038001f 0xebffffffff00e000

def z938 : W := mkw 0x9b540003b9b60000 0x226d50000ee6d800 0xffd00003ffff002f 0xbfff40000ffffc00

def z939 : W := mkw 0x9e59622800000000 0x02796588a0000000 0x1ffffffc0000001f 0xe07ffffff0000000

def z940 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff13f833fc00ffff 0xfbfc4fe0cff003ff

def z941 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffc08ffffff002f 0xbffff023fffffc00

def z942 : W := mkw 0x040149100ec5b172 0x04100524403b16c5 0x1cc34f003fc7f1fd 0xf4730d3c00ff1fc7

def z943 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff03f003dc00ffd3 0x7bfc0fc00f7003ff

def z944 : W := mkw 0x6cf3c6a000000000 0x01b3cf1a80000000 0xfffffffc0000001f 0xe3fffffff0000000

def z945 : W := mkw 0x93040003b9b60000 0x224c10000ee6d800 0xff3c0003ffff002f 0xbffcf0000ffffc00

def z946 : W := mkw 0x0c514b740ecdb37b 0x0431452dd03b36cd 0x1cd34ffc3fc7f1fd 0xf4734d3ff0ff1fc7

def z947 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x03fffffe223f8fff 0xcc0ffffff888fe3f

def z948 : W := mkw 0xfefbe6a840004800 0x03fbef9aa1000120 0xffffffffc0000e1f 0xebffffffff000038

def z949 : W := mkw 0x60a28900c360d830 0x01828a24030d8360 0xe0e38f03c3f8fe3b 0xdf838e3c0f0fe3f8

def z950 : W := mkw 0x2403dff44649ffff 0x0c900f7fd11927ff 0x0003fffc0000ffd0 0x40000ffff00003ff

def z951 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfce00003ffff002b 0xbff380000ffffc00

def z952 : W := mkw 0x60a285c0c1685a1c 0x09828a170305a168 0xe0e387c3c1f8fe33 0xdb838e1f0f07e3f8

def z953 : W := mkw 0xdafc000199b60000 0x236bf0000666d800 0xfcfc0001ffff002d 0xb7f3f00007fffc00

def z954 : W := mkw 0x48f806a800000000 0x0123e01aa0000000 0x03fcbffc0000000a 0x000ff2fff0000000

def z955 : W := mkw 0x9f5d722b3c962580 0x327d75c8acf25896 0x1f1c703c3c0701c4 0x207c71c0f0f01c07

def z956 : W := mkw 0x60a285c0c1685a1c 0x09828a170305a168 0xe0e38fc3c1f87e1b 0xdb838e3f0f07e1f8

def z957 : W := mkw 0xfefbe6a954006900 0x13fbef9aa55001a4 0xffffffffdc00fe3f 0xfbffffffff7003f8

def z958 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0e30703c3f8fe2b 0xdf838c1c0f0fe3f8

def z959 : W := mkw 0x085009100ec5b172 0x04214024403b16c5 0x1cd30f003fc7f1fd 0xf4734c3c00ff1fc7

def z960 : W := mkw 0xfefbe6a954006900 0x13fbef9aa55001a4 0xfffffffdfc00f1ff 0xf3fffffff7f003c7

def z961 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cd34f303fc771cd 0x74734d3cc0ff1dc7

def z962 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cd347303fc7f1e5 0x74734d1cc0ff1fc7

def z963 : W := mkw 0x01041957fbffdefd 0x280410655fefff7b 0x00000003ffffffe0 0x1c0000000fffffff

def z964 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff13f003fe07ffff 0xfffc4fc00ff81fff

def z965 : W := mkw 0x040149100641b170 0x00100524401906c5 0x1cd34f303fc7f1fd 0xf4734d3cc0ff1fc7

def z966 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1fdf7f3c3fc7f1fd 0xf47f7dfcf0ff1fc7

def z967 : W := mkw 0xdef966a800000000 0x037be59aa0000000 0x1ffcfffc0000001e 0xa07ff3fff0000000

def z968 : W := mkw 0xfefbe6a9dda46900 0x33fbef9aa77691a4 0xfcc30701ddc07001 0x73f30c1c077701c0

def z969 : W := mkw 0xdaf8000199a40000 0x236be00006669000 0xfcf00003ffff002f 0xbff3c0000ffffc00

def z970 : W := mkw 0xdef9422000000000 0x037be50880000000 0xfffffffc0000001f 0xe3fffffff0000000

def z971 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffc88c3ffff003f 0xbffff2230ffffc00

def z972 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1fff4f303fc7f1ff 0xf47ffd3cc0ff1fc7

def z973 : W := mkw 0xb603f00154006d80 0x12d80fc0055001b6 0xfc03f003dc00fff3 0xfbf00fc00f7003ff

def z974 : W := mkw 0xb707f00374126d80 0x12dc1fc00dd049b6 0xff03f003fe3ffff7 0xfffc0fc00ff8ffff

def z975 : W := mkw 0xb703f48374006d80 0x12dc0fd20dd001b6 0xff03ffc3fc00fff7 0xfbfc0fff0ff003ff

def z976 : W := mkw 0x9e5966a800000000 0x0279659aa0000000 0x1f1c7ffc00000004 0x207c71fff0000000

def z977 : W := mkw 0xb302900370004c80 0x02cc0a400dc00132 0xff03f003fc00fff7 0xfbfc0fc00ff003ff

def z978 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfcfc0003ffff0029 0x3ff3f0000ffffc00

def z979 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xff3c0003ffff0026 0x3ffcf0000ffffc00

def z980 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff2ff0cffc00fff7 0xfbfcbfc33ff003ff

def z981 : W := mkw 0xb603f00154006d80 0x12d80fc0055001b6 0xff03f001dc00ffd7 0xf3fc0fc0077003ff

def z982 : W := mkw 0xf6abe6a800000000 0x03daaf9aa0000000 0xff2ffffc00000017 0xe3fcbffff0000000

def z983 : W := mkw 0x010419577edffffb 0x140410655dfb7fff 0x00000003ffffffe0 0x1c0000000fffffff

def z984 : W := mkw 0x0c5143200cc43112 0x0431450c803310c4 0x1cd347003fc7f1fd 0xf4734d1c00ff1fc7

def z985 : W := mkw 0x01041956225b96f9 0x0004106558896e5b 0x033ffffe223ffffe 0xcc0cfffff888ffff

def z986 : W := mkw 0x9f5d72333c9725c2 0x367d75c8ccf25c97 0x1f1c70303c0701c4 0x207c71c0c0f01c07

def z987 : W := mkw 0x0c514b300ec5b172 0x0431452cc03b16c5 0x1cd34f303dc7f1d5 0x70734d3cc0f71fc7

def z988 : W := mkw 0x9701500334002580 0x025c05400cd00096 0xff03f003fc00fff7 0xfbfc0fc00ff003ff

def z989 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xff23f003fe38ffff 0xfffc8fc00ff8e3ff

def z990 : W := mkw 0xdef966a800000000 0x037be59aa0000000 0x1fff7ffc0000001d 0xe07ffdfff0000000

def z991 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xfffffffe00008e3f 0xebfffffff8000238

def z992 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0f38fc3e3fffe3f 0xdf83ce3f0f8ffff8

def z993 : W := mkw 0xdef966a800000000 0x037be59aa0000000 0xfffc7ffc0000000f 0xa3fff1fff0000000

def z994 : W := mkw 0x0c594b380ec5b172 0x0431652ce03b16c5 0x1cdf4f3c3fc7f1fd 0xf4737d3cf0ff1fc7

def z995 : W := mkw 0xdafc000199b60000 0x236bf0000666d800 0xfffc0001dfff000f 0xb7fff000077ffc00

def z996 : W := mkw 0xfafaa6a800000000 0x03ebea9aa0000000 0xfffcbffc0000000f 0xa3fff2fff0000000

def z997 : W := mkw 0xfefbe6a910000000 0x03fbef9aa4400000 0xfffffffddc00001f 0xf3fffffff7700000

def z998 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0c38fc3c3f8fe31 0x5f830e3f0f0fe3f8

def z999 : W := mkw 0x01041956625bdefd 0x0804106559896f7b 0x00000002223fffe0 0x0c0000000888ffff

def z1000 : W := mkw 0x000006a800000000 0x0000001aa0000000 0x033cfffc0000001e 0x800cf3fff0000000

def z1001 : W := mkw 0x2503d00264006d80 0x00940f40099001b6 0xff03f003fc00fff7 0xfbfc0fc00ff003ff

def z1002 : W := mkw 0x2c53e6a800000000 0x00b14f9aa0000000 0x1ffffffc0000001f 0xe07ffffff0000000

def z1003 : W := mkw 0xfefbe6a804002100 0x03fbef9aa0100084 0xfffffffc1c00701f 0xf3fffffff07001c0

def z1004 : W := mkw 0x60a28580c1605814 0x09828a1603058160 0xe0e38703c3f8fe3b 0xdf838e1c0f0fe3f8

def z1005 : W := mkw 0x0000085002098268 0x0000002140082609 0x033cf8fe223f8ffe 0x8c0cf3e3f888fe3f

def z1006 : W := mkw 0xfefbe6a950004800 0x13fbef9aa5400120 0xfffffffdc000001f 0xe3fffffff7000000

def z1007 : W := mkw 0x0c514b700ecdb37a 0x0431452dc03b36cd 0x1cf34ff03ffff1fd 0xf473cd3fc0ffffc7

def z1008 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xffff0f03ffff003f 0xfffffc3c0ffffc00

def z1009 : W := mkw 0xfefbe6a804002100 0x03fbef9aa0100084 0xfffffffc0000f1df 0xe3fffffff00003c7

def z1010 : W := mkw 0xbe53e22000000000 0x02f94f8880000000 0xfffffffc0000001f 0xe3fffffff0000000

def z1011 : W := mkw 0xb703c00374006900 0x02dc0f000dd001a4 0xff03c003fc00fff7 0xfbfc0f000ff003ff

def z1012 : W := mkw 0xb603f00154006d80 0x12d80fc0055001b6 0xfc030001dc00ffc1 0x73f00c00077003ff

def z1013 : W := mkw 0xfefbe6a844006900 0x13fbef9aa11001a4 0xfffffffc0000701f 0xe3fffffff00001c0

def z1014 : W := mkw 0xdaf806a800000000 0x036be01aa0000000 0xfffcfffc0000001f 0xa3fff3fff0000000

def z1015 : W := mkw 0xb603e00154006900 0x12d80f80055001a4 0xfc03c003fc00fff7 0xfbf00f000ff003ff

def z1016 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0e3ffffc3f8fe3b 0xdf838fffff0fe3f8

def z1017 : W := mkw 0x60a285c0c1685a1c 0x09828a170305a168 0xe0c30703c1f87e01 0x5b830c1c0f07e1f8

def z1018 : W := mkw 0xf2aaa6a800000000 0x03caaa9aa0000000 0xe32cbffc00000002 0x038cb2fff0000000

def z1019 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xe0f3cff3c3f8fe3f 0xdf83cf3fcf0fe3f8

def z1020 : W := mkw 0x4cf946a800000000 0x0133e51aa0000000 0x1ffffffc0000001f 0xe07ffffff0000000

def z1021 : W := mkw 0xdaf8000089a40000 0x036be00002269000 0xfffc0003ffff002f 0xbffff0000ffffc00

def z1022 : W := mkw 0x01041056201b06c9 0x0004104158806c1b 0x033cf0fe203f8ff6 0x880cf3c3f880fe3f

def z1023 : W := mkw 0x01041056201b06c9 0x0004104158806c1b 0x033cf8fe203f0fde 0x880cf3e3f880fc3f

def z1024 : W := mkw 0x60a28dc0c368da3c 0x09828a37030da368 0xfce38fc3fff8fe3f 0xfff38e3f0fffe3f8

def z1025 : W := mkw 0xfefbe6a889a40000 0x23fbef9aa2269000 0xfffffffc01c0001f 0xe3fffffff0070000

def z1026 : W := mkw 0xb703f22374006d80 0x12dc0fc88dd001b6 0xff03ff33fc00fff7 0xfbfc0ffccff003ff

def z1027 : W := mkw 0x01041856221b86e9 0x0004106158886e1b 0x033cf8fc223f8fdc 0x040cf3e3f088fe3f

def z1028 : W := mkw 0xfefbe6a800000000 0x03fbef9aa0000000 0xffffbffc0000000b 0x63fffefff0000000

def z1029 : W := mkw 0xb703f00374006d80 0x12dc0fc00dd001b6 0xfc03f003fc00fff1 0x7bf00fc00ff003ff

def z1030 : W := mkw 0xdbfc0003b9b60000 0x236ff0000ee6d800 0xfffc4833ffff003f 0xbffff120cffffc00

def z1031 : W := mkw 0x6cfbe6a800000000 0x01b3ef9aa0000000 0x03fffffc0000001e 0xc00ffffff0000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z7,z4,z5,z6])],[(0,[z8,z0,z1,z3,z9,z5,z6]),(0,[z0,z10,z1,z11,z3,z5,z6]),(0,[z0,z12,z1,z3,z4,z5,z6]),(0,[z13,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z14,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z16,z6])],[(0,[z0,z1,z3,z17,z4,z5,z6]),(0,[z18,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z1,z19,z3,z4,z5,z6]),(0,[z20,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z21]),(0,[z22,z1,z3,z23,z4,z5,z6]),(0,[z24,z0,z1,z3,z4,z5,z6]),(0,[z25,z0,z1,z3,z4,z5,z6]),(0,[z26,z0,z1,z3,z4,z5,z6]),(0,[z0,z27,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z28,z4,z5,z6]),(0,[z29,z0,z1,z3,z4,z5,z6])],[(0,[z30,z0,z31,z3,z4,z5,z6]),(0,[z0,z1,z3,z32,z4,z5,z6]),(1,[z0,z1,z3,z33,z5,z6])],[(0,[z34,z0,z1,z3,z35,z5,z6]),(0,[z0,z1,z3,z4,z5,z36,z6]),(0,[z0,z1,z3,z4,z5,z37,z6])]],
   [[(1,[z38,z1,z3,z4,z39,z6]),(0,[z0,z1,z3,z4,z39,z6,z40]),(0,[z34,z0,z1,z3,z41,z5,z6]),(0,[z0,z1,z42,z4,z5,z43,z6])],[(0,[z0,z1,z44,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z45,z5,z6]),(0,[z0,z46,z1,z3,z4,z5,z6])],[(0,[z0,z47,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z48]),(0,[z0,z49,z1,z3,z4,z50,z6]),(0,[z51,z0,z1,z3,z4,z5,z6])],[(0,[z0,z52,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z53]),(0,[z54,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z55,z3,z4,z5,z6]),(0,[z0,z1,z56,z3,z4,z5,z57])],[(0,[z0,z1,z3,z4,z58,z5,z6]),(1,[z0,z1,z3,z4,z59,z6]),(0,[z0,z1,z3,z60,z4,z5,z6])],[(0,[z61,z1,z62,z3,z4,z5,z6]),(0,[z0,z1,z63,z3,z4,z5,z6]),(0,[z0,z1,z3,z64,z4,z5,z6])],[(0,[z0,z1,z65,z3,z4,z5,z6])],[(0,[z22,z0,z1,z23,z4,z5,z6]),(0,[z0,z1,z66,z3,z4,z5,z6]),(0,[z0,z1,z67,z3,z4,z5,z6]),(1,[z34,z1,z3,z4,z5,z68]),(0,[z34,z0,z1,z69,z3,z4,z5]),(0,[z34,z70,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z71]),(0,[z72,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z5,z73,z6,z68]),(0,[z0,z74,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z75,z4,z5,z6]),(0,[z76,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z19,z3,z5,z77,z6]),(0,[z0,z1,z3,z4,z5,z77,z6])],[(0,[z0,z1,z3,z78,z4,z5,z6]),(0,[z0,z1,z79,z3,z9,z5,z6]),(0,[z0,z1,z80,z3,z4,z5,z6]),(0,[z81,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z82,z6]),(0,[z0,z1,z3,z4,z83,z5,z6]),(0,[z0,z84,z1,z3,z4,z5,z6])],[(1,[z85,z86,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z4,z87,z6]),(0,[z0,z88,z1,z3,z4,z5,z6]),(0,[z0,z1,z89,z3,z4,z5,z6])],[(0,[z0,z1,z67,z3,z4,z39,z5]),(0,[z0,z1,z90,z3,z4,z5,z6])],[(0,[z0,z86,z3,z91,z4,z5,z6])],[(0,[z92,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z93,z3,z4,z5,z6]),(0,[z0,z1,z3,z35,z4,z5,z6]),(0,[z15,z0,z1,z69,z3,z4,z5]),(0,[z0,z1,z94,z3,z4,z5,z6]),(0,[z0,z95,z49,z3,z4,z5,z6])],[(0,[z96,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z97,z23,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z98,z6]),(1,[z0,z1,z99,z4,z5,z6]),(1,[z100,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z101,z5,z6]),(0,[z102,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z103,z6])]],
   [[],[(0,[z104,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z23,z4,z5,z6,z57]),(0,[z0,z1,z105,z3,z23,z4,z5]),(0,[z0,z1,z3,z4,z106,z5,z6]),(0,[z0,z1,z3,z107,z4,z5,z6])],[(0,[z108,z0,z31,z3,z4,z5,z6]),(0,[z109,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z110,z3,z5,z6]),(0,[z0,z111,z1,z3,z4,z5,z6]),(0,[z112,z0,z1,z3,z4,z5,z6]),(0,[z113,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z114,z3,z4,z5,z6])],[(0,[z115,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z116]),(0,[z0,z49,z1,z117,z3,z4,z6]),(0,[z118,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z39,z5,z6])],[(0,[z22,z61,z1,z3,z4,z5,z6]),(0,[z0,z119,z1,z3,z4,z5,z6]),(0,[z0,z1,z79,z120,z3,z5,z6]),(0,[z0,z1,z121,z3,z4,z5,z6])],[(0,[z0,z1,z122,z3,z4,z5,z6]),(0,[z34,z0,z123,z3,z4,z5,z6]),(0,[z0,z1,z3,z124,z4,z5,z6]),(0,[z0,z1,z125,z3,z91,z4,z6]),(0,[z126,z0,z1,z3,z4,z5,z6]),(0,[z127,z0,z1,z3,z4,z5,z6]),(0,[z0,z95,z1,z3,z4,z128,z6]),(0,[z0,z1,z120,z3,z129,z4,z6]),(0,[z130,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z131,z86,z3,z4,z5,z6])],[(0,[z0,z1,z132,z3,z4,z5,z6])],[(0,[z0,z1,z3,z133,z4,z5,z6]),(0,[z0,z1,z3,z134,z4,z5,z6]),(0,[z0,z1,z135,z3,z4,z5,z6]),(0,[z0,z1,z3,z136,z4,z5,z6]),(0,[z137,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z138]),(0,[z139,z0,z1,z56,z3,z4,z6])],[(0,[z140,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z141,z5,z6]),(0,[z22,z0,z1,z62,z4,z5,z6]),(0,[z142,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z143]),(0,[z0,z1,z3,z4,z5,z6,z144]),(0,[z0,z1,z110,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z145,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z146]),(0,[z0,z147,z1,z3,z4,z5,z6]),(0,[z148,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z149,z3,z4,z5,z6])],[(0,[z85,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z150,z6]),(0,[z0,z1,z3,z4,z5,z151,z6]),(0,[z0,z1,z152,z3,z4,z5,z6]),(0,[z0,z1,z153,z3,z4,z5,z154]),(1,[z0,z1,z69,z4,z5,z57]),(0,[z155,z0,z1,z3,z4,z5,z6])],[(0,[z0,z156,z1,z3,z4,z5,z6]),(0,[z157,z100,z1,z3,z4,z5,z6]),(0,[z158,z0,z1,z3,z4,z5,z6])],[(0,[z85,z86,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z159,z5,z6]),(1,[z108,z0,z3,z4,z5,z160])]],
   [[(0,[z0,z1,z3,z4,z39,z6,z161])],[(0,[z0,z1,z3,z4,z5,z6,z162]),(1,[z0,z1,z3,z4,z5,z163]),(1,[z0,z1,z164,z42,z4,z6]),(0,[z0,z1,z153,z3,z165,z4,z5])],[(1,[z0,z131,z97,z4,z5,z6]),(0,[z0,z1,z3,z4,z166,z5,z6]),(0,[z0,z167,z1,z3,z4,z5,z6]),(0,[z168,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z105,z3,z4,z5]),(0,[z0,z1,z97,z62,z4,z5,z6]),(0,[z0,z1,z169,z3,z4,z5,z6]),(0,[z0,z1,z170,z3,z4,z5,z6]),(0,[z0,z1,z171,z3,z4,z5,z6]),(0,[z0,z1,z3,z172,z4,z5,z6])],[(0,[z0,z31,z3,z91,z4,z5,z6]),(0,[z8,z1,z3,z4,z173,z5,z6]),(0,[z0,z1,z3,z174,z4,z5,z6]),(0,[z175,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z176,z5,z6]),(0,[z177,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z9,z4,z173,z5,z6]),(0,[z178,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z179,z4,z5,z6]),(0,[z0,z1,z3,z4,z180,z5,z6]),(0,[z0,z181,z1,z3,z4,z5,z6])],[(0,[z0,z1,z23,z91,z4,z5,z6]),(0,[z0,z182,z1,z3,z23,z4,z5]),(0,[z0,z1,z120,z3,z5,z6,z183])],[(1,[z0,z1,z184,z4,z5,z6]),(0,[z0,z185,z1,z3,z4,z5,z6]),(0,[z0,z95,z1,z3,z4,z5,z6]),(0,[z0,z95,z1,z164,z3,z4,z6]),(0,[z0,z1,z186,z3,z4,z5,z6]),(0,[z0,z1,z3,z187,z4,z5,z6])]],
   [[(0,[z188,z0,z1,z3,z4,z5,z6]),(1,[z0,z189,z1,z3,z4,z5]),(0,[z190,z0,z1,z3,z4,z5,z6]),(0,[z0,z95,z1,z3,z4,z50,z6]),(0,[z0,z191,z1,z3,z4,z5,z6]),(0,[z192,z0,z1,z3,z4,z5,z183]),(0,[z0,z1,z193,z3,z4,z5,z6])],[(0,[z0,z194,z1,z3,z4,z5,z6]),(0,[z0,z1,z195,z3,z4,z5,z6]),(1,[z0,z1,z196,z3,z4,z6]),(0,[z0,z1,z197,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z198,z5,z6]),(0,[z0,z1,z199,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z200,z5,z6]),(0,[z0,z1,z3,z4,z201,z5,z6]),(0,[z0,z1,z202,z3,z4,z5,z6]),(0,[z203,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z4,z204,z5,z6]),(0,[z0,z1,z205,z3,z4,z5,z6])],[(0,[z38,z0,z1,z3,z4,z206,z6]),(0,[z0,z1,z3,z4,z5,z6,z207]),(0,[z0,z1,z3,z4,z5,z6,z208]),(0,[z0,z1,z3,z4,z5,z6,z209]),(0,[z210,z0,z1,z3,z4,z5,z6])],[(0,[z0,z211,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z25,z1,z3,z4,z5,z206,z6]),(0,[z0,z1,z212,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z213]),(0,[z0,z147,z1,z3,z4,z5,z154]),(0,[z0,z1,z3,z4,z5,z6,z214]),(0,[z0,z1,z3,z215,z4,z5,z6])],[(0,[z61,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z87,z6]),(1,[z25,z1,z3,z4,z206,z6]),(0,[z0,z1,z3,z4,z216,z5,z6]),(0,[z0,z1,z3,z217,z4,z5,z6]),(0,[z0,z10,z1,z3,z218,z5,z6]),(1,[z0,z1,z3,z4,z5,z219]),(0,[z220,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z164,z117,z4,z5,z6]),(0,[z0,z1,z164,z3,z4,z43,z6]),(0,[z0,z1,z79,z3,z129,z5,z6])],[(0,[z0,z1,z3,z221,z4,z5,z6]),(0,[z0,z1,z222,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z223,z3,z4,z5,z6])],[(0,[z224,z0,z1,z3,z173,z5,z6]),(0,[z0,z1,z225,z3,z4,z5,z6]),(0,[z0,z1,z3,z226,z4,z5,z6])],[(1,[z30,z31,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z227,z6]),(0,[z0,z1,z11,z4,z5,z77,z6]),(0,[z0,z228,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z229,z4,z5,z6])],[(0,[z0,z1,z3,z4,z230,z5,z6]),(0,[z0,z1,z3,z231,z4,z5,z6]),(1,[z0,z1,z3,z4,z232,z161])],[(0,[z0,z233,z1,z3,z4,z5,z6]),(0,[z234,z0,z1,z3,z4,z5,z6])],[(0,[z30,z0,z1,z235,z4,z5,z6]),(0,[z0,z1,z3,z4,z236,z5,z6]),(1,[z224,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z237,z6]),(0,[z0,z238,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z239,z6]),(0,[z0,z1,z3,z4,z5,z240,z6]),(0,[z0,z1,z3,z4,z5,z241,z6]),(0,[z0,z242,z1,z3,z4,z5,z6])],[(0,[z0,z243,z1,z3,z4,z5,z6]),(0,[z0,z244,z1,z3,z218,z5,z6]),(0,[z0,z1,z245,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z246,z6]),(0,[z0,z247,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z161]),(1,[z139,z0,z1,z56,z3,z4])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z235,z4,z5,z6]),(0,[z0,z248,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z249,z6]),(0,[z0,z250,z1,z3,z4,z5,z6]),(0,[z251,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z252,z6])]],
   [[(1,[z0,z1,z253,z3,z4,z5]),(0,[z0,z1,z254,z3,z4,z5,z6]),(0,[z157,z0,z131,z3,z4,z5,z6]),(0,[z0,z1,z255,z3,z4,z5,z6])],[(0,[z0,z86,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z256,z5,z6]),(0,[z0,z1,z3,z257,z4,z5,z6]),(0,[z25,z0,z1,z3,z4,z206,z6]),(0,[z0,z1,z258,z3,z4,z5,z6]),(0,[z108,z15,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z259]),(0,[z0,z10,z1,z3,z4,z5,z260]),(0,[z0,z261,z1,z3,z4,z5,z6])],[(0,[z0,z1,z262,z3,z4,z5,z6]),(0,[z0,z1,z263,z3,z4,z5,z6])],[(0,[z0,z1,z264,z3,z4,z5,z6])],[(0,[z0,z1,z3,z265,z4,z5,z6]),(0,[z0,z266,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z163]),(0,[z0,z1,z79,z120,z3,z4,z6]),(0,[z0,z1,z3,z4,z267,z5,z6])],[(0,[z100,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z268,z3,z4,z5,z6]),(0,[z0,z1,z269,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z270,z6]),(0,[z0,z1,z3,z4,z5,z271,z6]),(0,[z0,z1,z3,z272,z4,z5,z6]),(0,[z224,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z273,z5,z6]),(1,[z274,z1,z3,z4,z5,z6]),(1,[z0,z1,z212,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z275,z6]),(0,[z0,z1,z3,z4,z276,z5,z6]),(0,[z0,z277,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z278,z6]),(0,[z0,z1,z3,z4,z5,z279,z6]),(1,[z0,z1,z3,z4,z280,z6])]],
   [[(0,[z281,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z282,z6]),(0,[z0,z1,z283,z3,z4,z5,z6]),(0,[z0,z1,z3,z284,z4,z5,z6]),(0,[z0,z1,z164,z42,z4,z5,z6]),(0,[z0,z1,z120,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z285])],[(0,[z286,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z287,z4,z5,z6]),(0,[z0,z288,z1,z3,z4,z5,z6]),(0,[z139,z0,z1,z3,z4,z5,z161])],[(1,[z0,z289,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z290,z6]),(0,[z0,z1,z3,z4,z291,z5,z6]),(1,[z61,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z292,z4,z5,z6]),(1,[z70,z0,z1,z293,z4,z5])],[(0,[z0,z1,z3,z173,z5,z6,z183]),(0,[z0,z294,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z50,z5,z6]),(0,[z0,z1,z3,z4,z5,z295,z6]),(0,[z0,z1,z3,z4,z232,z5,z6])],[(0,[z30,z85,z1,z3,z4,z5,z6]),(0,[z296,z0,z1,z3,z4,z5,z6]),(0,[z0,z244,z1,z11,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z297,z6]),(0,[z298,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z299,z4,z5,z6]),(0,[z0,z1,z3,z300,z4,z5,z6])],[(0,[z0,z1,z184,z3,z4,z5,z6]),(0,[z0,z1,z301,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z302,z6]),(0,[z0,z1,z3,z4,z5,z6,z303])]],
   [[(0,[z304,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z305,z4,z5,z6]),(0,[z0,z306,z1,z3,z4,z5,z6])],[(0,[z30,z1,z31,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z307,z5,z6]),(0,[z0,z1,z3,z4,z39,z5,z162]),(0,[z0,z1,z3,z4,z5,z6,z219]),(0,[z0,z1,z3,z308,z4,z5,z6])],[(0,[z0,z1,z196,z3,z91,z4,z6]),(0,[z0,z10,z3,z4,z309,z5,z6]),(0,[z0,z1,z3,z4,z5,z310,z6]),(0,[z0,z1,z3,z4,z5,z311,z6]),(0,[z0,z1,z312,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z313,z6]),(0,[z314,z0,z1,z3,z4,z5,z6]),(0,[z315,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z117,z3,z4,z5,z163])],[(0,[z0,z1,z3,z4,z41,z5,z6]),(0,[z0,z131,z1,z97,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z154,z183]),(0,[z0,z1,z117,z4,z5,z43,z6]),(0,[z0,z1,z3,z4,z5,z6,z316])],[(0,[z317,z0,z1,z3,z4,z5,z6]),(0,[z157,z274,z1,z3,z4,z5,z6]),(0,[z0,z10,z1,z3,z4,z5,z6])],[(0,[z0,z1,z117,z3,z4,z43,z6]),(0,[z0,z1,z3,z4,z232,z6,z161]),(0,[z0,z1,z56,z3,z318,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z319]),(0,[z0,z320,z1,z3,z4,z5,z6]),(0,[z0,z1,z321,z3,z4,z5,z6]),(0,[z322,z0,z1,z3,z4,z5,z6]),(0,[z323,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z293,z4,z5,z6])]],
   [[(0,[z86,z1,z31,z3,z4,z5,z6])],[(0,[z0,z1,z62,z3,z4,z5,z6]),(0,[z224,z8,z1,z3,z4,z5,z6]),(0,[z0,z123,z1,z3,z4,z5,z6]),(0,[z324,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z325,z6]),(0,[z108,z0,z1,z3,z4,z5,z160]),(0,[z0,z1,z3,z326,z4,z5,z6]),(0,[z0,z1,z3,z129,z5,z6,z183])],[(0,[z30,z0,z86,z3,z4,z5,z6]),(0,[z0,z327,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z328,z4,z5,z6]),(0,[z0,z3,z4,z5,z160,z6,z154])],[(0,[z38,z25,z1,z3,z4,z5,z6]),(0,[z0,z131,z1,z3,z4,z5,z6]),(0,[z0,z1,z329,z3,z4,z5,z6]),(0,[z0,z1,z3,z330,z4,z5,z6])],[(0,[z30,z0,z1,z331,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z332,z6]),(1,[z0,z1,z3,z58,z5,z6]),(1,[z0,z1,z3,z4,z5,z333])],[(1,[z0,z47,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z73,z6]),(0,[z0,z244,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z334,z4,z5,z6]),(0,[z0,z1,z3,z4,z335,z5,z6]),(0,[z0,z147,z3,z4,z5,z6,z154]),(1,[z0,z1,z3,z336,z4,z6])],[(1,[z0,z1,z331,z4,z5,z6]),(0,[z0,z1,z3,z91,z4,z5,z6]),(0,[z0,z1,z11,z3,z4,z5,z6]),(0,[z0,z337,z1,z3,z4,z5,z6])],[(0,[z0,z189,z1,z31,z3,z4,z5]),(0,[z0,z1,z3,z9,z5,z6,z183]),(1,[z0,z244,z3,z218,z5,z6]),(1,[z0,z1,z3,z4,z338,z5])]],
   [[(1,[z0,z1,z3,z4,z5,z339]),(0,[z340,z0,z1,z3,z4,z5,z6])],[(0,[z341,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z342,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z40])],[(0,[z0,z1,z343,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z344]),(0,[z345,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z346,z3,z4,z5,z6])],[(0,[z0,z10,z1,z3,z4,z5,z344]),(0,[z0,z1,z3,z4,z347,z5,z6])],[(0,[z34,z15,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z348,z5,z6]),(0,[z0,z3,z218,z4,z309,z5,z6])],[(0,[z139,z0,z1,z3,z4,z39,z6]),(0,[z0,z1,z349,z3,z4,z5,z6]),(0,[z0,z49,z1,z3,z4,z5,z219]),(0,[z0,z1,z3,z4,z5,z160,z183])],[(0,[z34,z1,z3,z4,z5,z6,z68]),(0,[z0,z1,z3,z4,z5,z128,z6])],[(0,[z8,z0,z1,z3,z173,z5,z6]),(0,[z0,z1,z350,z3,z4,z5,z6]),(0,[z0,z1,z69,z3,z4,z5,z57]),(0,[z351,z0,z1,z3,z4,z5,z6])]],
   [[(1,[z0,z182,z1,z3,z4,z5]),(0,[z0,z1,z352,z3,z4,z5,z6]),(0,[z353,z0,z1,z3,z4,z5,z6])],[],[(1,[z157,z0,z91,z4,z5,z6]),(0,[z354,z0,z1,z3,z4,z5,z6]),(0,[z355,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z356,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z4,z5,z339])],[(0,[z0,z1,z11,z3,z5,z77,z6]),(0,[z0,z357,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z358])],[(1,[z0,z1,z67,z3,z4,z5]),(0,[z0,z359,z1,z3,z4,z5,z6]),(0,[z0,z360,z1,z3,z4,z5,z6])],[(0,[z0,z1,z361,z3,z4,z5,z6]),(0,[z0,z362,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z363,z4,z5,z6]),(0,[z0,z1,z364,z3,z4,z5,z6]),(0,[z0,z1,z3,z365,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z366,z6]),(0,[z0,z1,z3,z4,z5,z367,z6]),(0,[z0,z1,z3,z4,z5,z6,z368]),(0,[z0,z1,z3,z369,z4,z5,z6])],[(0,[z0,z1,z3,z4,z370,z5,z6]),(0,[z371,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z62,z4,z5,z6,z57]),(0,[z0,z1,z3,z4,z372,z5,z6]),(1,[z0,z49,z3,z4,z128,z6]),(0,[z0,z1,z3,z4,z5,z373,z6])],[(0,[z108,z0,z86,z3,z4,z5,z6]),(0,[z0,z1,z374,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z206,z6]),(0,[z0,z1,z375,z3,z4,z5,z6])]],
   [[(0,[z34,z0,z1,z3,z4,z59,z6]),(0,[z0,z1,z3,z4,z5,z160,z6]),(0,[z0,z1,z3,z336,z4,z5,z6])],[(0,[z376,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z377,z4,z5,z6]),(0,[z0,z1,z3,z4,z378,z5,z6]),(0,[z0,z1,z3,z4,z379,z5,z6]),(0,[z0,z1,z380,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z381,z5,z6]),(0,[z0,z382,z1,z3,z4,z5,z6]),(1,[z0,z1,z11,z5,z77,z6])],[(0,[z0,z1,z3,z383,z4,z5,z6]),(0,[z0,z1,z105,z3,z4,z5,z6]),(0,[z0,z1,z384,z3,z4,z5,z6]),(0,[z70,z0,z1,z3,z4,z5,z57]),(0,[z0,z1,z56,z3,z293,z4,z5]),(0,[z0,z1,z3,z129,z4,z5,z6]),(0,[z192,z0,z1,z153,z3,z5,z6]),(0,[z0,z1,z56,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z33,z5,z6])],[(0,[z8,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z106,z6]),(0,[z0,z1,z3,z4,z5,z385,z6]),(0,[z0,z1,z386,z3,z4,z5,z6]),(0,[z0,z387,z1,z3,z4,z5,z6]),(0,[z388,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z293,z4,z5,z6,z57])],[(0,[z389,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z390,z5,z6]),(0,[z391,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z392,z3,z4,z5,z6])],[(1,[z0,z1,z3,z129,z6,z40]),(0,[z0,z1,z393,z3,z4,z5,z6])],[(0,[z0,z394,z1,z3,z4,z5,z6]),(0,[z0,z1,z395,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z396]),(0,[z0,z1,z79,z3,z173,z5,z6]),(0,[z34,z108,z0,z1,z3,z4,z5])],[(0,[z34,z0,z147,z1,z3,z4,z5]),(0,[z0,z1,z3,z397,z4,z5,z6]),(0,[z0,z1,z3,z398,z4,z5,z6])],[(0,[z0,z86,z3,z4,z5,z6,z154]),(0,[z0,z1,z3,z4,z399,z5,z6]),(0,[z157,z0,z3,z91,z4,z5,z6]),(0,[z0,z1,z400,z3,z4,z5,z6]),(0,[z0,z1,z164,z3,z42,z4,z6]),(0,[z0,z1,z3,z4,z5,z401,z6]),(0,[z0,z402,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z318,z5,z6])],[(0,[z403,z0,z1,z3,z4,z5,z6]),(0,[z34,z0,z1,z99,z4,z5,z6]),(0,[z0,z1,z404,z3,z4,z5,z6]),(0,[z405,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z406,z3,z4,z5,z6])],[(1,[z0,z374,z3,z4,z5,z6]),(0,[z407,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z408,z3,z4,z5,z6]),(1,[z0,z1,z125,z3,z4,z6]),(0,[z0,z1,z409,z3,z4,z5,z6])],[(0,[z0,z1,z410,z3,z4,z5,z6]),(0,[z34,z0,z1,z3,z4,z5,z73]),(0,[z411,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z412,z5,z6])],[(0,[z61,z0,z1,z23,z4,z5,z6]),(0,[z0,z413,z1,z3,z4,z5,z6]),(1,[z0,z1,z117,z4,z43,z6]),(0,[z0,z1,z3,z129,z4,z6,z161]),(0,[z0,z1,z56,z3,z4,z6,z161])],[(0,[z0,z10,z244,z3,z4,z5,z6]),(0,[z0,z1,z414,z3,z4,z5,z6]),(0,[z139,z0,z1,z56,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z415,z6]),(0,[z15,z0,z147,z1,z3,z4,z5]),(0,[z0,z1,z153,z3,z4,z5,z160])],[(0,[z0,z1,z416,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z417]),(0,[z0,z418,z1,z3,z4,z5,z6]),(0,[z0,z1,z153,z3,z4,z280,z6])],[(0,[z0,z1,z3,z4,z5,z419,z6]),(0,[z0,z1,z62,z91,z4,z5,z6]),(0,[z0,z1,z420,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z57,z183])],[(0,[z0,z1,z3,z4,z5,z421,z6]),(1,[z0,z1,z3,z4,z5,z260]),(0,[z0,z1,z3,z422,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z423,z6]),(0,[z0,z1,z120,z3,z4,z206,z6]),(0,[z15,z0,z1,z3,z4,z5,z73]),(0,[z0,z131,z1,z91,z4,z5,z6]),(0,[z0,z1,z56,z3,z4,z5,z154]),(0,[z0,z1,z3,z424,z4,z5,z6])],[(0,[z0,z1,z3,z425,z4,z5,z6]),(0,[z192,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z426,z6]),(0,[z0,z95,z1,z117,z3,z4,z6]),(0,[z0,z1,z3,z427,z4,z5,z6]),(0,[z0,z1,z3,z428,z4,z5,z6]),(0,[z0,z1,z79,z3,z4,z5,z6])],[(0,[z429,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z430,z3,z4,z5,z6]),(0,[z0,z1,z3,z431,z4,z5,z6]),(0,[z432,z0,z1,z3,z4,z5,z6])],[(0,[z0,z182,z1,z3,z4,z5,z6]),(0,[z34,z0,z1,z3,z4,z5,z161]),(0,[z0,z1,z3,z4,z5,z433,z6]),(0,[z0,z1,z3,z4,z309,z5,z6]),(0,[z0,z1,z434,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z435]),(0,[z0,z1,z3,z436,z4,z5,z6])]],
   [[(0,[z0,z437,z1,z3,z4,z5,z6]),(0,[z0,z1,z438,z3,z4,z5,z6]),(1,[z192,z0,z1,z153,z3,z5])],[(0,[z0,z1,z3,z4,z439,z5,z6]),(1,[z0,z408,z3,z4,z5,z6]),(0,[z0,z1,z3,z440,z4,z5,z6]),(0,[z0,z441,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z289,z1,z3,z4,z5,z6]),(0,[z0,z1,z442,z3,z4,z5,z6]),(0,[z0,z1,z110,z3,z91,z5,z6]),(0,[z0,z1,z443,z3,z4,z5,z6]),(0,[z0,z1,z444,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z445,z6]),(0,[z0,z1,z3,z4,z446,z5,z6])],[(0,[z0,z1,z3,z4,z5,z447,z6]),(0,[z0,z1,z448,z3,z4,z5,z6]),(0,[z449,z0,z1,z3,z4,z5,z6]),(0,[z450,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z69,z3,z4,z5,z6]),(0,[z0,z1,z69,z3,z293,z4,z5])],[(0,[z22,z0,z47,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z451,z5,z6]),(0,[z0,z452,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z57]),(0,[z0,z1,z3,z318,z4,z5,z6])],[(0,[z453,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z206,z6,z161]),(0,[z15,z0,z1,z3,z4,z5,z161]),(0,[z0,z3,z4,z50,z5,z128,z6]),(0,[z70,z0,z1,z69,z4,z5,z6]),(0,[z0,z1,z3,z4,z454,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z455]),(0,[z0,z1,z456,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z457,z6]),(0,[z458,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z293,z4,z5,z183]),(0,[z0,z1,z3,z459,z4,z5,z6]),(0,[z0,z1,z3,z460,z4,z5,z6])]],
   [[(0,[z0,z461,z1,z3,z4,z5,z6]),(0,[z0,z147,z1,z3,z4,z5,z160]),(0,[z0,z1,z79,z3,z4,z6,z161])],[(0,[z0,z31,z3,z4,z5,z6,z154]),(0,[z0,z1,z462,z3,z4,z5,z6]),(0,[z192,z0,z1,z120,z3,z5,z6])],[(0,[z0,z463,z1,z3,z4,z5,z6]),(0,[z61,z0,z1,z62,z4,z5,z6])],[(0,[z0,z1,z464,z3,z4,z5,z6]),(0,[z465,z0,z1,z3,z4,z5,z6]),(0,[z34,z0,z1,z184,z4,z5,z6]),(0,[z0,z1,z125,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z466,z6]),(1,[z0,z10,z3,z309,z5,z6])],[(0,[z0,z1,z467,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z338,z5,z6]),(0,[z0,z1,z468,z3,z4,z5,z6]),(0,[z139,z0,z1,z3,z129,z4,z6])],[(0,[z30,z0,z1,z3,z4,z5,z6]),(0,[z469,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z470]),(0,[z0,z1,z3,z471,z4,z5,z6])],[(0,[z85,z0,z31,z3,z4,z5,z6]),(0,[z472,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z473,z3,z4,z5,z6]),(0,[z0,z1,z19,z424,z4,z5,z6]),(0,[z0,z1,z3,z474,z4,z5,z6]),(0,[z0,z1,z3,z165,z5,z6,z183])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z475,z0,z1,z3,z4,z5,z6]),(0,[z476,z0,z1,z3,z4,z5,z6]),(0,[z477,z0,z1,z3,z4,z5,z6]),(1,[z0,z95,z3,z4,z50,z6]),(0,[z0,z1,z478,z3,z4,z5,z6]),(0,[z0,z1,z153,z3,z336,z4,z6])]],
   [[(0,[z0,z1,z3,z479,z4,z5,z6]),(0,[z480,z0,z1,z3,z4,z5,z6]),(0,[z70,z0,z1,z3,z4,z5,z6]),(0,[z70,z0,z1,z3,z293,z4,z5])],[(0,[z481,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z218,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z482,z6]),(0,[z0,z483,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z484,z6]),(0,[z0,z1,z19,z3,z424,z5,z6]),(0,[z0,z1,z117,z3,z42,z4,z6])],[(0,[z485,z0,z1,z3,z4,z5,z6]),(0,[z486,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z212,z3,z91,z5,z6])],[(0,[z0,z1,z487,z3,z4,z5,z6]),(0,[z0,z1,z3,z488,z4,z5,z6])],[(0,[z489,z0,z1,z3,z4,z5,z6]),(1,[z8,z1,z3,z173,z5,z6]),(0,[z0,z1,z3,z4,z490,z5,z6]),(0,[z0,z1,z3,z4,z491,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z260])],[(0,[z0,z1,z3,z4,z5,z492,z6]),(0,[z0,z1,z3,z4,z5,z493,z6]),(0,[z494,z0,z1,z3,z4,z5,z6]),(0,[z157,z0,z1,z97,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z495]),(0,[z0,z1,z3,z4,z5,z496,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z497]),(0,[z38,z0,z1,z3,z4,z39,z6]),(0,[z498,z0,z1,z3,z4,z5,z6]),(0,[z0,z131,z97,z3,z4,z5,z6]),(0,[z139,z0,z1,z79,z3,z4,z6])],[(0,[z0,z1,z3,z4,z499,z5,z6]),(0,[z0,z1,z164,z3,z4,z5,z6]),(0,[z0,z1,z3,z129,z4,z6,z40])],[(0,[z0,z49,z3,z4,z5,z128,z6])],[(1,[z0,z1,z3,z35,z5,z6])],[(1,[z0,z1,z3,z41,z5,z6]),(0,[z500,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z501,z4,z5,z6]),(1,[z0,z1,z3,z165,z5,z183])],[(0,[z0,z1,z3,z4,z5,z502,z6]),(0,[z0,z1,z503,z3,z4,z5,z6]),(0,[z0,z1,z120,z3,z5,z6,z40])],[(0,[z85,z1,z3,z23,z4,z5,z6]),(0,[z0,z504,z1,z3,z4,z5,z6]),(0,[z157,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z505])],[(0,[z0,z1,z3,z4,z5,z6,z506]),(0,[z0,z1,z3,z4,z5,z507,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z508]),(0,[z0,z1,z509,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z59,z6]),(0,[z510,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z511])],[(0,[z192,z0,z1,z3,z129,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z68]),(0,[z0,z1,z3,z512,z4,z5,z6])],[(0,[z513,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z514])],[(0,[z515,z0,z1,z3,z4,z5,z6]),(0,[z22,z0,z374,z3,z4,z5,z6]),(0,[z0,z1,z3,z516,z4,z5,z6]),(0,[z0,z517,z1,z3,z4,z5,z6]),(0,[z0,z1,z518,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z519]),(0,[z0,z1,z153,z3,z4,z5,z57])],[(0,[z25,z0,z1,z3,z4,z39,z6]),(0,[z0,z1,z3,z520,z4,z5,z6]),(0,[z0,z1,z3,z521,z4,z5,z6]),(1,[z0,z1,z19,z424,z5,z6])],[(0,[z0,z522,z1,z3,z4,z5,z6])],[(0,[z523,z0,z1,z3,z4,z5,z6]),(0,[z61,z1,z31,z3,z4,z5,z6]),(0,[z0,z1,z3,z524,z4,z5,z6]),(0,[z0,z244,z3,z218,z4,z5,z6]),(0,[z0,z1,z3,z4,z525,z5,z6]),(0,[z0,z1,z3,z526,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z527,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z528]),(0,[z0,z1,z3,z165,z4,z5,z6])],[(0,[z529,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z206,z6,z40]),(0,[z0,z1,z530,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z531,z0,z1,z3,z4,z5,z6])],[(0,[z1,z3,z4,z39,z5,z206,z6]),(0,[z0,z1,z3,z532,z4,z5,z6]),(0,[z0,z1,z79,z3,z4,z6,z40]),(0,[z192,z0,z1,z153,z3,z4,z5])],[(1,[z22,z1,z23,z4,z5,z6]),(0,[z0,z1,z3,z533,z4,z5,z6]),(0,[z25,z0,z1,z3,z273,z5,z6]),(0,[z0,z1,z534,z3,z4,z5,z6]),(0,[z0,z1,z3,z535,z4,z5,z6])],[(0,[z0,z1,z536,z3,z4,z5,z6]),(0,[z0,z1,z3,z537,z4,z5,z6]),(0,[z538,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z539,z6])],[(0,[z0,z540,z1,z3,z4,z5,z6]),(0,[z34,z0,z1,z153,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z6,z541]),(0,[z0,z542,z1,z3,z4,z5,z6]),(0,[z0,z1,z153,z3,z5,z6,z183])]],
   [[(0,[z0,z1,z31,z3,z4,z5,z6]),(0,[z0,z1,z543,z3,z4,z5,z6]),(0,[z0,z544,z1,z3,z4,z5,z6]),(0,[z0,z1,z545,z3,z4,z5,z6])],[(0,[z546,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z547]),(0,[z0,z1,z3,z548,z4,z5,z6])],[(0,[z0,z1,z3,z4,z549,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z550]),(0,[z0,z1,z3,z4,z5,z551,z6]),(0,[z70,z0,z1,z293,z4,z5,z6]),(0,[z0,z1,z3,z4,z552,z5,z6])],[(0,[z0,z1,z3,z553,z4,z5,z6]),(0,[z0,z554,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z555,z5,z6]),(0,[z0,z1,z3,z4,z556,z5,z6])],[(0,[z0,z1,z3,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z557]),(0,[z0,z1,z558,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z559,z6]),(0,[z34,z0,z1,z56,z3,z4,z5]),(0,[z15,z0,z1,z153,z3,z4,z5]),(0,[z139,z0,z1,z3,z4,z5,z6])],[(0,[z560,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z561,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z339]),(0,[z0,z562,z1,z3,z4,z5,z6])],[(0,[z0,z1,z253,z3,z9,z4,z5]),(0,[z0,z1,z563,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z564]),(0,[z0,z1,z3,z4,z5,z565,z6])]],
   [[(0,[z0,z1,z3,z23,z4,z5,z6]),(0,[z0,z566,z1,z3,z4,z5,z6]),(0,[z0,z1,z567,z3,z4,z5,z6])],[(0,[z0,z568,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z569,z4,z5,z6]),(0,[z0,z570,z1,z3,z4,z5,z6]),(0,[z0,z1,z117,z3,z4,z5,z6])],[(0,[z1,z31,z3,z23,z4,z5,z6]),(0,[z0,z1,z3,z173,z5,z6,z40]),(0,[z0,z1,z3,z571,z4,z5,z6]),(0,[z0,z1,z3,z572,z4,z5,z6])],[(0,[z224,z1,z3,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z154]),(0,[z0,z1,z3,z573,z4,z5,z6])],[(0,[z0,z1,z574,z3,z4,z5,z6]),(0,[z15,z0,z1,z56,z3,z4,z5]),(0,[z575,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z576,z3,z4,z5,z6]),(1,[z15,z1,z3,z4,z5,z73])],[(0,[z577,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z143]),(0,[z0,z1,z578,z3,z4,z5,z6]),(0,[z0,z1,z196,z3,z4,z5,z6]),(0,[z579,z0,z1,z3,z4,z5,z6]),(0,[z0,z49,z1,z3,z4,z5,z6]),(0,[z0,z49,z1,z164,z3,z4,z6])],[(0,[z22,z0,z1,z3,z4,z5,z6]),(0,[z580,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z581,z5,z6]),(0,[z0,z1,z3,z4,z582,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z583,z6]),(0,[z584,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z43,z6]),(0,[z0,z1,z3,z585,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z586,z6])],[(0,[z0,z1,z587,z3,z4,z5,z6]),(0,[z25,z0,z1,z3,z58,z5,z6])],[(0,[z588,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z162]),(0,[z0,z1,z3,z4,z5,z589,z6])],[(0,[z0,z131,z31,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z4,z445,z6]),(0,[z0,z1,z3,z4,z5,z590,z6]),(0,[z0,z1,z3,z591,z4,z5,z6]),(0,[z0,z1,z117,z3,z4,z338,z5])],[(0,[z0,z1,z3,z4,z5,z6,z592]),(0,[z593,z0,z1,z3,z4,z5,z6]),(0,[z594,z0,z1,z3,z4,z5,z6]),(1,[z0,z147,z3,z4,z5,z154]),(0,[z0,z1,z595,z3,z4,z5,z6]),(0,[z192,z0,z1,z3,z165,z5,z6])],[(0,[z0,z1,z3,z596,z4,z5,z6]),(0,[z0,z49,z1,z3,z4,z5,z333])],[(0,[z0,z1,z97,z3,z4,z5,z6]),(0,[z157,z0,z1,z91,z4,z5,z6]),(0,[z108,z0,z147,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z597,z5,z6])]],
   [[(0,[z598,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z129,z5,z6,z40])],[(0,[z0,z97,z3,z91,z4,z5,z6]),(0,[z0,z1,z153,z3,z293,z4,z5]),(0,[z0,z1,z153,z3,z4,z5,z6])],[(0,[z0,z599,z1,z3,z4,z5,z6])],[(0,[z224,z0,z1,z3,z9,z5,z6]),(0,[z108,z0,z3,z4,z5,z160,z6]),(0,[z0,z1,z3,z4,z5,z600,z6])],[],[(0,[z0,z1,z3,z601,z4,z5,z6]),(0,[z139,z0,z1,z3,z4,z232,z6])],[(0,[z0,z1,z3,z9,z5,z6,z40]),(0,[z38,z1,z3,z4,z39,z5,z6]),(0,[z0,z1,z3,z602,z4,z5,z6]),(0,[z0,z1,z3,z4,z603,z5,z6]),(0,[z0,z1,z3,z4,z5,z604,z6]),(0,[z0,z1,z3,z4,z5,z57,z161]),(0,[z0,z1,z3,z605,z4,z5,z6]),(0,[z0,z606,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z607,z4,z5,z6]),(0,[z0,z1,z3,z4,z608,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z609]),(0,[z0,z1,z3,z4,z232,z5,z161])]],
   [[(0,[z610,z0,z1,z3,z4,z5,z6]),(0,[z34,z0,z1,z3,z4,z106,z6]),(0,[z0,z10,z1,z3,z309,z5,z6]),(0,[z611,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z612]),(0,[z0,z1,z3,z613,z4,z5,z6]),(0,[z614,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z615,z4,z5,z6]),(0,[z0,z1,z3,z616,z4,z5,z6]),(0,[z0,z617,z1,z3,z4,z5,z6]),(0,[z618,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z619,z6]),(0,[z0,z620,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z621]),(0,[z0,z1,z3,z622,z4,z5,z6])],[(0,[z0,z1,z623,z3,z4,z5,z6]),(0,[z0,z1,z3,z624,z4,z5,z6]),(0,[z0,z1,z3,z42,z4,z5,z6])],[(0,[z15,z1,z3,z4,z5,z73,z6])],[(0,[z0,z1,z3,z4,z5,z6,z625]),(0,[z626,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z627,z6]),(0,[z0,z1,z11,z19,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z628]),(0,[z0,z1,z3,z629,z4,z5,z6])],[(0,[z0,z1,z56,z3,z4,z5,z160]),(0,[z0,z1,z630,z3,z4,z5,z6])]],
   [[(0,[z70,z0,z1,z23,z4,z5,z6]),(0,[z631,z0,z1,z3,z4,z5,z6]),(0,[z632,z0,z1,z3,z4,z5,z6]),(0,[z0,z244,z1,z3,z309,z5,z6]),(0,[z0,z1,z633,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z634])],[(0,[z635,z0,z1,z3,z4,z5,z6]),(0,[z636,z0,z1,z3,z4,z5,z6]),(0,[z637,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z638,z6]),(0,[z639,z0,z1,z3,z4,z5,z6])],[(0,[z640,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z641,z4,z5,z6]),(0,[z0,z1,z3,z4,z87,z5,z6]),(0,[z642,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z56,z3,z33,z5,z6])],[(0,[z0,z1,z643,z3,z4,z5,z6]),(0,[z0,z644,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z293,z4,z5,z161]),(0,[z0,z1,z3,z4,z5,z280,z6])],[(0,[z0,z1,z3,z645,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z646]),(0,[z0,z647,z1,z3,z4,z5,z6]),(0,[z0,z1,z69,z4,z5,z6,z57])],[(0,[z0,z1,z3,z4,z5,z344,z6])],[(0,[z648,z0,z1,z3,z4,z5,z6]),(0,[z649,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z650,z4,z5,z6]),(0,[z0,z1,z651,z3,z4,z5,z6])],[(0,[z652,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z653,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z165,z4,z5,z183]),(0,[z0,z1,z56,z3,z4,z232,z5])],[(0,[z0,z1,z3,z4,z5,z654,z6]),(0,[z0,z1,z11,z3,z4,z5,z138]),(0,[z0,z1,z3,z4,z5,z138,z6])],[(0,[z0,z1,z655,z3,z4,z5,z6]),(0,[z85,z0,z86,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z656,z5,z6]),(0,[z0,z657,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z658,z4,z5,z6]),(0,[z0,z1,z659,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z183]),(0,[z0,z1,z3,z660,z4,z5,z6])],[(0,[z192,z0,z1,z3,z173,z5,z6]),(0,[z0,z1,z3,z9,z4,z5,z143]),(0,[z0,z1,z3,z4,z5,z661,z6]),(0,[z0,z1,z3,z4,z5,z154,z161]),(0,[z0,z1,z662,z3,z4,z5,z6])],[(0,[z0,z1,z3,z663,z4,z5,z6]),(0,[z70,z15,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z664,z6])],[(0,[z61,z85,z1,z3,z4,z5,z6]),(0,[z1,z62,z3,z23,z4,z5,z6]),(0,[z0,z1,z3,z665,z4,z5,z6]),(0,[z34,z0,z408,z3,z4,z5,z6]),(0,[z108,z0,z1,z3,z4,z5,z6])],[(0,[z0,z274,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z666,z6]),(0,[z0,z1,z667,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z668]),(1,[z0,z1,z3,z4,z445,z6]),(0,[z0,z1,z3,z669,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z670,z6])]],
   [[(0,[z0,z1,z671,z3,z4,z5,z6]),(0,[z0,z1,z672,z3,z4,z5,z6]),(0,[z0,z1,z120,z3,z4,z39,z6]),(0,[z34,z0,z1,z3,z4,z5,z183]),(0,[z0,z95,z3,z4,z50,z5,z6]),(0,[z0,z673,z1,z3,z4,z5,z6])],[(0,[z0,z1,z674,z3,z4,z5,z6]),(0,[z0,z1,z424,z4,z5,z77,z6]),(0,[z0,z675,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z676,z4,z5,z6]),(0,[z0,z1,z253,z3,z4,z5,z6])],[(0,[z0,z289,z1,z31,z3,z4,z5]),(0,[z0,z677,z1,z3,z4,z5,z6]),(0,[z34,z0,z1,z3,z4,z5,z68]),(0,[z0,z1,z678,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z679,z5,z6])],[(0,[z70,z0,z1,z62,z4,z5,z6]),(0,[z680,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z681,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z333,z6]),(0,[z0,z1,z11,z3,z424,z5,z6]),(0,[z0,z1,z682,z3,z4,z5,z6])],[(0,[z0,z683,z1,z3,z4,z5,z6])],[(0,[z0,z189,z1,z3,z4,z5,z6]),(0,[z0,z1,z684,z3,z4,z5,z6]),(0,[z0,z10,z1,z19,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z685]),(0,[z0,z1,z3,z4,z173,z5,z6]),(0,[z15,z0,z1,z3,z4,z5,z183]),(0,[z686,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z687,z4,z5,z6])]],
   [[(0,[z688,z0,z1,z3,z4,z5,z6]),(0,[z689,z0,z1,z3,z4,z5,z6]),(0,[z38,z0,z1,z3,z4,z5,z6]),(0,[z0,z690,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z99,z4,z5,z6]),(0,[z691,z0,z1,z3,z4,z5,z6]),(0,[z692,z0,z1,z3,z4,z5,z6]),(0,[z192,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z693,z4,z5,z6]),(0,[z139,z0,z1,z3,z4,z206,z6]),(0,[z0,z1,z3,z694,z4,z5,z6]),(0,[z0,z49,z1,z3,z4,z128,z6]),(0,[z0,z1,z695,z3,z4,z5,z6])],[(0,[z0,z1,z696,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z5,z68]),(0,[z0,z1,z3,z4,z5,z697,z6]),(0,[z0,z1,z3,z4,z5,z698,z6]),(0,[z0,z1,z3,z4,z699,z5,z6])],[(0,[z0,z1,z235,z3,z4,z5,z6]),(0,[z34,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z700])],[(0,[z0,z1,z3,z331,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z160,z161])],[(0,[z0,z1,z3,z701,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z702])],[(0,[z0,z1,z3,z273,z4,z5,z6]),(0,[z0,z1,z3,z4,z703,z5,z6]),(1,[z0,z123,z3,z4,z5,z6]),(0,[z0,z244,z1,z19,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z704]),(0,[z108,z0,z1,z3,z4,z5,z154]),(0,[z0,z1,z3,z4,z5,z705,z6])],[(0,[z0,z1,z3,z4,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z3,z4,z5,z707])],[(0,[z0,z1,z708,z4,z5,z6]),(0,[z0,z1,z3,z709,z5,z6]),(0,[z0,z1,z3,z710,z5,z6]),(0,[z8,z1,z3,z173,z5,z6]),(1,[z0,z3,z4,z5,z711])],[(0,[z0,z1,z712,z4,z5,z6]),(0,[z0,z1,z3,z713,z5,z6]),(0,[z0,z1,z3,z4,z714,z6]),(0,[z715,z1,z3,z4,z5,z6]),(0,[z0,z244,z55,z3,z5,z6]),(0,[z0,z1,z716,z3,z5,z183])],[(0,[z0,z1,z717,z4,z5,z6]),(0,[z0,z1,z3,z4,z718,z6]),(0,[z0,z1,z3,z4,z719,z6]),(0,[z0,z1,z3,z58,z5,z6]),(0,[z15,z119,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z333]),(0,[z0,z720,z3,z4,z5,z6])]],
   [[(0,[z0,z47,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z721]),(0,[z224,z1,z253,z3,z9,z5]),(0,[z0,z1,z722,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z723]),(0,[z0,z1,z724,z3,z4,z5])],[(0,[z25,z1,z3,z4,z725,z6]),(0,[z0,z10,z3,z309,z5,z344]),(0,[z0,z726,z3,z4,z5,z6])],[(0,[z31,z3,z331,z4,z5,z6]),(0,[z61,z1,z464,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z727]),(0,[z0,z1,z67,z3,z728,z5]),(0,[z0,z1,z3,z729,z5,z6]),(0,[z0,z1,z153,z99,z4,z5]),(0,[z0,z244,z3,z218,z5,z6]),(0,[z0,z1,z3,z4,z5,z138]),(0,[z0,z1,z3,z4,z338,z5]),(0,[z0,z730,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z280,z57]),(0,[z18,z0,z1,z3,z129,z6])],[(0,[z0,z86,z331,z4,z5,z6]),(0,[z0,z3,z4,z5,z731,z6]),(0,[z0,z1,z732,z3,z4,z6]),(0,[z0,z1,z733,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z339])]],
   [[(0,[z0,z1,z184,z4,z59,z6]),(0,[z734,z1,z3,z4,z5,z6]),(0,[z0,z1,z121,z4,z5,z57]),(0,[z0,z1,z3,z165,z5,z183])],[(0,[z30,z31,z235,z4,z5,z6]),(0,[z0,z735,z3,z4,z5,z6]),(0,[z0,z1,z3,z365,z6,z40]),(0,[z0,z1,z3,z4,z5,z344]),(0,[z0,z244,z3,z736,z5,z6]),(0,[z0,z1,z737,z5,z77,z6]),(0,[z0,z1,z69,z4,z5,z57])],[(0,[z688,z1,z23,z4,z5,z6]),(0,[z652,z31,z3,z4,z5,z6]),(0,[z157,z0,z738,z4,z5,z6]),(0,[z157,z0,z196,z91,z4,z6]),(0,[z0,z3,z4,z5,z739,z6]),(0,[z0,z1,z716,z3,z4,z5]),(0,[z139,z0,z1,z740,z3,z4])],[(0,[z0,z1,z741,z3,z5,z6]),(0,[z0,z1,z3,z742,z5,z6]),(0,[z0,z620,z97,z4,z5,z6]),(0,[z70,z0,z1,z701,z4,z5]),(0,[z743,z274,z1,z3,z4,z5]),(0,[z744,z0,z1,z3,z4,z5]),(0,[z0,z3,z738,z4,z5,z6]),(0,[z108,z0,z3,z4,z5,z160]),(0,[z0,z745,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z746,z6])]],
   [[(0,[z0,z1,z747,z4,z5,z6]),(0,[z25,z1,z3,z273,z206,z6]),(0,[z0,z1,z3,z4,z748,z6])],[(0,[z0,z1,z3,z4,z749,z6]),(0,[z0,z408,z3,z4,z106,z6]),(0,[z0,z1,z56,z99,z4,z5]),(0,[z1,z3,z4,z5,z750,z68]),(0,[z0,z1,z3,z4,z5,z163])],[(0,[z0,z1,z3,z4,z751,z6]),(0,[z0,z1,z3,z4,z752,z6]),(0,[z0,z1,z3,z4,z5,z753]),(0,[z0,z1,z3,z754,z4,z5]),(0,[z8,z1,z3,z755,z5,z6]),(0,[z0,z756,z1,z3,z4,z5]),(0,[z0,z3,z4,z5,z711,z6]),(0,[z0,z1,z3,z757,z129,z6])],[(0,[z0,z182,z1,z3,z4,z5]),(0,[z0,z3,z736,z309,z5,z6])]],
   [[(0,[z577,z31,z3,z4,z5,z6]),(0,[z0,z1,z69,z758,z4,z5]),(0,[z70,z0,z1,z758,z4,z5])],[(0,[z0,z1,z759,z4,z5,z6]),(0,[z515,z0,z91,z4,z5,z6]),(0,[z0,z1,z3,z760,z5,z6]),(0,[z15,z0,z1,z3,z4,z280]),(0,[z157,z0,z91,z4,z5,z6]),(0,[z0,z1,z761,z4,z5,z6]),(0,[z0,z1,z19,z424,z5,z6])],[(0,[z157,z0,z125,z91,z4,z6]),(0,[z0,z1,z11,z305,z5,z6]),(0,[z0,z762,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z763]),(0,[z0,z1,z3,z4,z764,z5]),(0,[z0,z1,z153,z716,z3,z5])],[(0,[z0,z1,z765,z4,z5,z6]),(0,[z0,z766,z3,z4,z5,z6]),(0,[z0,z1,z184,z4,z5,z6]),(0,[z0,z1,z3,z767,z5,z6]),(0,[z224,z1,z3,z9,z5,z143]),(0,[z0,z1,z67,z3,z4,z5]),(0,[z34,z1,z3,z4,z106,z68]),(0,[z1,z3,z4,z5,z73,z750])]],
   [[(0,[z0,z189,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z768]),(0,[z224,z1,z3,z755,z5,z6]),(0,[z298,z1,z3,z4,z206,z6]),(0,[z0,z1,z3,z4,z5,z769]),(0,[z0,z1,z3,z4,z5,z770]),(0,[z0,z1,z3,z4,z5,z771])],[(0,[z0,z1,z3,z4,z772,z6]),(0,[z0,z49,z3,z4,z128,z6])],[(1,[z1,z773,z4,z5,z6]),(1,[z274,z91,z4,z5,z6])],[(0,[z108,z0,z289,z3,z4,z5]),(0,[z0,z1,z3,z774,z5,z6]),(0,[z34,z1,z193,z3,z4,z5]),(0,[z775,z1,z3,z4,z5,z6]),(0,[z192,z0,z1,z716,z3,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z776]),(0,[z108,z0,z578,z3,z4,z5])],[(0,[z30,z189,z31,z3,z4,z5]),(0,[z0,z1,z3,z777,z5,z6]),(0,[z0,z1,z3,z4,z778,z5]),(0,[z779,z1,z3,z4,z5,z6]),(0,[z0,z1,z780,z4,z5,z6]),(0,[z0,z1,z3,z33,z5,z160])],[(0,[z0,z1,z3,z4,z87,z6]),(0,[z0,z1,z3,z4,z5,z219]),(0,[z0,z1,z3,z4,z5,z781]),(0,[z0,z1,z3,z4,z782,z6]),(0,[z0,z1,z3,z758,z4,z5]),(0,[z0,z1,z3,z757,z4,z6])],[(0,[z0,z1,z3,z783,z5,z6]),(0,[z0,z1,z3,z784,z4,z5]),(0,[z0,z1,z3,z4,z106,z6]),(0,[z0,z1,z561,z120,z3,z6]),(0,[z0,z1,z99,z4,z106,z6]),(0,[z785,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z786,z4,z5]),(1,[z0,z1,z758,z4,z5]),(0,[z0,z1,z114,z293,z4,z5])]],
   [[(0,[z0,z1,z3,z787,z4,z6]),(0,[z1,z3,z755,z4,z5,z6]),(0,[z0,z1,z253,z3,z5,z183]),(0,[z351,z1,z3,z4,z39,z6]),(0,[z0,z1,z56,z3,z4,z106])],[(0,[z34,z123,z3,z4,z5,z68])],[(0,[z0,z1,z788,z3,z4,z6]),(0,[z0,z289,z408,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z789]),(0,[z0,z790,z3,z4,z5,z6]),(0,[z0,z791,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z792,z6]),(0,[z0,z1,z793,z3,z4,z6]),(0,[z0,z1,z794,z4,z5,z6]),(0,[z0,z1,z3,z4,z795,z6])],[(1,[z374,z23,z4,z5,z6]),(0,[z0,z1,z3,z796,z4,z5]),(0,[z0,z1,z3,z663,z6,z40]),(0,[z0,z1,z797,z4,z5,z6]),(0,[z0,z3,z4,z5,z711,z154]),(0,[z798,z1,z3,z4,z5,z6]),(0,[z0,z1,z11,z5,z77,z339]),(0,[z0,z1,z164,z4,z799,z6])]],
   [[(0,[z0,z1,z800,z3,z4,z5]),(0,[z8,z1,z3,z173,z87,z6]),(0,[z38,z1,z67,z3,z4,z39]),(0,[z0,z1,z801,z4,z5,z6])],[(0,[z22,z47,z23,z4,z5,z6]),(0,[z224,z1,z3,z9,z5,z6]),(0,[z15,z1,z3,z4,z5,z750]),(0,[z0,z3,z4,z5,z160,z711]),(0,[z0,z1,z375,z4,z5,z57]),(0,[z0,z1,z3,z318,z5,z6])],[(0,[z70,z0,z1,z14,z4,z5]),(0,[z25,z1,z3,z58,z206,z6]),(0,[z0,z1,z3,z4,z725,z6]),(0,[z0,z1,z3,z757,z6,z40]),(0,[z139,z0,z1,z56,z3,z4])],[(0,[z0,z1,z235,z4,z5,z6]),(0,[z0,z802,z1,z3,z4,z5]),(0,[z0,z1,z79,z416,z3,z6]),(0,[z0,z1,z253,z3,z803,z4]),(0,[z0,z1,z117,z398,z4,z6]),(0,[z0,z1,z3,z4,z83,z161]),(0,[z0,z1,z3,z4,z799,z6])]],
   [[(0,[z652,z1,z23,z4,z5,z6]),(0,[z102,z1,z23,z4,z5,z6]),(0,[z0,z1,z253,z3,z4,z714]),(0,[z0,z1,z804,z3,z5,z6]),(1,[z0,z1,z4,z799,z6])],[(0,[z374,z3,z23,z4,z5,z6]),(0,[z0,z408,z3,z4,z5,z183]),(0,[z0,z408,z3,z4,z59,z6]),(0,[z0,z1,z3,z4,z5,z805]),(0,[z0,z97,z738,z4,z5,z6]),(0,[z0,z806,z1,z3,z4,z5]),(0,[z0,z1,z117,z4,z43,z6])],[(0,[z0,z1,z3,z4,z5,z807]),(0,[z0,z1,z808,z3,z5,z6]),(0,[z0,z10,z3,z309,z5,z260]),(0,[z0,z1,z3,z4,z5,z809])],[(0,[z0,z1,z3,z4,z810,z6]),(0,[z0,z811,z3,z4,z5,z6]),(0,[z0,z1,z3,z35,z106,z6]),(0,[z0,z1,z3,z4,z106,z161]),(0,[z0,z1,z11,z737,z5,z6])]],
   [[(0,[z30,z31,z331,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z812]),(0,[z38,z1,z3,z4,z725,z6]),(0,[z34,z408,z3,z4,z5,z68]),(0,[z0,z1,z3,z41,z106,z6]),(0,[z34,z0,z1,z3,z4,z280]),(0,[z0,z1,z813,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z814]),(0,[z0,z1,z4,z737,z5,z6]),(0,[z0,z1,z424,z737,z5,z6])],[(0,[z0,z131,z44,z4,z5,z6]),(0,[z0,z815,z3,z4,z5,z6]),(0,[z1,z3,z4,z725,z5,z6]),(0,[z15,z1,z3,z4,z5,z73]),(0,[z0,z1,z3,z4,z5,z816]),(0,[z0,z1,z3,z4,z817,z6]),(0,[z0,z3,z4,z818,z128,z6]),(0,[z0,z382,z1,z56,z3,z4])],[(0,[z0,z1,z819,z4,z5,z6]),(0,[z274,z1,z3,z4,z5,z6]),(0,[z22,z182,z1,z23,z4,z5]),(0,[z0,z820,z3,z4,z5,z6]),(0,[z0,z1,z212,z3,z5,z6]),(0,[z0,z1,z821,z4,z5,z6])],[(0,[z0,z1,z3,z58,z39,z6]),(0,[z34,z1,z3,z4,z59,z68]),(0,[z1,z3,z4,z5,z6,z750]),(0,[z0,z266,z1,z153,z3,z5]),(0,[z0,z1,z3,z822,z4,z6]),(0,[z0,z1,z3,z293,z33,z5]),(0,[z0,z1,z3,z4,z5,z823]),(0,[z0,z1,z3,z4,z280,z6])]],
   [[(0,[z0,z147,z408,z3,z4,z5]),(0,[z0,z1,z3,z824,z5,z6]),(0,[z0,z1,z56,z740,z3,z4])],[(0,[z0,z1,z3,z4,z5,z825]),(0,[z0,z1,z826,z4,z5,z6]),(0,[z0,z1,z3,z4,z827,z6]),(0,[z0,z1,z3,z4,z5,z828])],[(0,[z0,z289,z1,z3,z4,z5]),(0,[z0,z1,z829,z4,z5,z6]),(0,[z61,z1,z62,z4,z5,z6]),(0,[z190,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z830,z6]),(0,[z0,z1,z3,z831,z5,z6]),(0,[z0,z95,z3,z4,z818,z6]),(0,[z192,z0,z1,z153,z3,z280]),(0,[z192,z0,z1,z3,z336,z6])],[(0,[z0,z1,z832,z4,z5,z6]),(0,[z0,z1,z3,z4,z833,z6]),(1,[z1,z3,z755,z5,z6]),(0,[z0,z1,z3,z834,z5,z6]),(0,[z0,z1,z67,z3,z4,z106]),(0,[z0,z1,z3,z4,z5,z835]),(0,[z192,z0,z1,z153,z3,z5])]],
   [[(0,[z0,z408,z3,z4,z5,z6]),(0,[z0,z408,z99,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z836]),(0,[z0,z1,z3,z4,z837,z6])],[(0,[z0,z838,z3,z4,z5,z6]),(0,[z85,z568,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z839,z6]),(0,[z840,z1,z3,z4,z5,z6]),(0,[z0,z147,z3,z4,z5,z154]),(0,[z0,z1,z3,z4,z5,z841])],[(0,[z0,z1,z3,z4,z5,z842]),(0,[z0,z1,z843,z4,z5,z6])],[(0,[z0,z31,z331,z4,z5,z6]),(0,[z0,z1,z3,z844,z5,z6]),(0,[z0,z845,z3,z4,z5,z6]),(0,[z0,z1,z846,z4,z5,z6]),(0,[z0,z1,z99,z4,z5,z183]),(0,[z0,z1,z99,z4,z59,z6]),(0,[z0,z1,z184,z4,z106,z6]),(0,[z0,z1,z196,z212,z3,z6]),(0,[z0,z3,z4,z50,z818,z6])]],
   [[(0,[z0,z847,z3,z4,z5,z6]),(0,[z0,z49,z3,z4,z128,z219]),(0,[z0,z1,z3,z4,z848,z6])],[(0,[z0,z849,z1,z3,z4,z5]),(0,[z0,z1,z3,z850,z5,z6])],[(0,[z0,z1,z3,z4,z851,z6]),(0,[z0,z1,z3,z852,z5,z6]),(0,[z34,z1,z3,z4,z5,z68]),(0,[z34,z1,z99,z4,z5,z68]),(0,[z0,z1,z3,z853,z5,z6]),(0,[z0,z337,z3,z4,z5,z154])],[(0,[z61,z374,z3,z4,z5,z6]),(0,[z22,z1,z773,z4,z5,z6]),(0,[z854,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z855,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z856,z6]),(0,[z0,z1,z3,z4,z5,z857]),(0,[z34,z1,z3,z4,z5,z750]),(0,[z0,z1,z3,z4,z5,z750])],[(0,[z1,z838,z3,z4,z5,z6]),(0,[z1,z62,z773,z4,z5,z6]),(0,[z0,z1,z3,z4,z858,z6]),(0,[z0,z3,z4,z818,z5,z6]),(1,[z0,z1,z716,z3,z5])],[(0,[z688,z0,z91,z4,z5,z6]),(0,[z0,z859,z1,z3,z4,z5]),(0,[z0,z1,z253,z3,z35,z5]),(0,[z34,z1,z414,z3,z4,z5]),(0,[z860,z1,z3,z4,z5,z6]),(0,[z0,z10,z3,z309,z5,z6])],[(0,[z0,z1,z861,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z711])]],
   [[(0,[z0,z374,z62,z4,z5,z6]),(0,[z0,z408,z3,z4,z5,z161]),(0,[z0,z408,z3,z35,z5,z6]),(0,[z0,z1,z3,z4,z280,z154]),(0,[z0,z418,z3,z4,z5,z160]),(0,[z0,z1,z293,z758,z4,z5])],[(0,[z0,z1,z862,z3,z5,z6]),(0,[z1,z3,z4,z39,z725,z6]),(0,[z0,z408,z3,z41,z5,z6]),(0,[z157,z274,z91,z4,z5,z6]),(0,[z0,z1,z3,z4,z863,z6]),(0,[z0,z1,z3,z4,z5,z864]),(0,[z0,z1,z865,z3,z5,z6]),(0,[z1,z3,z4,z5,z6,z866]),(0,[z0,z10,z352,z3,z5,z6]),(0,[z139,z0,z1,z3,z287,z4])],[(0,[z100,z1,z3,z4,z5,z6]),(0,[z0,z1,z99,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z867]),(0,[z868,z1,z3,z4,z5,z6]),(0,[z869,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z33,z5,z154])],[(0,[z0,z870,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z871,z6]),(0,[z0,z1,z3,z58,z206,z6]),(0,[z0,z123,z3,z4,z106,z6]),(0,[z0,z1,z3,z35,z5,z183]),(0,[z0,z1,z3,z35,z59,z6])]],
   [[(0,[z0,z1,z872,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z873]),(0,[z0,z1,z3,z4,z5,z874]),(0,[z70,z0,z1,z105,z4,z5]),(0,[z0,z1,z3,z41,z59,z6]),(0,[z0,z95,z468,z3,z4,z6])],[(0,[z274,z3,z91,z4,z5,z6]),(0,[z0,z1,z3,z875,z5,z6]),(0,[z0,z1,z3,z336,z4,z6])],[(0,[z0,z1,z331,z4,z5,z6]),(0,[z0,z1,z876,z4,z5,z6]),(0,[z0,z1,z67,z3,z4,z161]),(0,[z34,z1,z3,z35,z5,z68]),(0,[z0,z1,z110,z3,z5,z6])],[(0,[z0,z1,z3,z877,z5,z6]),(0,[z34,z1,z3,z41,z5,z68]),(0,[z0,z1,z878,z4,z5,z6])]],
   [[(0,[z0,z1,z879,z4,z5,z6]),(0,[z0,z1,z3,z880,z5,z6]),(0,[z0,z1,z3,z803,z4,z6]),(0,[z274,z131,z3,z4,z5,z6]),(0,[z0,z1,z3,z881,z5,z6]),(0,[z0,z1,z3,z882,z5,z6]),(0,[z0,z1,z3,z129,z295,z6])],[(0,[z0,z883,z3,z4,z5,z6]),(0,[z0,z1,z3,z884,z5,z6]),(0,[z0,z1,z110,z3,z885,z5]),(0,[z0,z1,z758,z4,z5,z57]),(0,[z0,z1,z3,z33,z5,z57])],[(0,[z0,z1,z3,z4,z886,z6]),(0,[z0,z1,z3,z4,z5,z887]),(0,[z0,z1,z888,z3,z4,z5]),(0,[z0,z1,z3,z173,z445,z6])],[(0,[z345,z31,z3,z4,z5,z6]),(0,[z0,z1,z889,z4,z5,z6]),(0,[z0,z1,z890,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z891]),(0,[z0,z1,z3,z892,z5,z6])]],
   [[(0,[z0,z893,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z894,z6]),(0,[z0,z408,z184,z4,z5,z6]),(0,[z895,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z799,z43,z6]),(0,[z0,z1,z3,z896,z5,z6]),(0,[z0,z897,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z898]),(0,[z0,z1,z3,z4,z899,z5]),(0,[z0,z1,z3,z4,z5,z900]),(0,[z0,z901,z1,z3,z4,z5])],[(0,[z0,z1,z3,z35,z5,z6]),(0,[z0,z902,z3,z4,z5,z6]),(0,[z0,z1,z99,z4,z5,z161]),(0,[z0,z1,z99,z35,z5,z6]),(0,[z0,z1,z110,z125,z3,z6]),(0,[z0,z1,z3,z4,z903,z6]),(0,[z0,z904,z1,z3,z4,z5]),(0,[z0,z1,z42,z4,z799,z6]),(0,[z0,z1,z716,z3,z5,z6]),(0,[z139,z0,z1,z3,z318,z6])],[(0,[z298,z1,z3,z173,z5,z6]),(0,[z0,z1,z3,z41,z5,z6]),(0,[z0,z1,z99,z41,z5,z6]),(0,[z15,z452,z1,z3,z4,z5]),(0,[z0,z1,z3,z905,z5,z6]),(0,[z0,z1,z3,z4,z906,z6]),(0,[z0,z49,z630,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z907]),(0,[z0,z1,z105,z4,z5,z57]),(0,[z1,z3,z755,z173,z5,z6]),(0,[z0,z1,z153,z3,z35,z5]),(1,[z0,z1,z740,z3,z4])],[(0,[z0,z1,z67,z3,z729,z5]),(0,[z908,z1,z3,z4,z5,z6]),(0,[z0,z1,z110,z3,z5,z900]),(0,[z0,z1,z3,z4,z909,z6])],[(0,[z34,z1,z184,z4,z5,z68])],[(0,[z0,z1,z910,z4,z5,z6]),(0,[z911,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z552,z161])]],
   [[(0,[z0,z1,z3,z4,z912,z6]),(0,[z0,z1,z913,z4,z5,z6]),(0,[z0,z1,z3,z914,z5,z6]),(0,[z0,z1,z3,z4,z915,z6]),(0,[z0,z1,z164,z42,z4,z6])],[(0,[z692,z1,z3,z9,z5,z6]),(0,[z0,z131,z97,z4,z5,z6]),(0,[z0,z1,z117,z4,z338,z43])],[(0,[z0,z1,z3,z4,z5,z916]),(0,[z0,z1,z105,z3,z4,z5]),(0,[z0,z1,z3,z4,z917,z6]),(0,[z0,z1,z3,z4,z216,z161]),(0,[z0,z1,z918,z3,z4,z6]),(0,[z0,z1,z3,z336,z6,z183])],[(0,[z0,z1,z3,z4,z445,z6]),(0,[z274,z1,z91,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z919]),(0,[z0,z1,z920,z3,z5,z6]),(0,[z0,z921,z3,z4,z5,z6]),(0,[z0,z1,z3,z922,z5,z6])],[(0,[z0,z1,z923,z3,z4,z6]),(0,[z0,z1,z3,z924,z5,z6]),(0,[z0,z1,z196,z3,z4,z925])],[(0,[z0,z1,z3,z4,z5,z926]),(0,[z0,z927,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z928,z6]),(1,[z1,z3,z4,z725,z6]),(0,[z0,z929,z3,z4,z5,z6]),(0,[z0,z1,z11,z5,z77,z6]),(0,[z0,z930,z3,z4,z5,z6]),(0,[z0,z931,z3,z4,z5,z6])],[(0,[z0,z932,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z204,z161]),(0,[z0,z123,z3,z4,z59,z6]),(0,[z157,z100,z91,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z933]),(0,[z0,z1,z934,z3,z4,z5])]],
   [[(0,[z1,z3,z773,z4,z5,z6]),(0,[z0,z1,z3,z665,z5,z183]),(0,[z15,z1,z3,z4,z5,z505]),(0,[z0,z1,z196,z3,z4,z6]),(0,[z0,z10,z3,z736,z5,z6]),(0,[z0,z1,z3,z935,z5,z6]),(0,[z192,z0,z1,z3,z287,z5]),(0,[z192,z0,z1,z153,z3,z336])],[(0,[z8,z1,z3,z173,z445,z6]),(0,[z34,z0,z1,z3,z33,z5]),(0,[z0,z1,z936,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z937]),(0,[z0,z3,z4,z736,z5,z6]),(0,[z0,z1,z3,z938,z4,z6]),(0,[z0,z49,z3,z4,z818,z6]),(0,[z0,z1,z3,z737,z5,z6]),(0,[z0,z1,z19,z737,z5,z6]),(0,[z0,z1,z3,z129,z6,z634])],[(0,[z0,z1,z3,z939,z4,z5]),(0,[z577,z0,z91,z4,z5,z6]),(0,[z0,z1,z196,z3,z786,z4]),(0,[z0,z49,z3,z4,z128,z333]),(0,[z0,z1,z3,z4,z280,z160]),(1,[z0,z1,z737,z5,z6]),(0,[z0,z1,z659,z153,z3,z5]),(0,[z0,z1,z3,z129,z6,z40]),(0,[z0,z1,z740,z3,z4,z6])],[(0,[z593,z1,z23,z4,z5,z6]),(0,[z22,z1,z23,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z940,z5,z6]),(0,[z618,z1,z3,z173,z5,z6]),(0,[z0,z1,z3,z4,z941,z6]),(0,[z157,z0,z212,z91,z5,z6]),(0,[z0,z942,z3,z4,z5,z6])],[(0,[z0,z1,z3,z943,z5,z6]),(0,[z0,z1,z3,z944,z4,z5]),(0,[z0,z1,z3,z945,z4,z6]),(0,[z0,z946,z3,z4,z5,z6]),(0,[z340,z1,z3,z9,z5,z6]),(0,[z25,z1,z3,z4,z206,z6]),(0,[z15,z1,z3,z4,z5,z514]),(0,[z947,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z948]),(0,[z0,z1,z949,z4,z5,z6])],[(0,[z0,z1,z950,z3,z4,z6]),(0,[z0,z1,z3,z4,z951,z6])],[(0,[z0,z1,z952,z4,z5,z6]),(0,[z0,z1,z3,z4,z953,z6]),(0,[z0,z1,z954,z3,z4,z5]),(0,[z0,z1,z105,z99,z4,z5]),(0,[z70,z0,z1,z99,z4,z5]),(0,[z0,z1,z69,z99,z4,z5]),(0,[z0,z1,z3,z736,z5,z6]),(0,[z108,z0,z3,z4,z5,z711]),(0,[z0,z1,z955,z4,z5,z6])]],
   [[(0,[z0,z1,z956,z4,z5,z6]),(0,[z0,z374,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z957]),(0,[z0,z1,z3,z9,z445,z6]),(0,[z192,z0,z1,z253,z3,z5]),(0,[z0,z1,z958,z4,z5,z6]),(0,[z0,z738,z91,z4,z5,z6]),(0,[z0,z1,z738,z4,z5,z6]),(0,[z0,z1,z125,z3,z4,z6]),(0,[z0,z147,z3,z4,z5,z711]),(0,[z0,z959,z3,z4,z5,z6])],[(0,[z30,z31,z3,z4,z5,z6]),(0,[z485,z31,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z960]),(0,[z0,z961,z3,z4,z5,z6]),(0,[z0,z962,z3,z4,z5,z6]),(0,[z0,z1,z3,z728,z5,z6]),(0,[z0,z247,z3,z4,z5,z154])],[(0,[z0,z123,z3,z4,z5,z6]),(0,[z0,z1,z773,z4,z5,z6]),(0,[z0,z963,z1,z3,z4,z5]),(0,[z0,z123,z99,z4,z5,z6]),(0,[z0,z1,z184,z35,z5,z6]),(0,[z0,z274,z91,z4,z5,z6]),(1,[z0,z3,z736,z5,z6]),(0,[z0,z1,z3,z4,z232,z161])],[(0,[z0,z1,z3,z964,z5,z6]),(0,[z30,z838,z3,z4,z5,z6]),(0,[z0,z965,z3,z4,z5,z6]),(0,[z0,z966,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z967]),(0,[z38,z1,z3,z4,z39,z162]),(0,[z0,z1,z184,z41,z5,z6]),(1,[z0,z738,z4,z5,z6]),(0,[z0,z1,z56,z567,z3,z4]),(0,[z1,z3,z4,z5,z6,z968])]],
   [[(0,[z0,z1,z3,z4,z969,z6]),(0,[z139,z0,z1,z56,z3,z33])],[(1,[z838,z3,z4,z5,z6]),(0,[z611,z86,z3,z4,z5,z6]),(0,[z1,z3,z4,z725,z206,z6])],[(0,[z0,z289,z3,z4,z5,z154]),(0,[z0,z1,z3,z4,z5,z970]),(0,[z0,z1,z3,z4,z971,z6]),(0,[z0,z972,z3,z4,z5,z6]),(0,[z274,z1,z97,z4,z5,z6]),(0,[z0,z1,z716,z3,z165,z5]),(0,[z0,z1,z740,z3,z4,z161])],[(1,[z31,z331,z4,z5,z6]),(0,[z0,z1,z3,z973,z5,z6]),(0,[z0,z1,z253,z3,z4,z5]),(0,[z0,z1,z3,z974,z5,z6]),(0,[z0,z1,z3,z4,z5,z260]),(0,[z0,z1,z3,z265,z5,z183]),(0,[z0,z1,z3,z975,z5,z6]),(0,[z0,z1,z3,z976,z4,z5])]],
   [[(0,[z85,z838,z3,z4,z5,z6]),(0,[z0,z1,z3,z977,z5,z6]),(0,[z0,z1,z3,z4,z978,z6]),(0,[z108,z0,z408,z3,z4,z5]),(0,[z0,z1,z3,z4,z979,z6]),(0,[z0,z1,z740,z3,z4,z232])],[(0,[z0,z1,z110,z196,z3,z6]),(0,[z0,z1,z3,z318,z6,z161])],[(0,[z0,z1,z3,z980,z5,z6]),(0,[z1,z773,z23,z4,z5,z6]),(0,[z0,z1,z3,z981,z5,z6]),(0,[z0,z1,z3,z4,z5,z982]),(0,[z0,z1,z758,z4,z5,z6]),(0,[z0,z1,z3,z33,z5,z6])],[(0,[z0,z983,z1,z3,z4,z5]),(0,[z0,z374,z23,z4,z5,z6]),(0,[z0,z984,z3,z4,z5,z6]),(0,[z0,z408,z153,z3,z4,z5]),(0,[z34,z1,z89,z3,z4,z5]),(0,[z985,z1,z3,z4,z5,z6]),(0,[z0,z1,z986,z4,z5,z6]),(0,[z0,z1,z3,z129,z679,z6])]],
   [[(0,[z0,z987,z3,z4,z5,z6]),(0,[z38,z1,z3,z4,z39,z6]),(0,[z130,z1,z3,z4,z206,z6]),(1,[z1,z3,z4,z5,z750])],[(0,[z0,z1,z3,z988,z5,z6]),(0,[z0,z1,z3,z989,z5,z6]),(0,[z22,z1,z105,z23,z4,z5]),(0,[z0,z1,z3,z4,z5,z143]),(0,[z0,z1,z3,z273,z5,z6]),(0,[z0,z1,z3,z4,z5,z990])],[(0,[z0,z1,z3,z4,z5,z991]),(0,[z0,z123,z3,z35,z5,z6]),(0,[z0,z743,z1,z3,z4,z5]),(0,[z0,z3,z218,z736,z5,z6]),(0,[z0,z1,z11,z5,z138,z77])],[(0,[z0,z1,z992,z4,z5,z6]),(0,[z0,z123,z3,z41,z5,z6]),(0,[z0,z1,z3,z4,z5,z993]),(0,[z0,z994,z3,z4,z5,z6]),(0,[z0,z1,z3,z326,z6,z40])]],
   [[(0,[z30,z289,z31,z3,z4,z5]),(0,[z86,z838,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z995,z6]),(0,[z0,z1,z3,z4,z59,z6]),(0,[z0,z1,z3,z4,z5,z996]),(0,[z0,z1,z3,z585,z5,z183])],[(0,[z0,z1,z3,z4,z5,z997]),(0,[z0,z1,z998,z4,z5,z6]),(0,[z0,z1,z3,z512,z5,z183]),(0,[z0,z999,z1,z3,z4,z5]),(0,[z70,z0,z1,z293,z4,z5])],[(0,[z0,z1,z3,z4,z5,z162]),(0,[z0,z408,z56,z3,z4,z5]),(0,[z34,z1,z3,z526,z4,z5]),(0,[z0,z1,z3,z4,z818,z6]),(0,[z1000,z0,z1,z3,z4,z5]),(0,[z139,z0,z1,z56,z3,z318])],[(0,[z0,z1,z1001,z3,z5,z6]),(0,[z0,z1,z1002,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1003]),(0,[z1,z374,z23,z4,z5,z6])]],
   [[(0,[z0,z1,z1004,z4,z5,z6]),(0,[z113,z1,z3,z4,z39,z6]),(0,[z157,z0,z110,z91,z5,z6]),(0,[z1005,z1,z3,z4,z5,z6]),(0,[z0,z1,z164,z107,z4,z6]),(0,[z0,z1,z117,z4,z43,z163]),(0,[z0,z1,z3,z757,z5,z6]),(0,[z0,z1,z740,z3,z4,z5])],[(0,[z31,z23,z91,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1006]),(0,[z0,z1007,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1008,z6]),(0,[z0,z1,z3,z4,z5,z1009]),(1,[z0,z3,z4,z818,z6]),(0,[z0,z1,z117,z4,z799,z6])],[(0,[z0,z1,z3,z4,z1010,z5]),(0,[z61,z1,z773,z4,z5,z6]),(0,[z0,z1,z3,z1011,z5,z6]),(0,[z0,z1,z4,z799,z5,z6]),(0,[z0,z1,z3,z1012,z5,z6])],[(0,[z85,z86,z3,z4,z5,z6]),(0,[z126,z86,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1013]),(0,[z0,z1,z3,z4,z1014,z5]),(0,[z0,z1,z3,z459,z5,z183])]],
   [[(0,[z0,z1,z3,z1015,z5,z6]),(0,[z1,z3,z9,z755,z5,z6]),(0,[z0,z1,z1016,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z925]),(0,[z0,z1,z1017,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1018])],[(0,[z85,z1,z331,z4,z5,z6]),(0,[z0,z1,z1019,z4,z5,z6]),(0,[z838,z31,z3,z4,z5,z6]),(0,[z0,z1,z1020,z3,z4,z5]),(0,[z0,z1,z3,z4,z1021,z6])],[(0,[z108,z0,z3,z4,z5,z492]),(0,[z0,z123,z184,z4,z5,z6]),(0,[z744,z274,z1,z3,z4,z5]),(0,[z0,z131,z738,z4,z5,z6]),(0,[z0,z1,z3,z293,z4,z280])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z755,z5,z6]),(0,[z1022,z1,z3,z4,z5,z6]),(0,[z1023,z1,z3,z4,z5,z6]),(0,[z0,z1,z1024,z4,z5,z6]),(0,[z0,z95,z3,z4,z50,z6])]],
   [[(0,[z142,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1025]),(0,[z0,z1,z3,z537,z6,z40]),(0,[z0,z1,z19,z431,z5,z6]),(0,[z0,z1,z3,z1026,z5,z6]),(0,[z1027,z1,z3,z4,z5,z6])],[(0,[z22,z374,z23,z4,z5,z6])],[(0,[z1,z31,z331,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1028]),(0,[z0,z1,z3,z1029,z5,z6]),(0,[z139,z0,z1,z67,z3,z4]),(0,[z0,z1,z3,z4,z885,z5]),(0,[z0,z1,z125,z212,z3,z6]),(0,[z0,z1,z3,z4,z582,z161]),(0,[z0,z1,z149,z293,z4,z5])],[(0,[z0,z1,z3,z4,z1030,z6]),(0,[z0,z1,z3,z1031,z4,z5]),(0,[z15,z0,z1,z3,z33,z5]),(0,[z0,z84,z3,z4,z5,z160])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 559) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 559).take 466) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1025)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [559, 466] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 95).take 33).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [95, 33] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_41006

theorem PEqualNP.Outside.L_meta_41006 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4243122176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4243122176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41006.solve