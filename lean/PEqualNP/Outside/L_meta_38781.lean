import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38781

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4270377096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00012242580d6159#64 ++ 0x400012242580d615#64 ++ 0x5023e7c7d81fe3ff#64 ++ 0xa5023e7c7d81fe3f#64 : BitVec 256),
   (0x00cc891920628ea2#64 ++ 0x800cc891920628ea#64 ++ 0xf1dc993920e3ffff#64 ++ 0x7f1dc993920e3fff#64 : BitVec 256),
   (0x2617162e3b0334c3#64 ++ 0x02617162e3b0334c#64 ++ 0x6e1f1e3e3f033cce#64 ++ 0xf6e1f1e3e3f033cc#64 : BitVec 256),
   (0x1b601fc00db43b0c#64 ++ 0x01b601fc00db43b0#64 ++ 0xbfe01fc03ffc3f0d#64 ++ 0xfbfe01fc03ffc3f0#64 : BitVec 256),
   (0x8dbfe00036dbc000#64 ++ 0x08dbfe00036dbc00#64 ++ 0xbfffe0003fffc00b#64 ++ 0xebfffe0003fffc00#64 : BitVec 256),
   (0x4ffaddb580000000#64 ++ 0x04ffaddb58000000#64 ++ 0xcfffffffc0000007#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1dc993920e3ffff 0x7f1dc993920e3fff

def z1 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe01fc03ffc3f0d 0xfbfe01fc03ffc3f0

def z2 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1f1e3e3f033cce 0xf6e1f1e3e3f033cc

def z3 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0x8fdc183800000000 0x58fdc18380000000

def z4 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfffffffc0000007 0xfcfffffffc000000

def z5 : W := mkw 0x4ffbfff7d80d6159 0x44ffbfff7d80d615 0xdfffffffd81fe3ff 0xfdfffffffd81fe3f

def z6 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z7 : W := mkw 0x00012242580d6159 0x400012242580d615 0x5023e7c7d81fe3ff 0xa5023e7c7d81fe3f

def z8 : W := mkw 0x269f963f3b43b4e3 0x8269f963f3b43b4e 0x6e1f9e3f3f03fcfe 0xf6e1f9e3f3f03fcf

def z9 : W := mkw 0x59e8c9d184b40b0c 0x059e8c9d184b40b0 0x91e0e1c1c0fc0301 0x091e0e1c1c0fc030

def z10 : W := mkw 0x1bedbfdb7dffffff 0xc1bedbfdb7dfffff 0xffffffffffffffff 0xffffffffffffffff

def z11 : W := mkw 0x00c8891100000000 0x000c889110000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z12 : W := mkw 0x00cdab5b786feffb 0xc00cdab5b786feff 0xf1fffffff8ffffff 0xff1fffffff8fffff

def z13 : W := mkw 0x4f725db580000000 0x04f725db58000000 0x4e237fffc0000004 0x94e237fffc000000

def z14 : W := mkw 0x89e8e91104f8ca20 0x889e8e91104f8ca2 0x91e0e10100fcc331 0x091e0e10100fcc33

def z15 : W := mkw 0x104009c000240b0c 0x0104009c000240b0 0x000001c000000300 0x0000001c00000030

def z16 : W := mkw 0x00cc8b592866afaa 0x800cc8b592866afa 0xf1fc9ff938ffffff 0xff1fc9ff938fffff

def z17 : W := mkw 0x0920000004900000 0x0092000000490000 0xbfe000003ffc0009 0xebfe000003ffc000

def z18 : W := mkw 0x1b601d8005b01a04 0x01b601d8005b01a0 0xafc0180027e01c00 0x5afc0180027e01c0

def z19 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x7e3fffffff1fffff 0xf7e3fffffff1ffff

def z20 : W := mkw 0x3f771fee3fb73fcf 0x03f771fee3fb73fc 0xffff1ffe3fff3fcf 0xfffff1ffe3fff3fc

def z21 : W := mkw 0x0dbac00000000000 0x00dbac0000000000 0x8fdc000000000000 0x48fdc00000000000

def z22 : W := mkw 0x6fffdfbfbb0334c3 0x06fffdfbfbb0334c 0xefffffffff033ccf 0xfefffffffff033cc

def z23 : W := mkw 0x5b601ff58db43b0c 0x05b601ff58db43b0 0xffe01ffffffc3f0d 0xfffe01ffffffc3f0

def z24 : W := mkw 0x0001200250094051 0x4000120025009405 0x000000000003c0f0 0x0000000000003c0f

def z25 : W := mkw 0x1b601fc24db43b5d 0x41b601fc24db43b5 0xffe01fc7fffc3ffd 0xfffe01fc7fffc3ff

def z26 : W := mkw 0x1bec9fd92df6bfae 0x81bec9fd92df6bfa 0xfffc9ff93fffffff 0xffffc9ff93ffffff

def z27 : W := mkw 0x2417002e320304c3 0x02417002e320304c 0x401f003e000300c2 0x0401f003e000300c

def z28 : W := mkw 0x0b601d8000000000 0x00b601d800000000 0x8fe01fc000000005 0xf8fe01fc00000000

def z29 : W := mkw 0x9fffffc03ffffb0c 0x09fffffc03ffffb0 0xbfffffc03fffff0f 0xfbfffffc03fffff0

def z30 : W := mkw 0x2005020a3b0334c3 0x02005020a3b0334c 0x200000003f033cc8 0x0200000003f033cc

def z31 : W := mkw 0x0001200250094051 0x4000120025009405 0x4003e007c003c0f2 0x04003e007c003c0f

def z32 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xffffe7c7ffffc00f 0xeffffe7c7ffffc00

def z33 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfdc00003fffc008 0x4bfdc00003fffc00

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0x4023e7c7c0000007 0xa4023e7c7c000000

def z35 : W := mkw 0x5ffadff58db43b0c 0x05ffadff58db43b0 0xfffffffffffc3f0f 0xffffffffffffc3f0

def z36 : W := mkw 0x8dbfe01936dbc4a2 0x88dbfe01936dbc4a 0xffffe0393fffc0fb 0xeffffe0393fffc0f

def z37 : W := mkw 0x8088e0000048c000 0x08088e0000048c00 0x0000e0000000c000 0x00000e0000000c00

def z38 : W := mkw 0x5f3256e48d94310c 0x05f3256e48d94310 0x0e2366c6df1c0000 0x80e2366c6df1c000

def z39 : W := mkw 0x49e8c99180000000 0x049e8c9918000000 0x81e0e1c1c0000001 0x081e0e1c1c000000

def z40 : W := mkw 0x0088800000408000 0x0008880000040800 0x91c0800000e0c001 0x091c0800000e0c00

def z41 : W := mkw 0x0200160009003000 0x0020016000900300 0x2e001e003f003c0c 0xf2e001e003f003c0

def z42 : W := mkw 0xadbfe02e36dbc4c3 0x0adbfe02e36dbc4c 0xffffe03e3fffc0cb 0xeffffe03e3fffc0c

def z43 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xafff60003ffc0000 0xcafff60003ffc000

def z44 : W := mkw 0x26de9d3d23629ea2 0x826de9d3d23629ea 0xffdc993927e3ffff 0x7ffdc993927e3fff

def z45 : W := mkw 0x00012242580d6159 0x400012242580d615 0x10000000181fe3f8 0x010000000181fe3f

def z46 : W := mkw 0x4ffadff7c8042159 0x44ffadff7c804215 0xcfffffffc00023f7 0xfcfffffffc00023f

def z47 : W := mkw 0x8920600004984000 0x0892060000498400 0x00206000001c0000 0x000206000001c000

def z48 : W := mkw 0x00c8891100608a20 0x800c8891100608a2 0x91c0810100e0c331 0x091c0810100e0c33

def z49 : W := mkw 0x261316261b013041 0x0261316261b01304 0x0e0306061f000000 0x80e0306061f00000

def z50 : W := mkw 0x0000000000000000 0x0000000000000000 0x500081010003e3ff 0x2500081010003e3f

def z51 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x00001fc000003f04 0x100001fc000003f0

def z52 : W := mkw 0x0000024008042108 0x0000002400804210 0x102007c0181c230d 0xa102007c0181c230

def z53 : W := mkw 0x0612142400000000 0x0061214240000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z54 : W := mkw 0x1b601f800db03a04 0x01b601f800db03a0 0xafc01e003fe03c0c 0xfafc01e003fe03c0

def z55 : W := mkw 0x00012242580d6159 0x400012242580d615 0x4023e6c7d81fc0f2 0x84023e6c7d81fc0f

def z56 : W := mkw 0x196009c004b40b0c 0x0196009c004b40b0 0x91e001c000fc0301 0x091e001c000fc030

def z57 : W := mkw 0xaf37762e3f9b74c3 0x0af37762e3f9b74c 0x6e3f7e3e3f1f3cce 0xf6e3f7e3e3f1f3cc

def z58 : W := mkw 0x26dfbf7f7b6ffffb 0xc26dfbf7f7b6ffff 0xffffffffffffffff 0xffffffffffffffff

def z59 : W := mkw 0x8005200036dbc000 0x08005200036dbc00 0x300000003fffc008 0x0300000003fffc00

def z60 : W := mkw 0x8dbec00026d28000 0x08dbec00026d2800 0xafdc000027e00000 0x4afdc000027e0000

def z61 : W := mkw 0x0040090000200a00 0x00040090000200a0 0xb1c0190020e03f0d 0x7b1c0190020e03f0

def z62 : W := mkw 0x1b2016c00d94310c 0x01b2016c00d94310 0x0e2006c01f1c0000 0x80e2006c01f1c000

def z63 : W := mkw 0x008c800020428000 0x0008c80002042800 0x001c80000003c002 0x0001c80000003c00

def z64 : W := mkw 0x4ffaddb584900000 0x04ffaddb58490000 0xfffffffffffc000f 0xffffffffffffc000

def z65 : W := mkw 0x0001200250094051 0x4000120025009405 0x00036006c0000000 0x000036006c000000

def z66 : W := mkw 0x6ffffffffb0f75db 0x46ffffffffb0f75d 0xffffffffff1fffff 0xfffffffffff1ffff

def z67 : W := mkw 0x8d33600016994000 0x08d3360001699400 0x0e2360001f1c0000 0x80e2360001f1c000

def z68 : W := mkw 0x8dbfe2427edfe159 0x48dbfe2427edfe15 0xffffe7c7ffffe3ff 0xeffffe7c7ffffe3f

def z69 : W := mkw 0x4ffaddb580200a00 0x04ffaddb580200a0 0xffffffffe0e03f0f 0xfffffffffe0e03f0

def z70 : W := mkw 0x26de9d3d23629ea2 0x826de9d3d23629ea 0xafdc183827e01c00 0x5afdc183827e01c0

def z71 : W := mkw 0x4ffeddbda0628ea2 0x84ffeddbda0628ea 0xafdc183820e01c00 0x5afdc183820e01c0

def z72 : W := mkw 0x00012242580d6159 0x400012242580d615 0x102007c0181fe3fd 0xa102007c0181fe3f

def z73 : W := mkw 0x0920000004900000 0x0092000000490000 0xafc0000027e00000 0x4afc0000027e0000

def z74 : W := mkw 0x49e8c99180000000 0x049e8c9918000000 0xc1e3e7c7c0000007 0xac1e3e7c7c000000

def z75 : W := mkw 0x0000024248042159 0x4000002424804215 0x400007c7c00023f4 0x0400007c7c00023f

def z76 : W := mkw 0x1b601d8005b01a04 0x01b601d8005b01a0 0xbfe018003ffc1c09 0xfbfe018003ffc1c0

def z77 : W := mkw 0x2617142c33031482 0x02617142c3303148 0x2e1f18383f031c0a 0xf2e1f18383f031c0

def z78 : W := mkw 0x5ffaddb585b01a04 0x05ffaddb585b01a0 0xafdc183827e01c00 0x5afdc183827e01c0

def z79 : W := mkw 0x0dbac00004900000 0x00dbac0000490000 0xbfffe0003ffc000b 0xebfffe0003ffc000

def z80 : W := mkw 0x5ffaddb585b01a04 0x05ffaddb585b01a0 0xefffffffe7e01c07 0xfefffffffe7e01c0

def z81 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xffe3ffc7fffc3f0f 0xfffe3ffc7fffc3f0

def z82 : W := mkw 0x8d3362425e9d6159 0x48d3362425e9d615 0x0e2366c6df1c0000 0x80e2366c6df1c000

def z83 : W := mkw 0x0004000820020482 0x0000400082002048 0x2000000020033cc8 0x02000000020033cc

def z84 : W := mkw 0x00012242580d6159 0x400012242580d615 0x002366c6d81c0000 0x8002366c6d81c000

def z85 : W := mkw 0x4f3254a480000000 0x04f3254a48000000 0x4e23e7c7c0000007 0xa4e23e7c7c000000

def z86 : W := mkw 0x0dbac00000000000 0x00dbac0000000000 0x8fffe00000000003 0xe8fffe0000000000

def z87 : W := mkw 0x0612142400000000 0x0061214240000000 0x0e1c183800000000 0x50e1c18380000000

def z88 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x2e1c183827001c00 0x52e1c183827001c0

def z89 : W := mkw 0x0000024248042159 0x4000002424804215 0x00000000000023f0 0x000000000000023f

def z90 : W := mkw 0x008c8019204284a2 0x8008c8019204284a 0x401c80390003c0f2 0x0401c80390003c0f

def z91 : W := mkw 0x1b641fc82df6bfae 0x81b641fc82df6bfa 0xbfe01fc03ffffffd 0xfbfe01fc03ffffff

def z92 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0x0e201fc01f1c3f04 0x90e201fc01f1c3f0

def z93 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xdfffffffc003e3ff 0xfdfffffffc003e3f

def z94 : W := mkw 0x8dbfe00836dbc482 0x08dbfe00836dbc48 0xfffff8383ffffccf 0xffffff8383ffffcc

def z95 : W := mkw 0x9dbfe2403ffffb0c 0x09dbfe2403ffffb0 0xbfffe0003fffff0b 0xebfffe0003fffff0

def z96 : W := mkw 0x0612142400000000 0x0061214240000000 0x4e1f1e3e00000006 0xf4e1f1e3e0000000

def z97 : W := mkw 0x4f3254a480000000 0x04f3254a48000000 0x0e2366c6c0000000 0x80e2366c6c000000

def z98 : W := mkw 0x00c8891100608a20 0x800c8891100608a2 0xd1c0810100e3e3ff 0x2d1c0810100e3e3f

def z99 : W := mkw 0x2200142c01001482 0x02200142c0100148 0x0000183800001c00 0x10000183800001c0

def z100 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x7e1f1e3e3f1ffffe 0xf7e1f1e3e3f1ffff

def z101 : W := mkw 0x00012242580d6159 0x400012242580d615 0x102367c6d81c230d 0xa102367c6d81c230

def z102 : W := mkw 0x4ffaddb580608a20 0x84ffaddb580608a2 0xdfffffffc0e0c337 0xfdfffffffc0e0c33

def z103 : W := mkw 0x00012242580d6159 0x400012242580d615 0x50008101181fe3ff 0x250008101181fe3f

def z104 : W := mkw 0x0920000004900000 0x0092000000490000 0x91e0000000fc0001 0x091e0000000fc000

def z105 : W := mkw 0x192002400db43b0c 0x0192002400db43b0 0xbfe000003ffc3f09 0xebfe000003ffc3f0

def z106 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1ffffffe0e3ffff 0xff1ffffffe0e3fff

def z107 : W := mkw 0xcdffe991b6dbc000 0x0cdffe991b6dbc00 0xbfffe1c1ffffc00b 0xebfffe1c1ffffc00

def z108 : W := mkw 0x1b613fc25dbd7b5d 0x41b613fc25dbd7b5 0xbfe37fc6fffc3f0d 0xfbfe37fc6fffc3f0

def z109 : W := mkw 0x19600bc00cb42b0c 0x019600bc00cb42b0 0x91e007c018fc230d 0xa91e007c018fc230

def z110 : W := mkw 0x80052000324bc000 0x080052000324bc00 0x000000000003c000 0x0000000000003c00

def z111 : W := mkw 0x649fc03fb20304c3 0x0649fc03fb20304c 0x401fe03fc00300c2 0x0401fe03fc00300c

def z112 : W := mkw 0x3b651fca3fb73fcf 0x03b651fca3fb73fc 0xbfe01fc03fff3fcd 0xfbfe01fc03fff3fc

def z113 : W := mkw 0x2612142403001000 0x0261214240300100 0x0e00000007000000 0x00e0000000700000

def z114 : W := mkw 0x0040091900200ea2 0x80040091900200ea 0x500099390003ffff 0x3500099390003fff

def z115 : W := mkw 0x8d33600016994000 0x08d3360001699400 0xbfe360003ffc0009 0xebfe360003ffc000

def z116 : W := mkw 0x849fe019324bc4a2 0x8849fe019324bc4a 0x401fe0390003c0f2 0x0401fe0390003c0f

def z117 : W := mkw 0x4f3254a480000000 0x04f3254a48000000 0x4e3f7efec0000006 0xf4e3f7efec000000

def z118 : W := mkw 0x0dfac91100000000 0x00dfac9110000000 0xcffff93900000007 0xfcffff9390000000

def z119 : W := mkw 0x2617142e330314c3 0x02617142e330314c 0x6e1f183e27031cc2 0x56e1f183e27031cc

def z120 : W := mkw 0x1b601dc005b41b0c 0x01b601dc005b41b0 0xbfe019c027fc1f01 0x5bfe019c027fc1f0

def z121 : W := mkw 0x1960098004b00a04 0x01960098004b00a0 0x81c0000000e00000 0x081c0000000e0000

def z122 : W := mkw 0x0417000032030000 0x0041700003203000 0x001f000000030002 0x0001f00000003000

def z123 : W := mkw 0xa49fe02e324bc4c3 0x0a49fe02e324bc4c 0x401fe03e0003c0c2 0x0401fe03e0003c0c

def z124 : W := mkw 0xcffeddb5a6d28000 0x0cffeddb5a6d2800 0xafdc183827e00000 0x5afdc183827e0000

def z125 : W := mkw 0x800522427edfe159 0x4800522427edfe15 0x7023e7c7ffffe3ff 0xa7023e7c7ffffe3f

def z126 : W := mkw 0x0004000820628ea2 0x80004000820628ea 0x3000000020e3fff8 0x03000000020e3fff

def z127 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xa1dc183820e01c00 0x5a1dc183820e01c0

def z128 : W := mkw 0x00012242580d6159 0x400012242580d615 0x402366c6d81f20ce 0xa402366c6d81f20c

def z129 : W := mkw 0x9dffe9c036ffcb0c 0x09dffe9c036ffcb0 0xbfffe1c03fffc30b 0xebfffe1c03fffc30

def z130 : W := mkw 0x1000024009243b0c 0x01000024009243b0 0x0000000000003f00 0x00000000000003f0

def z131 : W := mkw 0x02401d8000000000 0x002401d800000000 0x00001fc000000004 0x100001fc00000000

def z132 : W := mkw 0x1b613fc25dbd7b5d 0x41b613fc25dbd7b5 0xffe3ffc7ffffffff 0xfffe3ffc7fffffff

def z133 : W := mkw 0xafbff42c37dbd482 0x0afbff42c37dbd48 0xbffff8383fffdc0b 0xfbffff8383fffdc0

def z134 : W := mkw 0x0040091900200ea2 0x80040091900200ea 0x4000193900003ff4 0x14000193900003ff

def z135 : W := mkw 0x3f731fe61fb53b4d 0x03f731fe61fb53b4 0xbfe31fc63ffc3f0d 0xfbfe31fc63ffc3f0

def z136 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000101000023f4 0x040000101000023f

def z137 : W := mkw 0x0001020218012041 0x0000102021801204 0x40030606180320ce 0xa40030606180320c

def z138 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xb1dc183820e3fff8 0x5b1dc183820e3fff

def z139 : W := mkw 0x049ac00000000000 0x0049ac0000000000 0x001fe00000000002 0x0001fe0000000000

def z140 : W := mkw 0xcffafdb584d8c000 0x0cffafdb584d8c00 0xdfffffffc0fcc007 0xfdfffffffc0fcc00

def z141 : W := mkw 0x8dbee00026dac000 0x08dbee00026dac00 0xbffce00027fcc001 0x4bffce00027fcc00

def z142 : W := mkw 0x22401f3f09203ee3 0x822401f3f09203ee 0x40001f3f00003ff4 0x140001f3f00003ff

def z143 : W := mkw 0xadbfe20a3fdbf4c3 0x0adbfe20a3fdbf4c 0xbfffe0003ffffccb 0xebfffe0003ffffcc

def z144 : W := mkw 0x0001220218096041 0x0000122021809604 0x5023e606181fe0cf 0xa5023e606181fe0c

def z145 : W := mkw 0x1b2016c00d94310c 0x01b2016c00d94310 0x2e201ec03f1c3c0c 0xf2e201ec03f1c3c0

def z146 : W := mkw 0x49e9ebd3d80d6159 0x449e9ebd3d80d615 0xd1e3e7c7d81fe3ff 0xad1e3e7c7d81fe3f

def z147 : W := mkw 0x26df9f3f3b63bee3 0x826df9f3f3b63bee 0xffdf9f3f3fe3ffff 0xfffdf9f3f3fe3fff

def z148 : W := mkw 0x8dffe91936fbcea2 0x88dffe91936fbcea 0xfffff9393fffffff 0xffffff9393ffffff

def z149 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xb1dc993920e0df31 0x5b1dc993920e0df3

def z150 : W := mkw 0x2005020a3b0334c3 0x02005020a3b0334c 0x601c18383f033cce 0x7601c18383f033cc

def z151 : W := mkw 0x0417000032030000 0x0041700003203000 0x2e1f00003f03000a 0xe2e1f00003f03000

def z152 : W := mkw 0x3f761fec2fb63f8e 0x03f761fec2fb63f8 0xbffc1ff83ffc3f0d 0xfbffc1ff83ffc3f0

def z153 : W := mkw 0x0960090004b00a00 0x00960090004b00a0 0xbfe019003ffc3f0d 0xfbfe019003ffc3f0

def z154 : W := mkw 0x09ec891924f28ea2 0x809ec891924f28ea 0xfffc99393fffffff 0xffffc99393ffffff

def z155 : W := mkw 0x00cc891120628a20 0x800cc891120628a2 0xb1dc810120e3c33b 0x6b1dc810120e3c33

def z156 : W := mkw 0x100122425dbd7b5d 0x4100122425dbd7b5 0x300000003ffffff8 0x0300000003ffffff

def z157 : W := mkw 0x4ffbfdb7d0094051 0x44ffbfdb7d009405 0xcfffffffc003c0f7 0xfcfffffffc003c0f

def z158 : W := mkw 0x19e889d104f48b2c 0x819e889d104f48b2 0x91e081c100fcc331 0x091e081c100fcc33

def z159 : W := mkw 0x89ace00024dac000 0x089ace00024dac00 0xb1fce00020ffc00b 0x6b1fce00020ffc00

def z160 : W := mkw 0x00c8891100000000 0x000c889110000000 0xc1dc993900000007 0x7c1dc99390000000

def z161 : W := mkw 0x00412b5b582d6ffb 0xc00412b5b582d6ff 0x5023ffffd81fffff 0xb5023ffffd81ffff

def z162 : W := mkw 0x36571fee3b273fcf 0x036571fee3b273fc 0x6e1f1ffe3f033fce 0xf6e1f1ffe3f033fc

def z163 : W := mkw 0x0000024008042108 0x0000002400804210 0x002006c0181c0000 0x8002006c0181c000

def z164 : W := mkw 0x2617362e7b0b74d3 0x42617362e7b0b74d 0x6e1ffe3fff03fcfe 0xf6e1ffe3fff03fcf

def z165 : W := mkw 0x2005224a7b0f75db 0x42005224a7b0f75d 0x300000003f1ffff8 0x0300000003f1ffff

def z166 : W := mkw 0x2416002c22020482 0x02416002c2202048 0x001c003800000000 0x0001c00380000000

def z167 : W := mkw 0x4f3376e6d80d6159 0x44f3376e6d80d615 0x0e2366c6d81c0000 0x80e2366c6d81c000

def z168 : W := mkw 0x100002400db43b0c 0x0100002400db43b0 0x300000003ffc3f08 0x0300000003ffc3f0

def z169 : W := mkw 0x00c8891100608a20 0x800c8891100608a2 0x81c0000000e00000 0x081c0000000e0000

def z170 : W := mkw 0x008c800820428482 0x0008c80082042848 0xf1dc983820e3fccf 0x7f1dc983820e3fcc

def z171 : W := mkw 0x42401db580000000 0x042401db58000000 0x40001fffc0000004 0x140001fffc000000

def z172 : W := mkw 0x849fe000324bc000 0x0849fe000324bc00 0x001fe0000003c002 0x0001fe0000003c00

def z173 : W := mkw 0x0044091920220ea2 0x80044091920220ea 0x601c193920033ffe 0x7601c193920033ff

def z174 : W := mkw 0x0617142432030000 0x0061714243203000 0x6e1f1e3e3f03000e 0xf6e1f1e3e3f03000

def z175 : W := mkw 0x0204160829023482 0x0020416082902348 0x6e1c1e383f033cce 0xf6e1c1e383f033cc

def z176 : W := mkw 0x200102021b013041 0x0200102021b01304 0x000000001f000000 0x0000000001f00000

def z177 : W := mkw 0x4fbad4b580000000 0x04fbad4b58000000 0x4e3fe6ffc0000002 0x84e3fe6ffc000000

def z178 : W := mkw 0x0b601f8009003000 0x00b601f800900300 0xafe01fc03f003c0d 0xfafe01fc03f003c0

def z179 : W := mkw 0x0b2016000d903000 0x00b2016000d90300 0xbfe01e003ffc3c0d 0xfbfe01e003ffc3c0

def z180 : W := mkw 0xcffffdbdb6fbcea2 0x8cffffdbdb6fbcea 0xffffffffffffffff 0xffffffffffffffff

def z181 : W := mkw 0x449ac03580000000 0x0449ac0358000000 0x401fe03fc0000002 0x0401fe03fc000000

def z182 : W := mkw 0xcffffdb5b6dbc000 0x0cffffdb5b6dbc00 0xffffffffffffc00f 0xfffffffffffffc00

def z183 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000180020003c0c 0x72000180020003c0

def z184 : W := mkw 0x6fffdfbfbb63bee3 0x86fffdfbfbb63bee 0xffffffffffe3ffff 0xfffffffffffe3fff

def z185 : W := mkw 0x2f37162e3f9334c3 0x02f37162e3f9334c 0xffff1e3e3fff3ccf 0xfffff1e3e3fff3cc

def z186 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xffe09fc13fffffff 0xfffe09fc13ffffff

def z187 : W := mkw 0x0001200010094000 0x0000120001009400 0x1023e000181fc00b 0xa1023e000181fc00

def z188 : W := mkw 0x0004000820020482 0x0000400082002048 0x601c183820033cce 0x7601c183820033cc

def z189 : W := mkw 0x8dbbe00016d9c000 0x08dbbe00016d9c00 0x9fe3e0001ffcc001 0x89fe3e0001ffcc00

def z190 : W := mkw 0x0d32400000000000 0x00d3240000000000 0x0e23600000000000 0x80e2360000000000

def z191 : W := mkw 0x00c8891100200a00 0x000c8891100200a0 0xf1dc993920e03f0f 0x7f1dc993920e03f0

def z192 : W := mkw 0x0200140001001000 0x0020014000100100 0x2e00180027001c00 0x52e00180027001c0

def z193 : W := mkw 0x3fff9fff3ff7bfef 0x83fff9fff3ff7bfe 0xffff9fff3fffffff 0xfffff9fff3ffffff

def z194 : W := mkw 0x4ffeddbda0628ea2 0x84ffeddbda0628ea 0xffffffffe0e3ffff 0xfffffffffe0e3fff

def z195 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xafe01ec03ffc1c00 0xdafe01ec03ffc1c0

def z196 : W := mkw 0x008c800020428000 0x0008c80002042800 0xb1dc800020e3c00b 0x6b1dc800020e3c00

def z197 : W := mkw 0x04172000320b4000 0x004172000320b400 0x3e3fe0003f1fc00b 0xe3e3fe0003f1fc00

def z198 : W := mkw 0x6ffadfbf890034c3 0x06ffadfbf890034c 0xcfffffffc0003cc7 0xfcfffffffc0003cc

def z199 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x4e1f063e1f0300c2 0x84e1f063e1f0300c

def z200 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x2e0306063f033cc8 0x82e0306063f033cc

def z201 : W := mkw 0x0200160009003000 0x0020016000900300 0x00001e0000003c04 0x100001e0000003c0

def z202 : W := mkw 0x0005000032030000 0x0000500003203000 0x200000003f030008 0x0200000003f03000

def z203 : W := mkw 0x5be8dfd18db43b0c 0x05be8dfd18db43b0 0xbfe0ffc1fffc3f0d 0xfbfe0ffc1fffc3f0

def z204 : W := mkw 0x8004000026d28000 0x08004000026d2800 0x2000000027e00000 0x02000000027e0000

def z205 : W := mkw 0x2616162e2b0234c3 0x02616162e2b0234c 0x6e1c1e3e27003cc4 0x56e1c1e3e27003cc

def z206 : W := mkw 0x8005200836fbcea2 0x88005200836fbcea 0x300000003ffffff8 0x0300000003ffffff

def z207 : W := mkw 0x00012242580d6159 0x400012242580d615 0x5003e007d81fe3fa 0x05003e007d81fe3f

def z208 : W := mkw 0x261316261b013041 0x0261316261b01304 0x4e0306061f0320ce 0xa4e0306061f0320c

def z209 : W := mkw 0x2417022e3a0324c3 0x02417022e3a0324c 0x401f063e180320ce 0xa401f063e180320c

def z210 : W := mkw 0x0000000000200a00 0x00000000000200a0 0x3000000020e03f08 0x03000000020e03f0

def z211 : W := mkw 0x0612162409003000 0x0061216240900300 0x6e1f1e3e3f003c0e 0xf6e1f1e3e3f003c0

def z212 : W := mkw 0x4dbac03580000000 0x04dbac0358000000 0xcfffe03fc0000003 0xecfffe03fc000000

def z213 : W := mkw 0x8dbfe00276dbc051 0x48dbfe00276dbc05 0xffffe007ffffc0fb 0xeffffe007ffffc0f

def z214 : W := mkw 0x2200162e090034c3 0x02200162e090034c 0x40001e3e00003cc4 0x140001e3e00003cc

def z215 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e3fffffff033ccf 0xf6e3fffffff033cc

def z216 : W := mkw 0x42401ff7c8042159 0x442401ff7c804215 0x40001fffc00023f4 0x140001fffc00023f

def z217 : W := mkw 0x12401fc249243b5d 0x412401fc249243b5 0x40001fc7c0003ff4 0x140001fc7c0003ff

def z218 : W := mkw 0x26df9f3f3b0334c3 0x026df9f3f3b0334c 0xefdf9f3f3f033ccf 0xfefdf9f3f3f033cc

def z219 : W := mkw 0x89a8e00004d8c000 0x089a8e00004d8c00 0x91e0e00000fcc001 0x091e0e00000fcc00

def z220 : W := mkw 0x092122425c9d6159 0x4092122425c9d615 0xffe3e7c7ffffe3ff 0xeffe3e7c7ffffe3f

def z221 : W := mkw 0x00002040400c4118 0x400002040400c411 0x1020e1c1c01cc331 0x01020e1c1c01cc33

def z222 : W := mkw 0x3617166e3fb73fcf 0x03617166e3fb73fc 0x7e1f1e3e3fff3fce 0xf7e1f1e3e3fff3fc

def z223 : W := mkw 0xafbff62e3fdbf4c3 0x0afbff62e3fdbf4c 0xfffffe3e3ffffccf 0xffffffe3e3ffffcc

def z224 : W := mkw 0x1b2136c25d9d715d 0x41b2136c25d9d715 0x0e2366c6df1c0000 0x80e2366c6df1c000

def z225 : W := mkw 0x0201160219013041 0x0020116021901304 0x6e031e063f033cce 0xf6e031e063f033cc

def z226 : W := mkw 0x0000020208002041 0x0000002020800204 0x40000606000020c4 0x040000606000020c

def z227 : W := mkw 0x261336665b0d7159 0x4261336665b0d715 0x0e2366c6df1c0000 0x80e2366c6df1c000

def z228 : W := mkw 0x2200166e490435db 0x42200166e490435d 0x40001fffc0003ff4 0x140001fffc0003ff

def z229 : W := mkw 0x4088c01180000000 0x04088c0118000000 0x0000e001c0000000 0x00000e001c000000

def z230 : W := mkw 0x849fe2427a4fe159 0x4849fe2427a4fe15 0x503fe7c7d81fe3ff 0xa503fe7c7d81fe3f

def z231 : W := mkw 0x849fe00036dbc000 0x0849fe00036dbc00 0x301fe0003fffc00a 0x0301fe0003fffc00

def z232 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfdff83fc0000002 0x5cfdff83fc000000

def z233 : W := mkw 0x42c89db580000000 0x042c89db58000000 0xc1dc9fffc0000007 0x7c1dc9fffc000000

def z234 : W := mkw 0x4000003580000000 0x0400000358000000 0x4000003fc0000000 0x04000003fc000000

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000000003e3f8 0x0100000000003e3f

def z236 : W := mkw 0x0921200014994000 0x0092120001499400 0xbfe3e0003fffc00b 0xebfe3e0003fffc00

def z237 : W := mkw 0x89a8c00004d08000 0x089a8c00004d0800 0x81c0000000e00000 0x081c0000000e0000

def z238 : W := mkw 0x8dffe90036fbca00 0x08dffe90036fbca0 0xbffff9003fffff0f 0xfbffff9003fffff0

def z239 : W := mkw 0x6ffeddbda3021482 0x06ffeddbda302148 0xefffffffe7001c07 0xfefffffffe7001c0

def z240 : W := mkw 0x249f803f324384e3 0x8249f803f324384e 0x401f803f0003c0f2 0x0401f803f0003c0f

def z241 : W := mkw 0x49e8c99180000000 0x049e8c9918000000 0xc1fcf9f9c0000007 0x7c1fcf9f9c000000

def z242 : W := mkw 0x00400b5b48242ffb 0xc00400b5b48242ff 0x40001fffc0003ff4 0x140001fffc0003ff

def z243 : W := mkw 0x0040090000200a00 0x00040090000200a0 0xa1c0180020e01c00 0x5a1c0180020e01c0

def z244 : W := mkw 0x26df9f3f3b63bee3 0x826df9f3f3b63bee 0xefdf1e3e3fe33cce 0xfefdf1e3e3fe33cc

def z245 : W := mkw 0x0000020008002000 0x0000002000800200 0x000006001800200c 0xa000006001800200

def z246 : W := mkw 0x0200164009043108 0x0020016400904310 0x3e201fc03f1c3f0d 0xf3e201fc03f1c3f0

def z247 : W := mkw 0x0001200010094000 0x0000120001009400 0x10000000181fc008 0x010000000181fc00

def z248 : W := mkw 0x12401fd909243fae 0x812401fd909243fa 0x40001ff900003ff4 0x140001ff900003ff

def z249 : W := mkw 0x00002040400c4118 0x400002040400c411 0x5020e1c1c01fe3ff 0x25020e1c1c01fe3f

def z250 : W := mkw 0x669fd63fbb0334c3 0x0669fd63fbb0334c 0x6e1ffe3fff033cce 0xf6e1ffe3fff033cc

def z251 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0x8ffc1ff800000005 0xf8ffc1ff80000000

def z252 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x6e1f1e3e27001c06 0xf6e1f1e3e27001c0

def z253 : W := mkw 0x1b20148005901004 0x01b2014800590100 0x0e00000007000000 0x00e0000000700000

def z254 : W := mkw 0x00002040400c4118 0x400002040400c411 0x002060c0c01c0000 0x0002060c0c01c000

def z255 : W := mkw 0x8d3362425e9d6159 0x48d3362425e9d615 0x5e23e7c7df1fe3ff 0xa5e23e7c7df1fe3f

def z256 : W := mkw 0x3f3316e61f95314d 0x03f3316e61f95314 0x0e2306c61f1c0000 0x80e2306c61f1c000

def z257 : W := mkw 0x0001200010094000 0x0000120001009400 0x00236000181c0000 0x800236000181c000

def z258 : W := mkw 0x8dbfe2403edfe108 0x08dbfe2403edfe10 0xbfffe7c03fffe30f 0xebfffe7c03fffe30

def z259 : W := mkw 0x449be037d0094051 0x4449be037d009405 0x401fe03fc003c0f2 0x0401fe03fc003c0f

def z260 : W := mkw 0x2617166e7b0735db 0x42617166e7b0735d 0x6e1f1fffff033ffe 0xf6e1f1fffff033ff

def z261 : W := mkw 0x00412b42582d6b59 0x400412b42582d6b5 0xf1e3ffc7f8ffffff 0xff1e3ffc7f8fffff

def z262 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z263 : W := mkw 0x0200142400000000 0x0020014240000000 0x40001e3e00000004 0x140001e3e0000000

def z264 : W := mkw 0x4040099180000000 0x0404009918000000 0x000001c1c0000000 0x0000001c1c000000

def z265 : W := mkw 0x0000200000084000 0x0000020000008400 0x1020e000001cc001 0x01020e000001cc00

def z266 : W := mkw 0x0dbfc00032030000 0x00dbfc0003203000 0xafffe0003f03000b 0xeafffe0003f03000

def z267 : W := mkw 0x4dfac9b580000000 0x04dfac9b58000000 0xc1ffe1ffc0000003 0x0c1ffe1ffc000000

def z268 : W := mkw 0x1b601fc009243b0c 0x01b601fc009243b0 0x8fe01fc000003f05 0xf8fe01fc000003f0

def z269 : W := mkw 0x09ac800024d28000 0x009ac800024d2800 0xbffc80003fffc00b 0xebffc80003fffc00

def z270 : W := mkw 0x2417002e320304c3 0x02417002e320304c 0x601f183e20033cce 0x7601f183e20033cc

def z271 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x7e1f9f3f3f03ffff 0xf7e1f9f3f3f03fff

def z272 : W := mkw 0x0000024008042108 0x0000002400804210 0x10000000181c2308 0x010000000181c230

def z273 : W := mkw 0x0416000022020000 0x0041600002202000 0x2e1c000027000000 0x42e1c00002700000

def z274 : W := mkw 0x0040090000200a00 0x00040090000200a0 0x91c0010000e00301 0x091c0010000e0030

def z275 : W := mkw 0x8dffe91136fbca20 0x88dffe91136fbca2 0xbfffe1013fffc33b 0xebfffe1013fffc33

def z276 : W := mkw 0x8dfec91926f28ea2 0x88dfec91926f28ea 0xafdc183827e01c00 0x5afdc183827e01c0

def z277 : W := mkw 0x46daddb580000000 0x046daddb58000000 0x401fffffc0000006 0x1401fffffc000000

def z278 : W := mkw 0x8dbec00026d28000 0x08dbec00026d2800 0xbffc00003ffc0009 0xebffc00003ffc000

def z279 : W := mkw 0x00c8891100000000 0x000c889110000000 0xd1dc99390003e3ff 0x7d1dc99390003e3f

def z280 : W := mkw 0x0ffadd8000000000 0x00ffadd800000000 0x8fffffc000000007 0xf8fffffc00000000

def z281 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xafdfe00027e3c002 0x4afdfe00027e3c00

def z282 : W := mkw 0x1000004004b40b0c 0x01000004004b40b0 0x1000000000fc0300 0x01000000000fc030

def z283 : W := mkw 0x44dec93da0628ea2 0x844dec93da0628ea 0xf1dff93fe0e3ffff 0x7f1dff93fe0e3fff

def z284 : W := mkw 0xcdbfe035b6dbc000 0x0cdbfe035b6dbc00 0xffffe03fffffc00b 0xeffffe03fffffc00

def z285 : W := mkw 0xc9e8e99184d8c000 0x0c9e8e99184d8c00 0x91e0e1c1c0fcc001 0x091e0e1c1c0fcc00

def z286 : W := mkw 0x66571fbfbb0334c3 0x066571fbfbb0334c 0x6e1f1fffff033cce 0xf6e1f1fffff033cc

def z287 : W := mkw 0x00012242580d6159 0x400012242580d615 0x402367c7d81c23f4 0x8402367c7d81c23f

def z288 : W := mkw 0x12413fc2592d7b5d 0x412413fc2592d7b5 0x5023ffc7d81fffff 0xb5023ffc7d81ffff

def z289 : W := mkw 0x0001200010094000 0x0000120001009400 0x0003e0000003c002 0x00003e0000003c00

def z290 : W := mkw 0x049f800032438000 0x0049f80003243800 0xbfdf80003fe3c00b 0xebfdf80003fe3c00

def z291 : W := mkw 0x1be89fd10db43b0c 0x01be89fd10db43b0 0xfffc9ff93ffc3f0f 0xffffc9ff93ffc3f0

def z292 : W := mkw 0x8dbae00004d8c000 0x08dbae00004d8c00 0x9fffe00000fcc003 0xe9fffe00000fcc00

def z293 : W := mkw 0x2413002612010041 0x0241300261201004 0x0003000600000000 0x0000300060000000

def z294 : W := mkw 0x00002242480c6159 0x400002242480c615 0x5020e7c7c01ce3f5 0x05020e7c7c01ce3f

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0x10200000181c0009 0xa10200000181c000

def z296 : W := mkw 0x0001000210010041 0x0000100021001004 0x40030006000300c2 0x040030006000300c

def z297 : W := mkw 0x2612162e090034c3 0x02612162e090034c 0x4e1f1e3e00003cc6 0xf4e1f1e3e00003cc

def z298 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xffffe1013fffe3ff 0xeffffe1013fffe3f

def z299 : W := mkw 0x849ec00022428000 0x0849ec0002242800 0x001c000000000000 0x0001c00000000000

def z300 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xe1dc993920e01c07 0x7e1dc993920e01c0

def z301 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x401f1e3e00033cc6 0x1401f1e3e00033cc

def z302 : W := mkw 0x06133666580d6159 0x406133666580d615 0x5e3fffffd81fe3ff 0xf5e3fffffd81fe3f

def z303 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x6e1c183827033cce 0x76e1c183827033cc

def z304 : W := mkw 0x0000000000000000 0x0000000000000000 0x2e0000003f000008 0xe2e0000003f00000

def z305 : W := mkw 0x2005000a320304c3 0x02005000a320304c 0x00000000000300c0 0x000000000000300c

def z306 : W := mkw 0x0040090000000000 0x0004009000000000 0x81c0190000000005 0x781c019000000000

def z307 : W := mkw 0x00c9ab53586deb79 0xc00c9ab53586deb7 0xd1e3e7c7d8ffe3ff 0xad1e3e7c7d8ffe3f

def z308 : W := mkw 0x99e8e9c004fccb0c 0x099e8e9c004fccb0 0x91e0e1c000fcc301 0x091e0e1c000fcc30

def z309 : W := mkw 0x9fffffc27ffffb5d 0x49fffffc27ffffb5 0xffffffc7ffffffff 0xfffffffc7fffffff

def z310 : W := mkw 0x0004000820628ea2 0x80004000820628ea 0x7000810120e3ffff 0x27000810120e3fff

def z311 : W := mkw 0x00012240180d6108 0x000012240180d610 0x1023e7c0181fe30f 0xa1023e7c0181fe30

def z312 : W := mkw 0x0dbbe242580d6159 0x40dbbe242580d615 0xdfffe7c7d81fe3ff 0xedfffe7c7d81fe3f

def z313 : W := mkw 0x49e8c99180000000 0x049e8c9918000000 0x81c0000000000000 0x081c000000000000

def z314 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xe1dc193920e03ff4 0x5e1dc193920e03ff

def z315 : W := mkw 0x00012242580d6159 0x400012242580d615 0x00000000181c0000 0x000000000181c000

def z316 : W := mkw 0x0000000000000000 0x0000000000000000 0x4003060600000006 0xa400306060000000

def z317 : W := mkw 0x1b613fc01dbd7b0c 0x01b613fc01dbd7b0 0xbfe3ffc03fffff0f 0xfbfe3ffc03fffff0

def z318 : W := mkw 0x0417000832030482 0x0041700083203048 0x6e1f18383f033cce 0xf6e1f18383f033cc

def z319 : W := mkw 0x0001024218052149 0x0000102421805214 0x502307c6181f23cf 0xa502307c6181f23c

def z320 : W := mkw 0x00002240480c6118 0x400002240480c611 0x1020e7c1d81ce33d 0xa1020e7c1d81ce33

def z321 : W := mkw 0x4f3254a480000000 0x04f3254a48000000 0x0e00000000000000 0x00e0000000000000

def z322 : W := mkw 0x0001000010010000 0x0000100001001000 0x000300001803000a 0xa000300001803000

def z323 : W := mkw 0x2617162e3b63bee3 0x82617162e3b63bee 0x7e1f1e3e3fe3fffe 0xf7e1f1e3e3fe3fff

def z324 : W := mkw 0x9f3376c01f9d710c 0x09f3376c01f9d710 0x0e2366c01f1c0000 0x80e2366c01f1c000

def z325 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0x8fff7efec0000000 0xd8fff7efec000000

def z326 : W := mkw 0x2004000823021482 0x0200400082302148 0x2000000027001c00 0x02000000027001c0

def z327 : W := mkw 0x041702023a032041 0x0041702023a03204 0x6e1f06063f0320ce 0xe6e1f06063f0320c

def z328 : W := mkw 0x261316261b013041 0x0261316261b01304 0x2e031e063f003c0c 0xf2e031e063f003c0

def z329 : W := mkw 0x1b611fc21db53b4d 0x01b611fc21db53b4 0xffe31fc63fff3fcf 0xfffe31fc63fff3fc

def z330 : W := mkw 0x0004000820020482 0x0000400082002048 0x701c99392003ffff 0x7701c99392003fff

def z331 : W := mkw 0x89a8e04044dcc118 0x489a8e04044dcc11 0x91e0e1c1c0fcc331 0x091e0e1c1c0fcc33

def z332 : W := mkw 0x4ffadfb589003000 0x04ffadfb58900300 0xefffffffff003c0f 0xfefffffffff003c0

def z333 : W := mkw 0x0b601d8004900000 0x00b601d800490000 0xbfe01fc03ffc000d 0xfbfe01fc03ffc000

def z334 : W := mkw 0x00c8a951406ccb38 0xc00c8a951406ccb3 0x91e0e1c1c0fcc331 0x091e0e1c1c0fcc33

def z335 : W := mkw 0x8d32400006900000 0x08d3240000690000 0x0e00000007000000 0x00e0000000700000

def z336 : W := mkw 0x0b601d8000000000 0x00b601d800000000 0x8fc0180000000000 0x58fc018000000000

def z337 : W := mkw 0x2205160a3b0334c3 0x02205160a3b0334c 0x2e001e003f033ccc 0xf2e001e003f033cc

def z338 : W := mkw 0x4ffeddbda0020482 0x04ffeddbda002048 0xefffffffe0033ccf 0xfefffffffe0033cc

def z339 : W := mkw 0x0000020009003000 0x0000002000900300 0x200000003f003c08 0x0200000003f003c0

def z340 : W := mkw 0x89a8e00004d8c000 0x089a8e00004d8c00 0xbfe0e0003ffcc009 0xebfe0e0003ffcc00

def z341 : W := mkw 0x0000000000000000 0x0000000000000000 0xb1c0000020e00009 0x6b1c0000020e0000

def z342 : W := mkw 0x22cc9f3f2962bee3 0x822cc9f3f2962bee 0xf1dc9f3f20e3ffff 0x7f1dc9f3f20e3fff

def z343 : W := mkw 0x4ffeddbda0628ea2 0x84ffeddbda0628ea 0xefffffffe0e01c07 0xfefffffffe0e01c0

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0x0023e00000000003 0xa0023e0000000000

def z345 : W := mkw 0x1bec9fc02df6bb0c 0x01bec9fc02df6bb0 0xbffc9fc03fffff0f 0xfbffc9fc03fffff0

def z346 : W := mkw 0x0040091900200ea2 0x80040091900200ea 0x0000183800001c00 0x10000183800001c0

def z347 : W := mkw 0x1f721fe40db43b0c 0x01f721fe40db43b0 0xffff1ffe3ffc3f0f 0xfffff1ffe3ffc3f0

def z348 : W := mkw 0x00c8891100000000 0x000c889110000000 0x81c0810100000001 0x081c081010000000

def z349 : W := mkw 0x4be8dd9180000000 0x04be8dd918000000 0x8fe0ffc1c0000005 0xf8fe0ffc1c000000

def z350 : W := mkw 0x2616162c2b023482 0x02616162c2b02348 0x2e1c1e383f003c0c 0xf2e1c1e383f003c0

def z351 : W := mkw 0x0005224a786feffb 0xc0005224a786feff 0x7023e7c7f8ffffff 0xa7023e7c7f8fffff

def z352 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x6e3f7efeff1f3cce 0xf6e3f7efeff1f3cc

def z353 : W := mkw 0x4ffeddbda04284a2 0x84ffeddbda04284a 0xcfffffffc003c0f7 0xfcfffffffc003c0f

def z354 : W := mkw 0x1b641fc82db63f8e 0x01b641fc82db63f8 0xfffc1ff83fff3fcf 0xffffc1ff83fff3fc

def z355 : W := mkw 0x2201366e590d75db 0x42201366e590d75d 0x5023ffffd81fffff 0xb5023ffffd81ffff

def z356 : W := mkw 0x4412402480000000 0x0441240248000000 0x00036006c0000000 0x000036006c000000

def z357 : W := mkw 0x4ffadff588042108 0x04ffadff58804210 0xdfffffffd81c230f 0xfdfffffffd81c230

def z358 : W := mkw 0x3f3716ee3f9735cf 0x03f3716ee3f9735c 0x6e3f1efe3f1f3cce 0xf6e3f1efe3f1f3cc

def z359 : W := mkw 0xafbff66e7fdff5db 0x4afbff66e7fdff5d 0xffffffffffffffff 0xffffffffffffffff

def z360 : W := mkw 0x2005020a3b0334c3 0x02005020a3b0334c 0x600306063f033cce 0xa600306063f033cc

def z361 : W := mkw 0x2617362e3b0b74c3 0x02617362e3b0b74c 0x7e3ffe3e3f1ffccf 0xf7e3ffe3e3f1ffcc

def z362 : W := mkw 0x261336665b0d7159 0x4261336665b0d715 0x5e23e7c7df1fe3ff 0xa5e23e7c7df1fe3f

def z363 : W := mkw 0x0044090820220e82 0x00044090820220e8 0xf1dc193820e33fcf 0x7f1dc193820e33fc

def z364 : W := mkw 0x09a8c00000000000 0x009a8c0000000000 0x81e0e00000000001 0x081e0e0000000000

def z365 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfc018003ffc3f08 0x5bfc018003ffc3f0

def z366 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0x8fe3e7c7c0000001 0x88fe3e7c7c000000

def z367 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xd1dc813900e3c3f3 0x0d1dc813900e3c3f

def z368 : W := mkw 0x0001220258096051 0x4000122025809605 0x4003e607d803e0fe 0xa4003e607d803e0f

def z369 : W := mkw 0x5ffaddf584b40b0c 0x05ffaddf584b40b0 0xdfffffffc0fc0307 0xfdfffffffc0fc030

def z370 : W := mkw 0x8fbff6003fdbf000 0x08fbff6003fdbf00 0xbffffe003ffffc0f 0xfbffffe003ffffc0

def z371 : W := mkw 0x8925200036dbc000 0x08925200036dbc00 0xbfe000003fffc009 0xebfe000003fffc00

def z372 : W := mkw 0x5ffadff589243b0c 0x05ffadff589243b0 0xcfffffffc0003f07 0xfcfffffffc0003f0

def z373 : W := mkw 0x0040090000200a00 0x00040090000200a0 0x0000190000003f04 0x10000190000003f0

def z374 : W := mkw 0x8413600012094000 0x0841360001209400 0x0003600000000000 0x0000360000000000

def z375 : W := mkw 0x0088800000000000 0x0008880000000000 0x81dc800000000003 0x681dc80000000000

def z376 : W := mkw 0x120016c00904310c 0x0120016c00904310 0x000006c000000000 0x0000006c00000000

def z377 : W := mkw 0x00002040400c4118 0x400002040400c411 0x5023e7c7c01cc337 0xa5023e7c7c01cc33

def z378 : W := mkw 0x8417200036dbc000 0x08417200036dbc00 0x3e1f00003fffc00a 0xe3e1f00003fffc00

def z379 : W := mkw 0x0005224a786feffb 0xc0005224a786feff 0x3000000038fffff8 0x03000000038fffff

def z380 : W := mkw 0x00012242580d6159 0x400012242580d615 0x102366c6d81fe3f8 0x8102366c6d81fe3f

def z381 : W := mkw 0x02013642590d7159 0x402013642590d715 0x7e23ffc7ff1fffff 0xf7e23ffc7ff1ffff

def z382 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0x91ffe00000ffc003 0x091ffe00000ffc00

def z383 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xb1dc193820e03f0d 0x7b1dc193820e03f0

def z384 : W := mkw 0x449ac03580000000 0x0449ac0358000000 0x403fe7ffc0000007 0xa403fe7ffc000000

def z385 : W := mkw 0xdffffff5bffffb0c 0x0dffffff5bffffb0 0xffffffffffffff0f 0xfffffffffffffff0

def z386 : W := mkw 0x0000024008042108 0x0000002400804210 0x000007c000002304 0x0000007c00000230

def z387 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xafc01fc027e03f04 0x5afc01fc027e03f0

def z388 : W := mkw 0x12401d8001201a04 0x012401d8001201a0 0x0000180000001c00 0x10000180000001c0

def z389 : W := mkw 0x8dbbe00016994000 0x08dbbe0001699400 0x8fffe0001f1c0003 0xe8fffe0001f1c000

def z390 : W := mkw 0x0412000000000000 0x0041200000000000 0x0e1f000000000002 0xe0e1f00000000000

def z391 : W := mkw 0x00cc8919204284a2 0x800cc8919204284a 0xc1dc99390003c0f7 0x7c1dc99390003c0f

def z392 : W := mkw 0x2617166e3b0735cb 0x02617166e3b0735c 0x7e3f1ffe3f1f3fcf 0xf7e3f1ffe3f1f3fc

def z393 : W := mkw 0x1bec9d9925f29ea6 0x81bec9d9925f29ea 0xffdc993927e3ffff 0x7ffdc993927e3fff

def z394 : W := mkw 0x092002400c942108 0x0092002400c94210 0xbfe007c03ffc230d 0xebfe007c03ffc230

def z395 : W := mkw 0x449ec03da04284a2 0x8449ec03da04284a 0x401fe03fc003c0f2 0x0401fe03fc003c0f

def z396 : W := mkw 0x9b653fc03ffffb0c 0x09b653fc03ffffb0 0xbfe01fc03fffff0d 0xfbfe01fc03fffff0

def z397 : W := mkw 0x8dbec00026d28000 0x08dbec00026d2800 0xbfdc800027e3c00b 0x6bfdc800027e3c00

def z398 : W := mkw 0x00cda91b706bcef3 0xc00cda91b706bcef 0xf1dff93fe0e3ffff 0x7f1dff93fe0e3fff

def z399 : W := mkw 0x0bec9d9920628ea2 0x80bec9d9920628ea 0xfffc9ff920e3ffff 0xffffc9ff920e3fff

def z400 : W := mkw 0x0000000000000000 0x0000000000000000 0x002007c000000005 0xa002007c00000000

def z401 : W := mkw 0xcffffff7fedfe159 0x4cffffff7fedfe15 0xffffffffffffe3ff 0xfffffffffffffe3f

def z402 : W := mkw 0x6fffdfbfbb0334c3 0x06fffdfbfbb0334c 0xefdf1e3e3f033cce 0xfefdf1e3e3f033cc

def z403 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0x91e01fc000fc3f05 0x191e01fc000fc3f0

def z404 : W := mkw 0x4ffbfff7d80d6159 0x44ffbfff7d80d615 0xcfffffffd81c0007 0xfcfffffffd81c000

def z405 : W := mkw 0x0dbac00000000000 0x00dbac0000000000 0xcfffe7c7c0000007 0xecfffe7c7c000000

def z406 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xb1dc983820e3dc0b 0x7b1dc983820e3dc0

def z407 : W := mkw 0x00400b4008242b08 0x000400b4008242b0 0xb1e01fc038fc3f0d 0xfb1e01fc038fc3f0

def z408 : W := mkw 0x0001200250094051 0x4000120025009405 0x5023e007d81fc0fb 0xa5023e007d81fc0f

def z409 : W := mkw 0x2205162e3b0334c3 0x02205162e3b0334c 0x60001e3e3f033ccc 0x160001e3e3f033cc

def z410 : W := mkw 0xa69ff62e3b4bf4c3 0x0a69ff62e3b4bf4c 0x6e1ffe3e3f03fcce 0xf6e1ffe3e3f03fcc

def z411 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x2e1c18383f033cc8 0x52e1c18383f033cc

def z412 : W := mkw 0x89ade00036dbc000 0x089ade00036dbc00 0xb1e0e0003fffc009 0x0b1e0e0003fffc00

def z413 : W := mkw 0x1b601dc004b40b0c 0x01b601dc004b40b0 0x9fe01fc000fc0305 0xf9fe01fc000fc030

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000810100000007 0x2400081010000000

def z415 : W := mkw 0x0001020218012041 0x0000102021801204 0x00000000180320c8 0x000000000180320c

def z416 : W := mkw 0x0044090820628ea2 0x80044090820628ea 0xb1c0190020e3fffd 0x7b1c0190020e3fff

def z417 : W := mkw 0x008c8019204284a2 0x8008c8019204284a 0xf1dc803920e3c0fb 0x6f1dc803920e3c0f

def z418 : W := mkw 0x0044091920628ea2 0x80044091920628ea 0x7000193920e3fffc 0x17000193920e3fff

def z419 : W := mkw 0x4ffbfdb590094000 0x04ffbfdb59009400 0xdfffffffd81fc00f 0xfdfffffffd81fc00

def z420 : W := mkw 0x0000004000040108 0x0000000400004010 0x102001c0001c0301 0x0102001c0001c030

def z421 : W := mkw 0x9ffffd8037fbda04 0x09ffffd8037fbda0 0xbffff8003fffdc0b 0xfbffff8003fffdc0

def z422 : W := mkw 0x9fffffd93fffffae 0x89fffffd93fffffa 0xfffffff93fffffff 0xffffffff93ffffff

def z423 : W := mkw 0x7fffdfffbfb73fcf 0x07fffdfffbfb73fc 0xffffffffffff3fcf 0xfffffffffffff3fc

def z424 : W := mkw 0x0088801100408020 0x8008880110040802 0x000080010000c030 0x0000080010000c03

def z425 : W := mkw 0x6f3756aebb0334c3 0x06f3756aebb0334c 0x6e3f7efeff033cce 0xf6e3f7efeff033cc

def z426 : W := mkw 0xbfffffee3fffffcf 0x0bfffffee3fffffc 0xfffffffe3fffffcf 0xffffffffe3fffffc

def z427 : W := mkw 0x469ad43580000000 0x0469ad4358000000 0x4e1ffe3fc0000006 0xf4e1ffe3fc000000

def z428 : W := mkw 0x10400b400db43b0c 0x010400b400db43b0 0xb1c019003ffc3f0d 0x7b1c019003ffc3f0

def z429 : W := mkw 0x8dbfe04076dfc118 0x48dbfe04076dfc11 0xbfffe1c1ffffc33b 0xebfffe1c1ffffc33

def z430 : W := mkw 0x4ffeddbda0628ea2 0x84ffeddbda0628ea 0xffdc993920e3ffff 0x7ffdc993920e3fff

def z431 : W := mkw 0x0920000004900000 0x0092000000490000 0x0e2000001f1c0000 0x80e2000001f1c000

def z432 : W := mkw 0x42413ff7d80d6159 0x442413ff7d80d615 0x5023ffffd81fe3ff 0xb5023ffffd81fe3f

def z433 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0x0e3fe0001f1fc002 0x80e3fe0001f1fc00

def z434 : W := mkw 0x00cc890020628a00 0x000cc890020628a0 0xb1dc990020e3ff0f 0x7b1dc990020e3ff0

def z435 : W := mkw 0x849fe000324bc000 0x0849fe000324bc00 0xb1dfe00020e3c00b 0x6b1dfe00020e3c00

def z436 : W := mkw 0x8dbfe00836fbcea2 0x88dbfe00836fbcea 0xbfffe0003ffffffb 0xebfffe0003ffffff

def z437 : W := mkw 0x26571f2e3b233ec3 0x026571f2e3b233ec 0xffdf1f3e3fe33fcf 0xfffdf1f3e3fe33fc

def z438 : W := mkw 0x9fbff6c03fdff10c 0x09fbff6c03fdff10 0xbfffe6c03fffc00b 0xebfffe6c03fffc00

def z439 : W := mkw 0x00c8891900608ea2 0x800c8891900608ea 0xd1c0993900e0fff5 0x1d1c0993900e0fff

def z440 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x2e001fc03f003f0c 0xf2e001fc03f003f0

def z441 : W := mkw 0x1000000005b01a04 0x01000000005b01a0 0x2000000027e01c00 0x02000000027e01c0

def z442 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfdc1fffc0000004 0x5cfdc1fffc000000

def z443 : W := mkw 0x0004000820628ea2 0x80004000820628ea 0x701c183820e3fffe 0x7701c183820e3fff

def z444 : W := mkw 0xaf3376261f997041 0x0af3376261f99704 0x0e2366061f1c0000 0x80e2366061f1c000

def z445 : W := mkw 0x008c800020428000 0x0008c80002042800 0xf1dc810120e3e3ff 0x6f1dc810120e3e3f

def z446 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xb1c0810120e3fff9 0x0b1c0810120e3fff

def z447 : W := mkw 0x4f725da480000000 0x04f725da48000000 0x8fe37fc6c0000005 0xf8fe37fc6c000000

def z448 : W := mkw 0x5f725fe48db43b0c 0x05f725fe48db43b0 0xbfe37fc6fffc3f0d 0xfbfe37fc6fffc3f0

def z449 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0x401c99390003fff6 0x1401c99390003fff

def z450 : W := mkw 0x00012242580d6159 0x400012242580d615 0x500007c7d81fe3fc 0x0500007c7d81fe3f

def z451 : W := mkw 0x196009c004b40b0c 0x0196009c004b40b0 0xb1e019c020fc3f0d 0x7b1e019c020fc3f0

def z452 : W := mkw 0x20cd8b1b3b63bee3 0x820cd8b1b3b63bee 0xf1dc99393fe3ffff 0x7f1dc99393fe3fff

def z453 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x10201fc0181c3f0d 0xb10201fc0181c3f0

def z454 : W := mkw 0x1f771fc03fb73b0c 0x01f771fc03fb73b0 0xbfff1fc03fff3f0f 0xfbfff1fc03fff3f0

def z455 : W := mkw 0x3f773fee7fbf7fdf 0x43f773fee7fbf7fd 0xffffffffffffffff 0xffffffffffffffff

def z456 : W := mkw 0xafbed42c27d29482 0x0afbed42c27d2948 0xafdc183827e01c00 0x5afdc183827e01c0

def z457 : W := mkw 0x46521db580000000 0x046521db58000000 0x4e1f1fffc0000006 0xf4e1f1fffc000000

def z458 : W := mkw 0x89a9e00014d9c000 0x089a9e00014d9c00 0x91e3e00018ffc00b 0xa91e3e00018ffc00

def z459 : W := mkw 0x9f737fc01fbd7b0c 0x09f737fc01fbd7b0 0xbfe37fc03ffc3f0d 0xfbfe37fc03ffc3f0

def z460 : W := mkw 0xa617362e3fdbf4c3 0x0a617362e3fdbf4c 0x7e1f1e3e3ffffcce 0xf7e1f1e3e3ffffcc

def z461 : W := mkw 0x0000200040084010 0x4000020004008401 0x0000e001c000c030 0x00000e001c000c03

def z462 : W := mkw 0x8dbfc00036d38000 0x08dbfc00036d3800 0xafdf00003fe3000a 0xeafdf00003fe3000

def z463 : W := mkw 0x1b2136c25d9d715d 0x41b2136c25d9d715 0x5e23e7c7df1fe3ff 0xa5e23e7c7df1fe3f

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x5023e7c7c003e3ff 0xa5023e7c7c003e3f

def z465 : W := mkw 0x00012242580d6159 0x400012242580d615 0x1020e1c1d81fe3f9 0x01020e1c1d81fe3f

def z466 : W := mkw 0x04df891932638ea2 0x804df891932638ea 0xffdf99393fe3ffff 0xfffdf99393fe3fff

def z467 : W := mkw 0x00c8891100000000 0x000c889110000000 0x81dc183800000000 0x581dc18380000000

def z468 : W := mkw 0x0000000240000051 0x4000000024000005 0x40000007c00000f0 0x040000007c00000f

def z469 : W := mkw 0x0040091100000000 0x0004009110000000 0x4000193900000004 0x1400019390000000

def z470 : W := mkw 0x008c801920628ea2 0x8008c801920628ea 0x701c803920e3fffa 0x0701c803920e3fff

def z471 : W := mkw 0x100122425dbd7b5d 0x4100122425dbd7b5 0x7023e7c7ffffffff 0xa7023e7c7fffffff

def z472 : W := mkw 0x008c800820628ea2 0x8008c800820628ea 0xb1dc800020e3fffb 0x6b1dc800020e3fff

def z473 : W := mkw 0x5ffadff58db43b0c 0x05ffadff58db43b0 0xbffc1ff83ffc3f0d 0xfbffc1ff83ffc3f0

def z474 : W := mkw 0x02401f0009203a00 0x002401f0009203a0 0xbfc01f003fe03f0d 0xfbfc01f003fe03f0

def z475 : W := mkw 0x2613162e1b0134c3 0x02613162e1b0134c 0x4e031e3e1f003cc4 0x94e031e3e1f003cc

def z476 : W := mkw 0x0d37000036930000 0x00d3700003693000 0xbfff00003fff000b 0xebfff00003fff000

def z477 : W := mkw 0x32401fee09243fcf 0x032401fee09243fc 0x40001ffe00003fc4 0x140001ffe00003fc

def z478 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x2e1f1e3e3f001c00 0xd2e1f1e3e3f001c0

def z479 : W := mkw 0x00012242580d6159 0x400012242580d615 0x4003e7c7c003e3f6 0x04003e7c7c003e3f

def z480 : W := mkw 0x10cc8b592df6bfae 0x810cc8b592df6bfa 0xf1dc99393fffffff 0x7f1dc99393ffffff

def z481 : W := mkw 0x84dfe919326bcea2 0x884dfe919326bcea 0xf1dff93920e3ffff 0x7f1dff93920e3fff

def z482 : W := mkw 0x00c9ab53580d6159 0x400c9ab53580d615 0xd1ffffffd81fe3ff 0xfd1ffffffd81fe3f

def z483 : W := mkw 0x261316261b013041 0x0261316261b01304 0x4e1f1e3e1f000006 0xf4e1f1e3e1f00000

def z484 : W := mkw 0x0000024248042159 0x4000002424804215 0x502007c7d81c23fd 0xa502007c7d81c23f

def z485 : W := mkw 0x0000000000000000 0x0000000000000000 0x100080000003c00b 0x2100080000003c00

def z486 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0x8ffcf9f9c0000001 0x58ffcf9f9c000000

def z487 : W := mkw 0x0000000000000000 0x0000000000000000 0x100001000000230d 0x2100001000000230

def z488 : W := mkw 0x061716003b033000 0x0061716003b03300 0x2e1f1e003f033c0e 0xf2e1f1e003f033c0

def z489 : W := mkw 0x0004000820628ea2 0x80004000820628ea 0x2000000020e01c00 0x02000000020e01c0

def z490 : W := mkw 0x8005200036dbc000 0x08005200036dbc00 0x3023e0003fffc00b 0xa3023e0003fffc00

def z491 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0x9fe007c01ffc0301 0x89fe007c01ffc030

def z492 : W := mkw 0x849fe000324bc000 0x0849fe000324bc00 0x2e1fe0003f03c00a 0xe2e1fe0003f03c00

def z493 : W := mkw 0x0001200250094051 0x4000120025009405 0x4023e7c7c003c0f7 0xa4023e7c7c003c0f

def z494 : W := mkw 0x8d376000369b4000 0x08d376000369b400 0x2e3f60003f1f000a 0xe2e3f60003f1f000

def z495 : W := mkw 0x0b601d8000200a00 0x00b601d8000200a0 0xbfe01fc020e03f0d 0xfbfe01fc020e03f0

def z496 : W := mkw 0x0000024008042108 0x0000002400804210 0x5023e7c7d81c230f 0xa5023e7c7d81c230

def z497 : W := mkw 0x449be277d80d6159 0x4449be277d80d615 0x503fe7ffd81fe3ff 0xa503fe7ffd81fe3f

def z498 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xe1dc983920e3dcf2 0x5e1dc983920e3dcf

def z499 : W := mkw 0x0960098000000000 0x0096009800000000 0x81e001c000000001 0x081e001c00000000

def z500 : W := mkw 0x0001024258052159 0x4000102425805215 0x400307c7d80323fe 0xa400307c7d80323f

def z501 : W := mkw 0x0004000820020482 0x0000400082002048 0x201c183820001c00 0x5201c183820001c0

def z502 : W := mkw 0xcffffdb5b6dbc000 0x0cffffdb5b6dbc00 0xbffff8383fffc00b 0xfbffff8383fffc00

def z503 : W := mkw 0x44dac93580000000 0x044dac9358000000 0xc1dff93fc0000007 0x7c1dff93fc000000

def z504 : W := mkw 0x1b603fc04dbc7b1c 0x41b603fc04dbc7b1 0xbfe0ffc1fffcff3d 0xfbfe0ffc1fffcff3

def z505 : W := mkw 0x0004000020020000 0x0000400002002000 0x201c00002003000a 0x6201c00002003000

def z506 : W := mkw 0x0000024248042159 0x4000002424804215 0x500087c7c003e3ff 0x2500087c7c003e3f

def z507 : W := mkw 0x19ec89d924f68fae 0x819ec89d924f68fa 0xf1fc99f920ffffff 0x7f1fc99f920fffff

def z508 : W := mkw 0x2417202e720b44d3 0x42417202e720b44d 0x401fe03fc003c0f2 0x0401fe03fc003c0f

def z509 : W := mkw 0x4b601db580000000 0x04b601db58000000 0xcfe01fffc0000005 0xfcfe01fffc000000

def z510 : W := mkw 0x49ecc999a0628ea2 0x849ecc999a0628ea 0xf1fcf9f9e0e3ffff 0x7f1fcf9f9e0e3fff

def z511 : W := mkw 0x0001020218012041 0x0000102021801204 0x500387071803e3ff 0xa500387071803e3f

def z512 : W := mkw 0x26571f3f3b233ee3 0x826571f3f3b233ee 0x6e1f1f3f3f033ffe 0xf6e1f1f3f3f033ff

def z513 : W := mkw 0x8dffeb5b7effeffb 0xc8dffeb5b7effeff 0xffffffffffffffff 0xffffffffffffffff

def z514 : W := mkw 0x0001020218012041 0x0000102021801204 0x0003060618000000 0x8000306061800000

def z515 : W := mkw 0x008c8019204284a2 0x8008c8019204284a 0x501c81390003e3ff 0x2501c81390003e3f

def z516 : W := mkw 0x0005224a780f65db 0x40005224a780f65d 0x703ffffff81fffff 0xf703ffffff81ffff

def z517 : W := mkw 0x00012042500d4159 0x400012042500d415 0x5023e1c7c01fc3f3 0x05023e1c7c01fc3f

def z518 : W := mkw 0x0000024248042159 0x4000002424804215 0x4023e7c7c00023f7 0xa4023e7c7c00023f

def z519 : W := mkw 0x8dbec00026d28000 0x08dbec00026d2800 0xafffe00027e00003 0xeafffe00027e0000

def z520 : W := mkw 0x3005024a3fb73fcf 0x03005024a3fb73fc 0x300000003fff3fc8 0x0300000003fff3fc

def z521 : W := mkw 0x2417226e7a0f65db 0x42417226e7a0f65d 0x503fe7ffd81fe3ff 0xa503fe7ffd81fe3f

def z522 : W := mkw 0x2fbfd62e3b0334c3 0x02fbfd62e3b0334c 0xeffffe3e3f033ccf 0xfeffffe3e3f033cc

def z523 : W := mkw 0x0b613fc2580d6159 0x40b613fc2580d615 0xdfe3ffc7d81fe3ff 0xfdfe3ffc7d81fe3f

def z524 : W := mkw 0x0dbec00020428000 0x00dbec0002042800 0xbfffe00020e3c00b 0xebfffe00020e3c00

def z525 : W := mkw 0x100402482df6bfae 0x8100402482df6bfa 0x300000003ffffff8 0x0300000003ffffff

def z526 : W := mkw 0x6ffbdfb79b013041 0x06ffbdfb79b01304 0xcfffffffdf000007 0xfcfffffffdf00000

def z527 : W := mkw 0x00012242580d6159 0x400012242580d615 0x4023e7c7d81c0007 0xa4023e7c7d81c000

def z528 : W := mkw 0x1b2016c00d94310c 0x01b2016c00d94310 0xbfe006c03ffc0009 0xebfe006c03ffc000

def z529 : W := mkw 0x8fbff42436dbc000 0x08fbff42436dbc00 0xfffffe3e3fffc00f 0xffffffe3e3fffc00

def z530 : W := mkw 0x849fe002724bc051 0x4849fe002724bc05 0x401fe007c003c0f2 0x0401fe007c003c0f

def z531 : W := mkw 0x02cc9f192962bea2 0x802cc9f192962bea 0xffdc9f393fe3ffff 0xfffdc9f393fe3fff

def z532 : W := mkw 0x52401ff589243b0c 0x052401ff589243b0 0x40001fffc0003f04 0x140001fffc0003f0

def z533 : W := mkw 0x8dbfe2427edfe159 0x48dbfe2427edfe15 0xbfffe6c6ffffc00b 0xebfffe6c6ffffc00

def z534 : W := mkw 0x0088801100000000 0x0008880110000000 0x401c803900000002 0x0401c80390000000

def z535 : W := mkw 0x4fbad4a480000000 0x04fbad4a48000000 0x8fffe6c6c0000003 0xe8fffe6c6c000000

def z536 : W := mkw 0x6fffddbfb20304c3 0x06fffddbfb20304c 0xcfffffffc00300c7 0xfcfffffffc00300c

def z537 : W := mkw 0x4be8ddb580000000 0x04be8ddb58000000 0xc1e0ffffc0000005 0x1c1e0ffffc000000

def z538 : W := mkw 0x00cc891120428000 0x000cc89112042800 0xf1dc993920e3c00f 0x7f1dc993920e3c00

def z539 : W := mkw 0x19600bc00db43b0c 0x019600bc00db43b0 0xb1e001c03ffc3f09 0x0b1e001c03ffc3f0

def z540 : W := mkw 0x00012040500d4118 0x400012040500d411 0x1023e1c1d81fc33b 0xa1023e1c1d81fc33

def z541 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0x8ffff83800000003 0xf8ffff8380000000

def z542 : W := mkw 0x8dfec91926f28ea2 0x88dfec91926f28ea 0xffdc993927e3ffff 0x7ffdc993927e3fff

def z543 : W := mkw 0x1bec9d9925f29ea6 0x81bec9d9925f29ea 0xafdc183827e01c00 0x5afdc183827e01c0

def z544 : W := mkw 0x06de9d3d20628ea2 0x806de9d3d20628ea 0xffdf9f3f20e3ffff 0xfffdf9f3f20e3fff

def z545 : W := mkw 0x0dbbe00010094000 0x00dbbe0001009400 0x9fffe000181fc00b 0xe9fffe000181fc00

def z546 : W := mkw 0xafffff3f3ffbfee3 0x8afffff3f3ffbfee 0xffffff3f3fffffff 0xfffffff3f3ffffff

def z547 : W := mkw 0x900522403ffffb0c 0x0900522403ffffb0 0x300000003fffff08 0x0300000003fffff0

def z548 : W := mkw 0x8001200016994000 0x0800120001699400 0x000000001f1c0000 0x0000000001f1c000

def z549 : W := mkw 0x62401fbf890034c3 0x062401fbf890034c 0x40001fffc0003cc4 0x140001fffc0003cc

def z550 : W := mkw 0x42401db580000000 0x042401db58000000 0x4023ffffc0000007 0xb4023ffffc000000

def z551 : W := mkw 0x4ffaddbd80200ea2 0x84ffaddbd80200ea 0xcfffffffc0003ff7 0xfcfffffffc0003ff

def z552 : W := mkw 0x196009c004b40b0c 0x0196009c004b40b0 0xbfe001c03ffc0309 0xebfe001c03ffc030

def z553 : W := mkw 0x9be8ffc00dfcfb0c 0x09be8ffc00dfcfb0 0xbfe0ffc03ffcff0d 0xfbfe0ffc03ffcff0

def z554 : W := mkw 0x008da000304bc000 0x0008da000304bc00 0xb1ffe00038ffc00b 0xeb1ffe00038ffc00

def z555 : W := mkw 0x1bec9fd92df6bfae 0x81bec9fd92df6bfa 0xbffc1ff83ffc3f0d 0xfbffc1ff83ffc3f0

def z556 : W := mkw 0x008da25b784fe5fb 0xc008da25b784fe5f 0x503fe7ffd81fe3ff 0xa503fe7ffd81fe3f

def z557 : W := mkw 0x0000000800000482 0x0000000080000048 0x4000183800003cc4 0x14000183800003cc

def z558 : W := mkw 0x24df893f32638ee3 0x824df893f32638ee 0xf1df993f20e3ffff 0x7f1df993f20e3fff

def z559 : W := mkw 0x8ffffd8036dbc000 0x08ffffd8036dbc00 0xbfffffc03fffc00f 0xfbfffffc03fffc00

def z560 : W := mkw 0x12401fc00db43b0c 0x012401fc00db43b0 0x30001fc03ffc3f0c 0x130001fc03ffc3f0

def z561 : W := mkw 0xafbfd62e3fd3b4c3 0x0afbfd62e3fd3b4c 0xefdf1e3e3fe33cce 0xfefdf1e3e3fe33cc

def z562 : W := mkw 0x2f771fae3b0334c3 0x02f771fae3b0334c 0xefff1ffe3f033ccf 0xfefff1ffe3f033cc

def z563 : W := mkw 0x1b601d8005b01a04 0x01b601d8005b01a0 0xafe01fc027e01c05 0xfafe01fc027e01c0

def z564 : W := mkw 0x5ffadff58d94310c 0x05ffadff58d94310 0xcfffffffdf1c0007 0xfcfffffffdf1c000

def z565 : W := mkw 0x4ffeddb5a0428000 0x04ffeddb5a042800 0xffffffffe0e3c00f 0xfffffffffe0e3c00

def z566 : W := mkw 0xafbff6263fdbf041 0x0afbff6263fdbf04 0xbfffe6063fffc00b 0xebfffe6063fffc00

def z567 : W := mkw 0x1b2016c00db43b0c 0x01b2016c00db43b0 0x3e2006c03ffc3f08 0x83e2006c03ffc3f0

def z568 : W := mkw 0xcf3374a496994000 0x0cf3374a49699400 0x0e2366c6df1c0000 0x80e2366c6df1c000

def z569 : W := mkw 0x2005020a3b63bee3 0x82005020a3b63bee 0x300000003fe3fff8 0x0300000003fe3fff

def z570 : W := mkw 0x1b601fd90db43fae 0x81b601fd90db43fa 0xffe01ff93ffc3ffd 0xfffe01ff93ffc3ff

def z571 : W := mkw 0x4ffafdf5c00c4118 0x44ffafdf5c00c411 0xdfffffffc01cc337 0xfdfffffffc01cc33

def z572 : W := mkw 0x4920408080000000 0x0492040808000000 0x002060c0c0000000 0x0002060c0c000000

def z573 : W := mkw 0x0920000000000000 0x0092000000000000 0x8fe0000000000001 0xe8fe000000000000

def z574 : W := mkw 0x42401dbd80200ea2 0x842401dbd80200ea 0x40001fffc0003ff4 0x140001fffc0003ff

def z575 : W := mkw 0xefffffbfbfdbf4c3 0x0efffffbfbfdbf4c 0xfffffffffffffccf 0xffffffffffffffcc

def z576 : W := mkw 0x849fe000324bc000 0x0849fe000324bc00 0x103fe000181fc00b 0xa103fe000181fc00

def z577 : W := mkw 0x00040008204284a2 0x800040008204284a 0x000000000003c0f0 0x0000000000003c0f

def z578 : W := mkw 0x008da01b704bc4f3 0xc008da01b704bc4f 0x401fe03fc003c0f2 0x0401fe03fc003c0f

def z579 : W := mkw 0x00cdab5b786feffb 0xc00cdab5b786feff 0xf1dc993938ffffff 0x7f1dc993938fffff

def z580 : W := mkw 0x00cc891920020482 0x000cc89192002048 0xe1dc993920033ccf 0x7e1dc993920033cc

def z581 : W := mkw 0xa005220a3fdbf4c3 0x0a005220a3fdbf4c 0x300000003ffffcc8 0x0300000003ffffcc

def z582 : W := mkw 0xc49fe035b24bc000 0x0c49fe035b24bc00 0x401fe03fc003c002 0x0401fe03fc003c00

def z583 : W := mkw 0x0200140000000000 0x0020014000000000 0x0e001e0000000004 0xf0e001e000000000

def z584 : W := mkw 0x12cc9fd92966bfae 0x812cc9fd92966bfa 0xf1dc9ff920e3ffff 0x7f1dc9ff920e3fff

def z585 : W := mkw 0x00cc8b5b6866affb 0xc00cc8b5b6866aff 0xf1dc9fffe0e3ffff 0x7f1dc9fffe0e3fff

def z586 : W := mkw 0x0040091100200a20 0x80040091100200a2 0x0000010100000330 0x0000001010000033

def z587 : W := mkw 0xcffffdb5b24bc000 0x0cffffdb5b24bc00 0xcfffffffc003c007 0xfcfffffffc003c00

def z588 : W := mkw 0x800522427edfe159 0x4800522427edfe15 0x300000003fffe3f8 0x0300000003fffe3f

def z589 : W := mkw 0x9ffedfc02ff6bb0c 0x09ffedfc02ff6bb0 0xbffc1fc03ffc3f0d 0xfbffc1fc03ffc3f0

def z590 : W := mkw 0x0001200250094051 0x4000120025009405 0x5003e107c003e3ff 0x25003e107c003e3f

def z591 : W := mkw 0x49e8c99180608a20 0x849e8c99180608a2 0x91e0e1c1c0e0c331 0x091e0e1c1c0e0c33

def z592 : W := mkw 0x3f761dac27b21e86 0x03f761dac27b21e8 0xafdc183827e01c00 0x5afdc183827e01c0

def z593 : W := mkw 0x2617142e320304c3 0x02617142e320304c 0x4e1f1e3e000300c6 0xf4e1f1e3e000300c

def z594 : W := mkw 0x8d33600016994000 0x08d3360001699400 0x1e23e0001f1fc00b 0xa1e23e0001f1fc00

def z595 : W := mkw 0x4ffbdfb798012041 0x04ffbdfb79801204 0xcfffffffd80320cf 0xfcfffffffd80320c

def z596 : W := mkw 0xcffeddb5a6d28000 0x0cffeddb5a6d2800 0xefffffffe7e00007 0xfefffffffe7e0000

def z597 : W := mkw 0x0000004040040118 0x4000000404004011 0x000001c1c0000330 0x0000001c1c000033

def z598 : W := mkw 0x1b613fc25dbd7b5d 0x41b613fc25dbd7b5 0xbfe01fc03ffffffd 0xfbfe01fc03ffffff

def z599 : W := mkw 0x0413000012010000 0x0041300001201000 0x0e0300001f000000 0x80e0300001f00000

def z600 : W := mkw 0x0616142c20020482 0x00616142c2002048 0x6e1f1e3e20033cce 0xf6e1f1e3e20033cc

def z601 : W := mkw 0x00012242580d6159 0x400012242580d615 0x1023e6c6d81fc00b 0xa1023e6c6d81fc00

def z602 : W := mkw 0x808da00036dbc000 0x0808da00036dbc00 0xb1dc80003fffc00b 0x6b1dc80003fffc00

def z603 : W := mkw 0x0000000004900000 0x0000000000490000 0x300000003ffc0008 0x0300000003ffc000

def z604 : W := mkw 0x0b601d8000000000 0x00b601d800000000 0xcfe3ffc7c0000007 0xfcfe3ffc7c000000

def z605 : W := mkw 0x041722427a0f6159 0x4041722427a0f615 0x7e3fe7c7ff1fe3ff 0xe7e3fe7c7ff1fe3f

def z606 : W := mkw 0x0000000000000000 0x0000000000000000 0x100081010000c331 0x0100081010000c33

def z607 : W := mkw 0x8dbfe000324bc000 0x08dbfe000324bc00 0x8fffe0000003c003 0xe8fffe0000003c00

def z608 : W := mkw 0x120016400db43b0c 0x0120016400db43b0 0x3e001e003ffc3f0c 0xf3e001e003ffc3f0

def z609 : W := mkw 0x1b2016c00d94310c 0x01b2016c00d94310 0x1e2007c01f1c230d 0xa1e2007c01f1c230

def z610 : W := mkw 0x00002040400c4118 0x400002040400c411 0x10000000001cc330 0x010000000001cc33

def z611 : W := mkw 0x100002400d94310c 0x0100002400d94310 0x000000001f1c0000 0x0000000001f1c000

def z612 : W := mkw 0x8dffe91136dbc000 0x08dffe91136dbc00 0xfffff9393fffc00f 0xffffff9393fffc00

def z613 : W := mkw 0x008c800020428000 0x0008c80002042800 0xa1dc000020e00000 0x4a1dc000020e0000

def z614 : W := mkw 0x19612bc25cbd6b5d 0x419612bc25cbd6b5 0xd1e3e7c7d8ffe3ff 0xad1e3e7c7d8ffe3f

def z615 : W := mkw 0x0001020218012041 0x0000102021801204 0x4023e7c7d80320cf 0xa4023e7c7d80320c

def z616 : W := mkw 0x8000200004d8c000 0x08000200004d8c00 0x1000000000fcc000 0x01000000000fcc00

def z617 : W := mkw 0x8dffe91936fbcea2 0x88dffe91936fbcea 0xbffff8383fffdc0b 0xfbffff8383fffdc0

def z618 : W := mkw 0x8dbfe2427edfe159 0x48dbfe2427edfe15 0xbfffe0003fffe3fb 0xebfffe0003fffe3f

def z619 : W := mkw 0x100002400db43b0c 0x0100002400db43b0 0x302007c03ffc3f0d 0xa302007c03ffc3f0

def z620 : W := mkw 0x06da9d3500000000 0x006da9d350000000 0xcfdf9f3f00000007 0xfcfdf9f3f0000000

def z621 : W := mkw 0x8d37600036dbc000 0x08d37600036dbc00 0x3e2360003fffc008 0x83e2360003fffc00

def z622 : W := mkw 0x2417020a3b0334c3 0x02417020a3b0334c 0x2e1f00003f033cca 0xe2e1f00003f033cc

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0x400080010003c0f2 0x0400080010003c0f

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0x002366c6c0000000 0x8002366c6c000000

def z625 : W := mkw 0x449ac03580000000 0x0449ac0358000000 0x001c003800000000 0x0001c00380000000

def z626 : W := mkw 0x00000019000004a2 0x800000019000004a 0x40000039000000f0 0x040000039000000f

def z627 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfdc993900000007 0x7cfdc99390000000

def z628 : W := mkw 0x0613162618012041 0x0061316261801204 0x4e1f1e3e180320ce 0xf4e1f1e3e180320c

def z629 : W := mkw 0x0000000800200ea2 0x80000000800200ea 0x0000000000003ff0 0x00000000000003ff

def z630 : W := mkw 0x008da242784fe159 0x4008da242784fe15 0xf1ffe7c7f8ffe3ff 0xef1ffe7c7f8ffe3f

def z631 : W := mkw 0x0001200010094000 0x0000120001009400 0x5023e7c7d81fc00f 0xa5023e7c7d81fc00

def z632 : W := mkw 0x2417002e320304c3 0x02417002e320304c 0x6e1f003e3f0300ca 0xe6e1f003e3f0300c

def z633 : W := mkw 0x2000020a090034c3 0x02000020a090034c 0x0000000000003cc0 0x00000000000003cc

def z634 : W := mkw 0x4fffddb5b2030000 0x04fffddb5b203000 0xefffffffff03000f 0xfefffffffff03000

def z635 : W := mkw 0x192000c00494010c 0x0192000c00494010 0x002000c0001c0000 0x0002000c0001c000

def z636 : W := mkw 0x00c8891100608a20 0x800c8891100608a2 0xd1dc993900e0c337 0x7d1dc993900e0c33

def z637 : W := mkw 0x00cca959606ecfba 0xc00cca959606ecfb 0xf1fcf9f9e0ffffff 0x7f1fcf9f9e0fffff

def z638 : W := mkw 0x0be89d9100000000 0x00be89d910000000 0xcffc9ff900000007 0xfcffc9ff90000000

def z639 : W := mkw 0x4f3376e6d80d6159 0x44f3376e6d80d615 0x5e23e7c7d81fe3ff 0xa5e23e7c7d81fe3f

def z640 : W := mkw 0x0005020a380324c3 0x00005020a380324c 0x601f1e3e38033cce 0xf601f1e3e38033cc

def z641 : W := mkw 0x0000000000000000 0x0000000000000000 0x4003e007c0000002 0x04003e007c000000

def z642 : W := mkw 0x0000024008042108 0x0000002400804210 0x502087c1181fe3ff 0xa502087c1181fe3f

def z643 : W := mkw 0x3b601fee0db43fcf 0x03b601fee0db43fc 0xffe01ffe3ffc3fcd 0xfffe01ffe3ffc3fc

def z644 : W := mkw 0x00cd8b1b3863aee3 0x800cd8b1b3863aee 0xf1df9f3f38e3ffff 0xff1df9f3f38e3fff

def z645 : W := mkw 0x0040091900200ea2 0x80040091900200ea 0xf1c0193920e03ffd 0x7f1c0193920e03ff

def z646 : W := mkw 0x2005224a7b0f75db 0x42005224a7b0f75d 0x7023e7c7ff1fffff 0xa7023e7c7ff1ffff

def z647 : W := mkw 0x0f721da400000000 0x00f721da40000000 0xcfff1ffe00000007 0xfcfff1ffe0000000

def z648 : W := mkw 0x2000002e000004c3 0x02000002e000004c 0x4000003e000000c0 0x04000003e000000c

def z649 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfdf1e3e00000006 0xfcfdf1e3e0000000

def z650 : W := mkw 0x008c8019204284a2 0x8008c8019204284a 0x601c98392003fcfe 0x7601c98392003fcf

def z651 : W := mkw 0x80cda91936fbcea2 0x880cda91936fbcea 0xf1dc99393fffffff 0x7f1dc99393ffffff

def z652 : W := mkw 0x0000000000608a20 0x80000000000608a2 0x1000000000e0c330 0x01000000000e0c33

def z653 : W := mkw 0x89a9e2425cdde159 0x489a9e2425cdde15 0xd1e3e7c7d8ffe3ff 0xad1e3e7c7d8ffe3f

def z654 : W := mkw 0x269f962e3b43b4c3 0x0269f962e3b43b4c 0xffdf9e3e3fe3fccf 0xfffdf9e3e3fe3fcc

def z655 : W := mkw 0x42cc9dbda0628ea2 0x842cc9dbda0628ea 0xf1dc9fffe0e3ffff 0x7f1dc9fffe0e3fff

def z656 : W := mkw 0x0200160009003000 0x0020016000900300 0x0e0006001f000000 0x80e0006001f00000

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000000320ce 0x240000000000320c

def z658 : W := mkw 0x0000024248042159 0x4000002424804215 0x000006c6c0000000 0x0000006c6c000000

def z659 : W := mkw 0x49e8e9d1c00c4118 0x449e8e9d1c00c411 0x91e0e1c1c01cc331 0x091e0e1c1c01cc33

def z660 : W := mkw 0x0612142400000000 0x0061214240000000 0x0e03060600000000 0x80e0306060000000

def z661 : W := mkw 0x2200162e090034c3 0x02200162e090034c 0x6e001e3e3f003ccc 0xf6e001e3e3f003cc

def z662 : W := mkw 0x0fbad42400000000 0x00fbad4240000000 0xcffffe3e00000007 0xfcffffe3e0000000

def z663 : W := mkw 0x0b601fc008042108 0x00b601fc00804210 0x9fe01fc0181c230d 0xf9fe01fc0181c230

def z664 : W := mkw 0x2201162e190134c3 0x02201162e190134c 0x40031e3e18033cce 0xb40031e3e18033cc

def z665 : W := mkw 0x00012242580d6159 0x400012242580d615 0x50030606181fe3fe 0xa50030606181fe3f

def z666 : W := mkw 0x0004000820020482 0x0000400082002048 0x401c0038000300c2 0x0401c0038000300c

def z667 : W := mkw 0xcfbff4a4b6dbc000 0x0cfbff4a4b6dbc00 0xbfffe6c6ffffc00b 0xebfffe6c6ffffc00

def z668 : W := mkw 0x6ffeddbda3021482 0x06ffeddbda302148 0xafdc183827001c00 0x5afdc183827001c0

def z669 : W := mkw 0x00c8891900200ea2 0x800c8891900200ea 0xc1dc993900003ff7 0x7c1dc993900003ff

def z670 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0xb1c01fc020e03f0d 0x7b1c01fc020e03f0

def z671 : W := mkw 0x2204162e290234c3 0x02204162e290234c 0x601c1e3e20033cce 0x7601c1e3e20033cc

def z672 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xe1dc183820e33cce 0x7e1dc183820e33cc

def z673 : W := mkw 0x0b20148000000000 0x00b2014800000000 0x0e2006c000000000 0x80e2006c00000000

def z674 : W := mkw 0x261716263b033041 0x0261716263b03304 0x2e1f06063f03000a 0xe2e1f06063f03000

def z675 : W := mkw 0x5ffedffdadf6bfae 0x85ffedffdadf6bfa 0xffffffffffffffff 0xffffffffffffffff

def z676 : W := mkw 0x1ffadfc00db43b0c 0x01ffadfc00db43b0 0xbfffffc03ffc3f0f 0xfbfffffc03ffc3f0

def z677 : W := mkw 0x0dfec91920628ea2 0x80dfec91920628ea 0xfffff93920e3ffff 0xffffff93920e3fff

def z678 : W := mkw 0x4ffffffff86feffb 0xc4ffffffff86feff 0xfffffffff8ffffff 0xffffffffff8fffff

def z679 : W := mkw 0x008c8019204284a2 0x8008c8019204284a 0x001c003800000000 0x0001c00380000000

def z680 : W := mkw 0x8dbfe2023edbe041 0x08dbfe2023edbe04 0xffffe6063fffe0cf 0xeffffe6063fffe0c

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0x401c183800000006 0x7401c18380000000

def z682 : W := mkw 0x89ece91924facea2 0x889ece91924facea 0xf1fcf93920ffffff 0x7f1fcf93920fffff

def z683 : W := mkw 0x00012242580d6159 0x400012242580d615 0x1023e000181fe3fb 0xa1023e000181fe3f

def z684 : W := mkw 0x1b601d8005b01a04 0x01b601d8005b01a0 0xbfc0190027e03f0d 0x7bfc0190027e03f0

def z685 : W := mkw 0x5ffbfff7ddbd7b5d 0x45ffbfff7ddbd7b5 0xffffffffffffffff 0xffffffffffffffff

def z686 : W := mkw 0x0412002400000000 0x0041200240000000 0x401f003e00000002 0x0401f003e0000000

def z687 : W := mkw 0x2417022e3b0334c3 0x02417022e3b0334c 0x601f003e3f033cca 0x0601f003e3f033cc

def z688 : W := mkw 0x2200162609003041 0x0220016260900304 0x0000060600000000 0x0000006060000000

def z689 : W := mkw 0x0040090000200a00 0x00040090000200a0 0xf1c0990120e3ffff 0x7f1c0990120e3fff

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x400007c7c0000004 0x0400007c7c000000

def z691 : W := mkw 0x9ffedd8027f29a04 0x09ffedd8027f29a0 0xafdc180027e01c00 0x5afdc180027e01c0

def z692 : W := mkw 0x00cda919306bcea2 0x800cda919306bcea 0xf1fff93938ffffff 0xff1fff93938fffff

def z693 : W := mkw 0xcffbfdb596994000 0x0cffbfdb59699400 0xcfffffffdf1c0007 0xfcfffffffdf1c000

def z694 : W := mkw 0x4dfac99180000000 0x04dfac9918000000 0x8fffe1c1c0000003 0xe8fffe1c1c000000

def z695 : W := mkw 0x196029c044bc4b1c 0x4196029c044bc4b1 0x91e0e1c1c0fcc331 0x091e0e1c1c0fcc33

def z696 : W := mkw 0x3f771fae3fb33ec7 0x03f771fae3fb33ec 0xefdf1e3e3fe33cce 0xfefdf1e3e3fe33cc

def z697 : W := mkw 0x1be89fd10df4bb2c 0x81be89fd10df4bb2 0xbfe09fc13ffcff3d 0xfbfe09fc13ffcff3

def z698 : W := mkw 0x6f3356a69b013041 0x06f3356a69b01304 0x0e2366c6df000000 0x80e2366c6df00000

def z699 : W := mkw 0x0004000020428000 0x0000400002042800 0x3000000020e3c008 0x03000000020e3c00

def z700 : W := mkw 0x420014a480000000 0x0420014a48000000 0x000006c6c0000000 0x0000006c6c000000

def z701 : W := mkw 0x00c8891100608a20 0x800c8891100608a2 0xb1c0990120e0ff3d 0x7b1c0990120e0ff3

def z702 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020e1c1c0000001 0x00020e1c1c000000

def z703 : W := mkw 0x42401db580000000 0x042401db58000000 0x0000183800000000 0x1000018380000000

def z704 : W := mkw 0x0001200010094000 0x0000120001009400 0x5023e101181fe3ff 0xa5023e101181fe3f

def z705 : W := mkw 0x00012242580d6159 0x400012242580d615 0x1023e7c7d81cc331 0x81023e7c7d81cc33

def z706 : W := mkw 0x1b601fc00d94310c 0x01b601fc00d94310 0x8fe01fc01f1c0005 0xf8fe01fc01f1c000

def z707 : W := mkw 0x0920000004900000 0x0092000000490000 0xbfe080003fffc00b 0xebfe080003fffc00

def z708 : W := mkw 0x8dbec2426ed6a159 0x48dbec2426ed6a15 0xefdc07c7e7e023f4 0x4efdc07c7e7e023f

def z709 : W := mkw 0x06133666590d7159 0x406133666590d715 0x7e3fffffff1fffff 0xf7e3fffffff1ffff

def z710 : W := mkw 0x2616166c2b06358a 0x02616166c2b06358 0x3e3c1ff83f1c3f0d 0xf3e3c1ff83f1c3f0

def z711 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1dff93fe0e3ffff 0x7f1dff93fe0e3fff

def z712 : W := mkw 0x8d73691916b94ea2 0x88d73691916b94ea 0x4e2379391f1c3ff4 0x94e2379391f1c3ff

def z713 : W := mkw 0x44dac93580000000 0x044dac9358000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z714 : W := mkw 0x5ffaddb581201a04 0x05ffaddb581201a0 0xcfffffffc0001c07 0xfcfffffffc0001c0

def z715 : W := mkw 0x00cdab5b786feffb 0xc00cdab5b786feff 0xa1ff7efef8fc1c00 0xda1ff7efef8fc1c0

def z716 : W := mkw 0x8dbbe00016d9c000 0x08dbbe00016d9c00 0x8fe360001ffc0000 0x88fe360001ffc000

def z717 : W := mkw 0x469ad43580000000 0x0469ad4358000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z718 : W := mkw 0x4ffaddb580200a00 0x04ffaddb580200a0 0xefffffffe0e01c07 0xfefffffffe0e01c0

def z719 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x2e1c1e383f033ccc 0xf2e1c1e383f033cc

def z720 : W := mkw 0x00c9ab53580d6159 0x400c9ab53580d615 0xd1dc9939181fe3ff 0x7d1dc9939181fe3f

def z721 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xdfffffffd81c000f 0xfdfffffffd81c000

def z722 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe01ec03ffc1c09 0xfbfe01ec03ffc1c0

def z723 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1c1e3e3f033ccc 0x56e1c1e3e3f033cc

def z724 : W := mkw 0xadbfe02e76dbc4d3 0x4adbfe02e76dbc4d 0xffffe03fffffc0fb 0xeffffe03fffffc0f

def z725 : W := mkw 0x549ac2758db43b0c 0x0549ac2758db43b0 0x701fe03ffffc3f0a 0x0701fe03ffffc3f0

def z726 : W := mkw 0x4ffaddb580200a00 0x04ffaddb580200a0 0xcfffffffc0003f07 0xfcfffffffc0003f0

def z727 : W := mkw 0x2617162e3b43b4e3 0x82617162e3b43b4e 0x6e1f1e3e3f03fcfe 0xf6e1f1e3e3f03fcf

def z728 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xffe01fc7fffc3f0d 0xfffe01fc7fffc3f0

def z729 : W := mkw 0x0920000004900000 0x0092000000490000 0xbfe001003ffc230d 0xebfe001003ffc230

def z730 : W := mkw 0x2617342e730b54d3 0x42617342e730b54d 0x6e1ff83fe703dcf2 0x56e1ff83fe703dcf

def z731 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xffe3ffc7ffffffff 0xfffe3ffc7fffffff

def z732 : W := mkw 0x4ffaddb581001000 0x04ffaddb58100100 0xefffffffe7001c07 0xfefffffffe7001c0

def z733 : W := mkw 0x8d376000369b4000 0x08d376000369b400 0xbfff60003fff000b 0xebfff60003fff000

def z734 : W := mkw 0x09e8891104f08a20 0x809e8891104f08a2 0x91e0810100fcc331 0x091e0810100fcc33

def z735 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfffe0003ffcc001 0xcbfffe0003ffcc00

def z736 : W := mkw 0xcdbfe080b6dbc000 0x0cdbfe080b6dbc00 0xbfffe0c0ffffc00b 0xebfffe0c0ffffc00

def z737 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfdfe0003fffc00a 0x4bfdfe0003fffc00

def z738 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x7e3f7efeff1ffffe 0xf7e3f7efeff1ffff

def z739 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xafffe0003ffc0003 0xeafffe0003ffc000

def z740 : W := mkw 0xc2453db5b6dbc000 0x0c2453db5b6dbc00 0x70001fffffffc00c 0x170001fffffffc00

def z741 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1dc983920e3fffa 0x5f1dc983920e3fff

def z742 : W := mkw 0x2616346c630e559a 0x42616346c630e559 0x3e3cf9f9e71cdf31 0x53e3cf9f9e71cdf3

def z743 : W := mkw 0x22401f7f49243ffb 0xc22401f7f49243ff 0x40001fffc0003ff4 0x140001fffc0003ff

def z744 : W := mkw 0x0b20140005901000 0x00b2014000590100 0xbfe018003ffc1c09 0xfbfe018003ffc1c0

def z745 : W := mkw 0x00002040400c4118 0x400002040400c411 0x5023e7c7c01fe3ff 0xa5023e7c7c01fe3f

def z746 : W := mkw 0x5ffaddb585b01a04 0x05ffaddb585b01a0 0xffffffffe7e03f0f 0xfffffffffe7e03f0

def z747 : W := mkw 0x00012242580d6159 0x400012242580d615 0xf1e3e7c7f8ffe3ff 0xef1e3e7c7f8ffe3f

def z748 : W := mkw 0x69edcb9bbb0334c3 0x069edcb9bbb0334c 0xa1e0e1c1ff033cc9 0x0a1e0e1c1ff033cc

def z749 : W := mkw 0x99e8e9d104fccb2c 0x899e8e9d104fccb2 0x91e0e1c100fcc331 0x091e0e1c100fcc33

def z750 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1f9f3f3f033ccf 0xf6e1f9f3f3f033cc

def z751 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1f1e3e3f001c06 0xf6e1f1e3e3f001c0

def z752 : W := mkw 0x4ffaddb584900000 0x04ffaddb58490000 0xefffffffe7e00007 0xfefffffffe7e0000

def z753 : W := mkw 0x8dbbe00016d9c000 0x08dbbe00016d9c00 0x9fe3e0001fffc00b 0xa9fe3e0001fffc00

def z754 : W := mkw 0x4ffbfff7d80d6159 0x44ffbfff7d80d615 0x9fdc1838181fe3f8 0x59fdc1838181fe3f

def z755 : W := mkw 0xa617762e3b0b74c3 0x0a617762e3b0b74c 0x6e1f7e3e3f033cce 0xf6e1f7e3e3f033cc

def z756 : W := mkw 0x8dbbe00016d9c000 0x08dbbe00016d9c00 0x9fffe0001ffcc003 0xe9fffe0001ffcc00

def z757 : W := mkw 0x32401fe609243b4d 0x032401fe609243b4 0x00001fc600003f04 0x100001fc600003f0

def z758 : W := mkw 0x02401f4009243b08 0x002401f4009243b0 0xbfe01fc03ffc3f0d 0xfbfe01fc03ffc3f0

def z759 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbffff8003ffffc0f 0xfbffff8003ffffc0

def z760 : W := mkw 0x0f721da400000000 0x00f721da40000000 0xcfffffffc0000007 0xfcfffffffc000000

def z761 : W := mkw 0x0dbfc00036930000 0x00dbfc0003693000 0xbfffe0003fff000b 0xebfffe0003fff000

def z762 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xafffe0003fffc002 0xcafffe0003fffc00

def z763 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xb1dc993920e3fff9 0x5b1dc993920e3fff

def z764 : W := mkw 0x89e9e91114f9ca20 0x889e9e91114f9ca2 0xd1e3e10118ffe3ff 0xad1e3e10118ffe3f

def z765 : W := mkw 0x196009c004b40b0c 0x0196009c004b40b0 0xbfe019c03ffc3f0d 0xfbfe019c03ffc3f0

def z766 : W := mkw 0x2613162e1b0134c3 0x02613162e1b0134c 0x4e1f1e3e1f003cc6 0xf4e1f1e3e1f003cc

def z767 : W := mkw 0x5ffeddbda5f29ea6 0x85ffeddbda5f29ea 0xafdc183827e01c00 0x5afdc183827e01c0

def z768 : W := mkw 0x0004000820020482 0x0000400082002048 0x6e1c18383f033cce 0xf6e1c18383f033cc

def z769 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x6e1c183827003cc4 0x56e1c183827003cc

def z770 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x00001ec000001c00 0x100001ec000001c0

def z771 : W := mkw 0x19600b400db43b0c 0x019600b400db43b0 0xbfe019003ffc3f0d 0xfbfe019003ffc3f0

def z772 : W := mkw 0x2617342c330b5482 0x02617342c330b548 0x3e3ff8383f1fdc0b 0xf3e3ff8383f1fdc0

def z773 : W := mkw 0x89ace00024dac000 0x089ace00024dac00 0xbffce0003fffc00b 0xebffce0003fffc00

def z774 : W := mkw 0xa005224a7fdff5db 0x4a005224a7fdff5d 0x300000003ffffff8 0x0300000003ffffff

def z775 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfff7efec0000006 0xfcfff7efec000000

def z776 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x40001fc7c0003f04 0x140001fc7c0003f0

def z777 : W := mkw 0x0b2016400d943108 0x00b2016400d94310 0xbfe01fc03ffc3f0d 0xfbfe01fc03ffc3f0

def z778 : W := mkw 0x3d7709ee36b70fcf 0x03d7709ee36b70fc 0xd1ff01fe00ff03c3 0x0d1ff01fe00ff03c

def z779 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfdfffffc0000006 0x5cfdfffffc000000

def z780 : W := mkw 0x2617162e3b43b4c3 0x02617162e3b43b4c 0x7e1f1e3e3fe3fcce 0xf7e1f1e3e3fe3fcc

def z781 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1fcf9f9e0e3ffff 0x7f1fcf9f9e0e3fff

def z782 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x6e1fffffff03fffe 0xf6e1fffffff03fff

def z783 : W := mkw 0x1b601d8005b01a04 0x01b601d8005b01a0 0xbfc018003ffc1c08 0x5bfc018003ffc1c0

def z784 : W := mkw 0x3f3336e65f9d715d 0x43f3336e65f9d715 0x0e2366c6df1c0000 0x80e2366c6df1c000

def z785 : W := mkw 0x2205160a3b0334c3 0x02205160a3b0334c 0x6e1c1e383f033cce 0xf6e1c1e383f033cc

def z786 : W := mkw 0x0920000004900000 0x0092000000490000 0xbfe018003ffc3c0d 0xfbfe018003ffc3c0

def z787 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x7e1f9e3e3f03fccf 0xf7e1f9e3e3f03fcc

def z788 : W := mkw 0x12401f400db43b0c 0x012401f400db43b0 0xbfc01f003ffc3f0d 0xfbfc01f003ffc3f0

def z789 : W := mkw 0x26db9f371b61ba61 0x826db9f371b61ba6 0x9fc387071fe0c331 0x89fc387071fe0c33

def z790 : W := mkw 0x0d372000369b4000 0x00d372000369b400 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z791 : W := mkw 0x0612166409043108 0x0061216640904310 0x7e3fffffff1c3f0f 0xf7e3fffffff1c3f0

def z792 : W := mkw 0xadbfe03f36dbc4e3 0x8adbfe03f36dbc4e 0xffffe03f3fffc0fb 0xeffffe03f3fffc0f

def z793 : W := mkw 0x0004000820628ea2 0x80004000820628ea 0x7023e7c7e0e3ffff 0xa7023e7c7e0e3fff

def z794 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfe3e0003fffc009 0x8bfe3e0003fffc00

def z795 : W := mkw 0x261316261b013041 0x0261316261b01304 0x6e1f1e3e3f003c0e 0xf6e1f1e3e3f003c0

def z796 : W := mkw 0x8d33600016994000 0x08d3360001699400 0xafe360003ffc0000 0xcafe360003ffc000

def z797 : W := mkw 0x00012242580d6159 0x400012242580d615 0x5023e7c7d81fc3f3 0x85023e7c7d81fc3f

def z798 : W := mkw 0x4f3254a480000000 0x04f3254a48000000 0x0e3f7efec0000000 0xd0e3f7efec000000

def z799 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1f1e3e3f031cc2 0xd6e1f1e3e3f031cc

def z800 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xe1dc993920e3fff6 0x5e1dc993920e3fff

def z801 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfffffffc00320cf 0xfcfffffffc00320c

def z802 : W := mkw 0x1b601fc24db43b5d 0x41b601fc24db43b5 0xbfe01fc6fffc3f0d 0xfbfe01fc6fffc3f0

def z803 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe018003ffc3f09 0xfbfe018003ffc3f0

def z804 : W := mkw 0x46daddb580000000 0x046daddb58000000 0x4e1fffffc0000006 0xf4e1fffffc000000

def z805 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1f1f3f3f033ffe 0xf6e1f1f3f3f033ff

def z806 : W := mkw 0x8920600004984000 0x0892060000498400 0xbfe060003ffc0009 0xebfe060003ffc000

def z807 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1f1e3e27033cc6 0x56e1f1e3e27033cc

def z808 : W := mkw 0x2616162e2b0234c3 0x02616162e2b0234c 0x6e1f1e3e27003cc6 0xf6e1f1e3e27003cc

def z809 : W := mkw 0x2617362e3b0b74c3 0x02617362e3b0b74c 0x7e3fff3f3f1fffff 0xf7e3fff3f3f1ffff

def z810 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x4023ffc7c0003f07 0xb4023ffc7c0003f0

def z811 : W := mkw 0x8dbfe01b76dbc4f3 0xc8dbfe01b76dbc4f 0xffffe03fffffc0fb 0xeffffe03fffffc0f

def z812 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x6e3fffffe7001c07 0xf6e3fffffe7001c0

def z813 : W := mkw 0xcffeddbda6f28ea2 0x8cffeddbda6f28ea 0xafdc183827e01c00 0x5afdc183827e01c0

def z814 : W := mkw 0x2612162e090034c3 0x02612162e090034c 0x6e1f1e3e3f003cce 0xf6e1f1e3e3f003cc

def z815 : W := mkw 0x0044090820220e82 0x00044090820220e8 0xf1dc993920e3ffff 0x7f1dc993920e3fff

def z816 : W := mkw 0x19e8899104f08a24 0x819e8899104f08a2 0x91c0810100e0c331 0x091c0810100e0c33

def z817 : W := mkw 0x2617362e3b0b74c3 0x02617362e3b0b74c 0x7e1f1e3e3f1ffcce 0xf7e1f1e3e3f1ffcc

def z818 : W := mkw 0x0417000832030482 0x0041700083203048 0x2e1f18383f031c0a 0xf2e1f18383f031c0

def z819 : W := mkw 0x0204140821021482 0x0020414082102148 0x2e1c183827001c00 0x52e1c183827001c0

def z820 : W := mkw 0x1bac96d92dd6b5ae 0x81bac96d92dd6b5a 0x4e3c86f91f1fc0f2 0x84e3c86f91f1fc0f

def z821 : W := mkw 0x12401fd109243b2c 0x812401fd109243b2 0x00001fc100003f34 0x100001fc100003f3

def z822 : W := mkw 0x0920000004900000 0x0092000000490000 0xffe3e7c7fffc000f 0xeffe3e7c7fffc000

def z823 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe007c03ffc3f09 0x8bfe007c03ffc3f0

def z824 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1fc993938ffffff 0xff1fc993938fffff

def z825 : W := mkw 0x4f3254a480000000 0x04f3254a48000000 0x4e3f66fec0000002 0x84e3f66fec000000

def z826 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x2e1c18383f001c08 0xf2e1c18383f001c0

def z827 : W := mkw 0x89e8c91104f08a20 0x889e8c91104f08a2 0x81c0000000e00000 0x081c0000000e0000

def z828 : W := mkw 0x008c800820428482 0x0008c80082042848 0xf1dc993920e3ffff 0x7f1dc993920e3fff

def z829 : W := mkw 0x12401fc249243b5d 0x412401fc249243b5 0x00001fc000003ff4 0x100001fc000003ff

def z830 : W := mkw 0x2617166e3b0735cb 0x02617166e3b0735c 0x7e3f9fff3f1fffff 0xf7e3f9fff3f1ffff

def z831 : W := mkw 0xcdbfe035b6dbc000 0x0cdbfe035b6dbc00 0xffffe7ffffffc00f 0xeffffe7ffffffc00

def z832 : W := mkw 0xaf3376665f9d7159 0x4af3376665f9d715 0x0e2366c6df1c0000 0x80e2366c6df1c000

def z833 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0x8fff7ffec0000005 0xf8fff7ffec000000

def z834 : W := mkw 0x04172008320b4482 0x004172008320b448 0x7e3ff9393f1fffff 0xf7e3ff9393f1ffff

def z835 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0x4e3fffffc0000006 0x94e3fffffc000000

def z836 : W := mkw 0x0612142401001000 0x0061214240100100 0x6e1f1e3e27001c06 0xf6e1f1e3e27001c0

def z837 : W := mkw 0x3b601fe60db43b4d 0x03b601fe60db43b4 0xbfe01fc63ffc3f0d 0xfbfe01fc63ffc3f0

def z838 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0xffdf1e3e3fe33ccf 0xfffdf1e3e3fe33cc

def z839 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x000007c000000300 0x0000007c00000030

def z840 : W := mkw 0x449ac03580000000 0x0449ac0358000000 0x403fe6ffc0000002 0x8403fe6ffc000000

def z841 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x2e1f18383f033cca 0xf2e1f18383f033cc

def z842 : W := mkw 0x4dbac03584900000 0x04dbac0358490000 0xffffe03ffffc000b 0xeffffe03ffffc000

def z843 : W := mkw 0x2005224a7b0f75db 0x42005224a7b0f75d 0x200000003f1f3cc8 0x0200000003f1f3cc

def z844 : W := mkw 0x1b613d8255b95a55 0x41b613d8255b95a5 0xefc3f807e7e3dcf2 0x5efc3f807e7e3dcf

def z845 : W := mkw 0x12401fe409243b0c 0x012401fe409243b0 0x40001ffe00003f04 0x140001ffe00003f0

def z846 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x7e1f1e3e3f03fffe 0xf7e1f1e3e3f03fff

def z847 : W := mkw 0x4fbad4b580000000 0x04fbad4b58000000 0xcfffe6ffc0000003 0xecfffe6ffc000000

def z848 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x2e3f7efeff1c1c00 0xd2e3f7efeff1c1c0

def z849 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xafe01fc03ffc1c05 0xfafe01fc03ffc1c0

def z850 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1f183e3f033cca 0x56e1f183e3f033cc

def z851 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfdf00003fffc00a 0xebfdf00003fffc00

def z852 : W := mkw 0x1b601fc04db43b1c 0x41b601fc04db43b1 0xbfe01fc1fffc3f3d 0xfbfe01fc1fffc3f3

def z853 : W := mkw 0x8dbec00026d28000 0x08dbec00026d2800 0xbffc80003fffc00b 0xebffc80003fffc00

def z854 : W := mkw 0x96dfffc03b6ffb0c 0x096dfffc03b6ffb0 0x001fffc00003ff06 0x1001fffc00003ff0

def z855 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x7e3f7ffeff1f3fcf 0xf7e3f7ffeff1f3fc

def z856 : W := mkw 0x4ffaddb584900000 0x04ffaddb58490000 0xcfffffffdf1c0007 0xfcfffffffdf1c000

def z857 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1fff93920e3ffff 0xff1fff93920e3fff

def z858 : W := mkw 0x0924000024920000 0x0092400002492000 0xbffc00003fff000b 0xebffc00003fff000

def z859 : W := mkw 0x4ffaddb584900000 0x04ffaddb58490000 0xdfffffffc0fc0007 0xfdfffffffc0fc000

def z860 : W := mkw 0x59e8c99184b00a04 0x059e8c99184b00a0 0x81e0e1c1c0e00001 0x081e0e1c1c0e0000

def z861 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0x9fffe0001fffc003 0x89fffe0001fffc00

def z862 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfff7fffc0000004 0xdcfff7fffc000000

def z863 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe3ffc03ffc3f0f 0xfbfe3ffc03ffc3f0

def z864 : W := mkw 0xcdbfe024b6dbc000 0x0cdbfe024b6dbc00 0xbfffe006ffffc00b 0xebfffe006ffffc00

def z865 : W := mkw 0xaba8f62e0dd8f4c3 0x0aba8f62e0dd8f4c 0xd1e0fe3e00fcfcc5 0x1d1e0fe3e00fcfcc

def z866 : W := mkw 0x0000024008042108 0x0000002400804210 0x5023e7c7d81fe3ff 0xa5023e7c7d81fe3f

def z867 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1c18383f033cce 0x76e1c18383f033cc

def z868 : W := mkw 0x0921200014994000 0x0092120001499400 0xbfe360003ffc0009 0xebfe360003ffc000

def z869 : W := mkw 0x32401fee49243fdf 0x432401fee49243fd 0x40001fffc0003ff4 0x140001fffc0003ff

def z870 : W := mkw 0x0612162409003000 0x0061216240900300 0x2e1c1e383f003c0c 0xf2e1c1e383f003c0

def z871 : W := mkw 0x52401ffd89243fae 0x852401ffd89243fa 0x40001fffc0003ff4 0x140001fffc0003ff

def z872 : W := mkw 0x0613162619013041 0x0061316261901304 0x6e1f1e3e3f033cce 0xf6e1f1e3e3f033cc

def z873 : W := mkw 0x2616162c2b023482 0x02616162c2b02348 0x6e1f1e3e3f003c0e 0xf6e1f1e3e3f003c0

def z874 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x7e1f9f3f3f1fffff 0xf7e1f9f3f3f1ffff

def z875 : W := mkw 0x1b601fc24db43b5d 0x41b601fc24db43b5 0xffe3ffc7fffc3fff 0xfffe3ffc7fffc3ff

def z876 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xffffe0003fffe0cf 0xeffffe0003fffe0c

def z877 : W := mkw 0x0044090820628ea2 0x80044090820628ea 0xf1dc193820e3ffff 0x7f1dc193820e3fff

def z878 : W := mkw 0x449ac03580000000 0x0449ac0358000000 0x401fe7ffc0000006 0x0401fe7ffc000000

def z879 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xc1ffffffc0000007 0x1c1ffffffc000000

def z880 : W := mkw 0x09ac800024d28000 0x009ac800024d2800 0xbffc00003ffc0009 0xebffc00003ffc000

def z881 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe09fc13ffcff3d 0xfbfe09fc13ffcff3

def z882 : W := mkw 0x52401ff7c9243b5d 0x452401ff7c9243b5 0x40001fffc0003ff4 0x140001fffc0003ff

def z883 : W := mkw 0x0921000014910000 0x0092100001491000 0xbfe300003fff000b 0xebfe300003fff000

def z884 : W := mkw 0xcffaddb586900000 0x0cffaddb58690000 0xcfffffffc7000007 0xfcfffffffc700000

def z885 : W := mkw 0x4dbac03580000000 0x04dbac0358000000 0xcfffe7ffc0000007 0xecfffe7ffc000000

def z886 : W := mkw 0x8d32400006900000 0x08d3240000690000 0xbfe000003ffc0009 0xebfe000003ffc000

def z887 : W := mkw 0x2617142e330314c3 0x02617142e330314c 0x6e1f183e3f031cca 0xf6e1f183e3f031cc

def z888 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfff60003ffc0009 0xebfff60003ffc000

def z889 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xffffe1013fffc00f 0xeffffe1013fffc00

def z890 : W := mkw 0x19e889d104f48b2c 0x819e889d104f48b2 0x91e001c000fc0301 0x091e001c000fc030

def z891 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfffe1c1ffffc00b 0xebfffe1c1ffffc00

def z892 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1f1fffff033cce 0xf6e1f1fffff033cc

def z893 : W := mkw 0x849fe019324bc4a2 0x8849fe019324bc4a 0x001fe0380003c002 0x0001fe0380003c00

def z894 : W := mkw 0x8dbfc00036d38000 0x08dbfc00036d3800 0xbfff00003fff000b 0xebfff00003fff000

def z895 : W := mkw 0x8d33600016994000 0x08d3360001699400 0x9fe360001ffc0001 0x89fe360001ffc000

def z896 : W := mkw 0x0925000036930000 0x0092500003693000 0xbfe000003fff0009 0xebfe000003fff000

def z897 : W := mkw 0x2617362e3b0b74c3 0x02617362e3b0b74c 0x7e3fffffff1ffccf 0xf7e3fffffff1ffcc

def z898 : W := mkw 0x849fa00036dbc000 0x0849fa00036dbc00 0xbfdf80003fffc00b 0xebfdf80003fffc00

def z899 : W := mkw 0x0416000822020482 0x0041600082202048 0x2e1c183827001c00 0x52e1c183827001c0

def z900 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1dc9fffe0e3ffff 0x7f1dc9fffe0e3fff

def z901 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1f1e3e3f003cc4 0xd6e1f1e3e3f003cc

def z902 : W := mkw 0x5b601ff7cdb43b5d 0x45b601ff7cdb43b5 0xffe01ffffffc3ffd 0xfffe01ffffffc3ff

def z903 : W := mkw 0x0d32400004900000 0x00d3240000490000 0xbfe360003ffc0009 0xebfe360003ffc000

def z904 : W := mkw 0xa49fe02c324bc482 0x0a49fe02c324bc48 0x001fe0380003c002 0x0001fe0380003c00

def z905 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xb1dc983820e3fffb 0x7b1dc983820e3fff

def z906 : W := mkw 0x1b2016400db43b0c 0x01b2016400db43b0 0xbfe01e003ffc3f0d 0xfbfe01e003ffc3f0

def z907 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfffffffc00023f7 0xfcfffffffc00023f

def z908 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x20001fc020003f0c 0x720001fc020003f0

def z909 : W := mkw 0x06da9d3500000000 0x006da9d350000000 0xcfffffffc0000007 0xfcfffffffc000000

def z910 : W := mkw 0x008c800820628ea2 0x8008c800820628ea 0xf1dc983820e3ffff 0x7f1dc983820e3fff

def z911 : W := mkw 0x0920000004900000 0x0092000000490000 0xbfe3e0003ffc000b 0xebfe3e0003ffc000

def z912 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfc01fc03ffc3f0c 0x5bfc01fc03ffc3f0

def z913 : W := mkw 0x4f3654aca0628ea2 0x84f3654aca0628ea 0x3e2366c6e0e3fff8 0x83e2366c6e0e3fff

def z914 : W := mkw 0x4ffaddb580608a20 0x84ffaddb580608a2 0xffffffffe0e0ff3f 0xfffffffffe0e0ff3

def z915 : W := mkw 0x59e9ebd3dcbd6b5d 0x459e9ebd3dcbd6b5 0xd1e3e7c7d8ffe3ff 0xad1e3e7c7d8ffe3f

def z916 : W := mkw 0x2204162e290234c3 0x02204162e290234c 0x6e1c1e3e3f033cce 0xf6e1c1e3e3f033cc

def z917 : W := mkw 0x061716243b033000 0x0061716243b03300 0x6e1f1e3e3f033c0e 0xf6e1f1e3e3f033c0

def z918 : W := mkw 0x46daddb580000000 0x046daddb58000000 0xc1dfffffc0000007 0x7c1dfffffc000000

def z919 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x7e3fffffff03ffff 0xf7e3fffffff03fff

def z920 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x10001fc000003f0d 0x310001fc000003f0

def z921 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfdc80003fffc00b 0x6bfdc80003fffc00

def z922 : W := mkw 0x0fbad42400000000 0x00fbad4240000000 0xcfffffffc0000007 0xfcfffffffc000000

def z923 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x7e1f1fffff1ffffe 0xf7e1f1fffff1ffff

def z924 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x2e1c18383f001c00 0x52e1c18383f001c0

def z925 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x4e1f1e3e1f033cc6 0x94e1f1e3e1f033cc

def z926 : W := mkw 0x0205364a790f75db 0x40205364a790f75d 0x7e3fffffff1fffff 0xf7e3fffffff1ffff

def z927 : W := mkw 0xcdbfe035b6dbc000 0x0cdbfe035b6dbc00 0xbfffe0383fffc00b 0xebfffe0383fffc00

def z928 : W := mkw 0x8dbee00026dac000 0x08dbee00026dac00 0xbffce0003ffcc009 0xebffce0003ffcc00

def z929 : W := mkw 0x0617142c32030482 0x00617142c3203048 0x6e1f1e3e3f033cce 0xf6e1f1e3e3f033cc

def z930 : W := mkw 0x00012042500d4159 0x400012042500d415 0x5023e7c7c01fc3f7 0xa5023e7c7c01fc3f

def z931 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xffe01fc03fff3fcf 0xfffe01fc03fff3fc

def z932 : W := mkw 0x2617166e3b0735cb 0x02617166e3b0735c 0x6e1f1ffe3f033fce 0xf6e1f1ffe3f033fc

def z933 : W := mkw 0x2617142e330314c3 0x02617142e330314c 0x6e1f1e3e27031cc6 0xf6e1f1e3e27031cc

def z934 : W := mkw 0x19e88bd10cf4ab2c 0x819e88bd10cf4ab2 0xd1e087c118ffe3ff 0xad1e087c118ffe3f

def z935 : W := mkw 0x661716aebb0334c3 0x0661716aebb0334c 0x6e1f1efeff033cce 0xf6e1f1efeff033cc

def z936 : W := mkw 0x2616162c2b023482 0x02616162c2b02348 0x6e1c1e383f033cce 0xf6e1c1e383f033cc

def z937 : W := mkw 0x192002400db43b0c 0x0192002400db43b0 0xbfc000003ffc3f08 0x4bfc000003ffc3f0

def z938 : W := mkw 0x89a8e00004d8c000 0x089a8e00004d8c00 0x9fe0e0001ffcc001 0x89fe0e0001ffcc00

def z939 : W := mkw 0x8dbfe00076dbc010 0x48dbfe00076dbc01 0xbfffe001ffffc03b 0xebfffe001ffffc03

def z940 : W := mkw 0x00012242580d6159 0x400012242580d615 0x503fffffd81fe3ff 0xf503fffffd81fe3f

def z941 : W := mkw 0x8d37200036dbc000 0x08d37200036dbc00 0xbfff00003fffc00b 0xebfff00003fffc00

def z942 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1dc193920e3fffc 0x5f1dc193920e3fff

def z943 : W := mkw 0x3005224a7fbf7fdf 0x43005224a7fbf7fd 0x300000003ffffff8 0x0300000003ffffff

def z944 : W := mkw 0x8925200036dbc000 0x08925200036dbc00 0xbfc000003fffc008 0x4bfc000003fffc00

def z945 : W := mkw 0x2005224a7b6ffffb 0xc2005224a7b6ffff 0x300000003ffffff8 0x0300000003ffffff

def z946 : W := mkw 0x12413fc2592d7b5d 0x412413fc2592d7b5 0x4003ffc7c003fff6 0x14003ffc7c003fff

def z947 : W := mkw 0x2617162c3b033482 0x02617162c3b03348 0x2e1f1e383f033c0e 0xf2e1f1e383f033c0

def z948 : W := mkw 0x469ad4b580000000 0x0469ad4b58000000 0x401fe6ffc0000002 0x0401fe6ffc000000

def z949 : W := mkw 0x12401fc249243b5d 0x412401fc249243b5 0x00001fc6c0003f04 0x100001fc6c0003f0

def z950 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe37fc6fffc3f0d 0xfbfe37fc6fffc3f0

def z951 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x7e3f1e3e3f1f3ccf 0xf7e3f1e3e3f1f3cc

def z952 : W := mkw 0x2617162e7b0334d3 0x42617162e7b0334d 0x6e1f1e3fff033cfe 0xf6e1f1e3fff033cf

def z953 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x0000180000003f00 0x10000180000003f0

def z954 : W := mkw 0x0200160009003000 0x0020016000900300 0x6e1c1e383f003c0e 0xf6e1c1e383f003c0

def z955 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfffe7c03fffc00f 0xebfffe7c03fffc00

def z956 : W := mkw 0x2617142e330314c3 0x02617142e330314c 0x2e1f183e27001c00 0x52e1f183e27001c0

def z957 : W := mkw 0x8dbfe00276dbc051 0x48dbfe00276dbc05 0xffffe107ffffe3ff 0xeffffe107ffffe3f

def z958 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcffffeffc0000002 0xdcffffeffc000000

def z959 : W := mkw 0x2617362e7b0b74d3 0x42617362e7b0b74d 0x7e3ffe3fff1ffcff 0xf7e3ffe3fff1ffcf

def z960 : W := mkw 0x0920000004900000 0x0092000000490000 0xbfc000003ffc0008 0x4bfc000003ffc000

def z961 : W := mkw 0x00012242580d6159 0x400012242580d615 0x7023ffc7f81fffff 0xf7023ffc7f81ffff

def z962 : W := mkw 0x849fe008324bc4a2 0x8849fe008324bc4a 0x001fe0000003c0f2 0x0001fe0000003c0f

def z963 : W := mkw 0xcdbfe011b6dbc000 0x0cdbfe011b6dbc00 0xbfffe001ffffc00b 0xebfffe001ffffc00

def z964 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1df9f3f20e3ffff 0xff1df9f3f20e3fff

def z965 : W := mkw 0x09ada00034dbc000 0x009ada00034dbc00 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z966 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfffe7ffc0000003 0x8cfffe7ffc000000

def z967 : W := mkw 0x8924000026d28000 0x08924000026d2800 0xbfe000003ffc0009 0xebfe000003ffc000

def z968 : W := mkw 0x56dadff589243b0c 0x056dadff589243b0 0x401fffffc0003f06 0x1401fffffc0003f0

def z969 : W := mkw 0x4ffaddb584b00a00 0x04ffaddb584b00a0 0xfffffffffffc3f0f 0xffffffffffffc3f0

def z970 : W := mkw 0x1b601fd10db43b0c 0x01b601fd10db43b0 0xffe01ff93ffc3f0d 0xfffe01ff93ffc3f0

def z971 : W := mkw 0xa617362e3b4bf4c3 0x0a617362e3b4bf4c 0x6e1f1e3e3f03fcce 0xf6e1f1e3e3f03fcc

def z972 : W := mkw 0x2617166e7b0735db 0x42617166e7b0735d 0x7e1f9fffff03ffff 0xf7e1f9fffff03fff

def z973 : W := mkw 0x72401fff89243fcf 0x072401fff89243fc 0x40001fffc0003fc4 0x140001fffc0003fc

def z974 : W := mkw 0x89a8c00004d08000 0x089a8c00004d0800 0xbfe000003ffc0009 0xebfe000003ffc000

def z975 : W := mkw 0x8dbbe00016994000 0x08dbbe0001699400 0xbfffe0003ffc000b 0xebfffe0003ffc000

def z976 : W := mkw 0x2617142e330314c3 0x02617142e330314c 0x6e1f183e27033cce 0x76e1f183e27033cc

def z977 : W := mkw 0x2617362e7b0b74d3 0x42617362e7b0b74d 0x6e1f1e3e3f03fcfe 0xf6e1f1e3e3f03fcf

def z978 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfffe0003fffe3fb 0xebfffe0003fffe3f

def z979 : W := mkw 0x2616162e2b0234c3 0x02616162e2b0234c 0x2e1c183827003cc0 0x52e1c183827003cc

def z980 : W := mkw 0x2d37002e369304c3 0x02d37002e369304c 0xffff003e3fff00cb 0xeffff003e3fff00c

def z981 : W := mkw 0x19e8a9d144fccb3c 0xc19e8a9d144fccb3 0x91e0e1c1c0fcc331 0x091e0e1c1c0fcc33

def z982 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1ffe3fff033cce 0xf6e1ffe3fff033cc

def z983 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbffce0003fffc009 0x4bffce0003fffc00

def z984 : W := mkw 0x12401fc809243f8e 0x012401fc809243f8 0x40001ff800003fc4 0x140001ff800003fc

def z985 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xdfffffffc000230f 0xfdfffffffc000230

def z986 : W := mkw 0x0d32000004900000 0x00d3200000490000 0xbfff00003ffc000b 0xebfff00003ffc000

def z987 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfffe1013fffc33b 0xebfffe1013fffc33

def z988 : W := mkw 0x5ffaddb584b00a04 0x05ffaddb584b00a0 0xcfffffffc0e00007 0xfcfffffffc0e0000

def z989 : W := mkw 0x12401fc049243b1c 0x412401fc049243b1 0x00001fc1c0003f34 0x100001fc1c0003f3

def z990 : W := mkw 0x0dbec00024d28000 0x00dbec00024d2800 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z991 : W := mkw 0x8dbfe00836dbc482 0x08dbfe00836dbc48 0xfffff9393fffffff 0xffffff9393ffffff

def z992 : W := mkw 0x0920000004900000 0x0092000000490000 0xafe000003ffc0000 0xcafe000003ffc000

def z993 : W := mkw 0x2617142c33031482 0x02617142c3303148 0x6e1f1e3e3f031c0e 0xf6e1f1e3e3f031c0

def z994 : W := mkw 0x0b601d8004b00a00 0x00b601d8004b00a0 0xbfe01fc03ffc3f0d 0xfbfe01fc03ffc3f0

def z995 : W := mkw 0x46521db580000000 0x046521db58000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z996 : W := mkw 0x4ffaddb580408000 0x04ffaddb58040800 0xdfffffffc0e0c007 0xfdfffffffc0e0c00

def z997 : W := mkw 0x2616162c2b023482 0x02616162c2b02348 0x2e1c1e383f001c00 0xd2e1c1e383f001c0

def z998 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xffffe7c7ffffe3ff 0xeffffe7c7ffffe3f

def z999 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfff60003fffc008 0xcbfff60003fffc00

def z1000 : W := mkw 0x0924000824920482 0x0092400082492048 0xfffc18383fff3ccf 0xffffc18383fff3cc

def z1001 : W := mkw 0x0d36000026920000 0x00d3600002692000 0xbffc00003ffc0009 0xebffc00003ffc000

def z1002 : W := mkw 0x0417224a7a0f65db 0x40417224a7a0f65d 0x7e3fffffff1fffff 0xf7e3fffffff1ffff

def z1003 : W := mkw 0x0b601f000db03a00 0x00b601f000db03a0 0xbfe01f003ffc3f0d 0xfbfe01f003ffc3f0

def z1004 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xafff60003fff000a 0xeafff60003fff000

def z1005 : W := mkw 0x8dbfe01936dbc4a2 0x88dbfe01936dbc4a 0xffffe1393fffe3ff 0xeffffe1393fffe3f

def z1006 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0x8fffffffc0000001 0xd8fffffffc000000

def z1007 : W := mkw 0x5ffaddb585901004 0x05ffaddb58590100 0xcfffffffc7000007 0xfcfffffffc700000

def z1008 : W := mkw 0x6ffaddb583001000 0x06ffaddb58300100 0xcfffffffc7000007 0xfcfffffffc700000

def z1009 : W := mkw 0x2617362e3b0b74c3 0x02617362e3b0b74c 0x6e1ffe3e3f03fcce 0xf6e1ffe3e3f03fcc

def z1010 : W := mkw 0xa49fe02e724bc4d3 0x4a49fe02e724bc4d 0x401fe03fc003c0f2 0x0401fe03fc003c0f

def z1011 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x7e1ffe3fff1ffffe 0xf7e1ffe3fff1ffff

def z1012 : W := mkw 0xadbfe02c36dbc482 0x0adbfe02c36dbc48 0xbfffe0383fffc00b 0xebfffe0383fffc00

def z1013 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0x8ffffefec0000003 0xf8ffffefec000000

def z1014 : W := mkw 0x09a8c00004900000 0x009a8c0000490000 0xbfe0e0003ffc0009 0xebfe0e0003ffc000

def z1015 : W := mkw 0x5b601ff58db43b0c 0x05b601ff58db43b0 0xffe3fffffffc3f0f 0xfffe3fffffffc3f0

def z1016 : W := mkw 0x8920200004d8c000 0x08920200004d8c00 0xbfe000003ffcc009 0xebfe000003ffcc00

def z1017 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x2e1f1e3e27001c00 0xd2e1f1e3e27001c0

def z1018 : W := mkw 0x2616142e230214c3 0x02616142e230214c 0x6e1c183e27001cc0 0x56e1c183e27001cc

def z1019 : W := mkw 0x09ac801924d284a2 0x809ac801924d284a 0xfffc80393fffc0fb 0xefffc80393fffc0f

def z1020 : W := mkw 0x0612142400000000 0x0061214240000000 0x4e3f7efec0000006 0xf4e3f7efec000000

def z1021 : W := mkw 0x0d33000016910000 0x00d3300001691000 0xbfe300003ffc0009 0xebfe300003ffc000

def z1022 : W := mkw 0x049fa000324bc000 0x0049fa000324bc00 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z1023 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfc01e003ffc3f0c 0xfbfc01e003ffc3f0

def z1024 : W := mkw 0x4f3254a480000000 0x04f3254a48000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z1025 : W := mkw 0x2616162c2b023482 0x02616162c2b02348 0x2e1c18383f003c08 0x52e1c18383f003c0

def z1026 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xcfffffffc003c0f7 0xfcfffffffc003c0f

def z1027 : W := mkw 0x32401fec09243f8e 0x032401fec09243f8 0x00001ff800003f04 0x100001ff800003f0

def z1028 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x7e1f1f3e3f033fcf 0xf7e1f1f3e3f033fc

def z1029 : W := mkw 0x2417002e320304c3 0x02417002e320304c 0x6e1f183e3f033cce 0xf6e1f183e3f033cc

def z1030 : W := mkw 0x89a9e00014d9c000 0x089a9e00014d9c00 0xbfe3e0003fffc00b 0xebfe3e0003fffc00

def z1031 : W := mkw 0x849fe008324bc482 0x0849fe008324bc48 0x401fe0380003c0c2 0x0401fe0380003c0c

def z1032 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1fc9ff920e3ffff 0xff1fc9ff920e3fff

def z1033 : W := mkw 0x2617362e7b0b74d3 0x42617362e7b0b74d 0x7e1fff3fff03ffff 0xf7e1fff3fff03fff

def z1034 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe01ec03ffc3f08 0xdbfe01ec03ffc3f0

def z1035 : W := mkw 0x00012242590d7159 0x400012242590d715 0x7023e7c7ff1fffff 0xa7023e7c7ff1ffff

def z1036 : W := mkw 0x0005224a784fe5fb 0xc0005224a784fe5f 0x10000000181fe3f8 0x010000000181fe3f

def z1037 : W := mkw 0x0001200010094000 0x0000120001009400 0x5023e7c7d81fe3ff 0xa5023e7c7d81fe3f

def z1038 : W := mkw 0x00012242580d6159 0x400012242580d615 0x4023e7c7d81fe3f6 0x84023e7c7d81fe3f

def z1039 : W := mkw 0x2617362e7b0b74d3 0x42617362e7b0b74d 0x6e3fffffff03fcff 0xf6e3fffffff03fcf

def z1040 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x6e1f1e3e27033cce 0xf6e1f1e3e27033cc

def z1041 : W := mkw 0x4ffaddb580608a20 0x84ffaddb580608a2 0xdfffffffc0e3e3ff 0xfdfffffffc0e3e3f

def z1042 : W := mkw 0x061716083b033482 0x0061716083b03348 0x6e1f1e383f033cce 0xf6e1f1e383f033cc

def z1043 : W := mkw 0x0005224a780f65db 0x40005224a780f65d 0x30000000381ffff8 0x030000000381ffff

def z1044 : W := mkw 0x4fbad4b580000000 0x04fbad4b58000000 0x0e3f66fec0000000 0x80e3f66fec000000

def z1045 : W := mkw 0x5f3376e6dd9d715d 0x45f3376e6dd9d715 0x0e2366c6df1c0000 0x80e2366c6df1c000

def z1046 : W := mkw 0x59e8e9d1c4bc4b1c 0x459e8e9d1c4bc4b1 0x91e0e1c1c0fcc331 0x091e0e1c1c0fcc33

def z1047 : W := mkw 0x12401fd909243fae 0x812401fd909243fa 0x00001ff800003f04 0x100001ff800003f0

def z1048 : W := mkw 0x0000000000000000 0x0000000000000000 0x403fffffc0000007 0xf403fffffc000000

def z1049 : W := mkw 0x8dbfe02436dbc000 0x08dbfe02436dbc00 0xffffe03e3fffc00b 0xeffffe03e3fffc00

def z1050 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe0ffc1fffc3f0d 0xfbfe0ffc1fffc3f0

def z1051 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xf1dc183820e3fffe 0x7f1dc183820e3fff

def z1052 : W := mkw 0x12401fdb49243fff 0xc12401fdb49243ff 0x40001fffc0003ff4 0x140001fffc0003ff

def z1053 : W := mkw 0x0204140821021482 0x0020414082102148 0x6e1c183827033cce 0x76e1c183827033cc

def z1054 : W := mkw 0x200122425b0d7159 0x4200122425b0d715 0x5023e7c7df1fe3ff 0xa5023e7c7df1fe3f

def z1055 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x2e1c183827031c0a 0x72e1c183827031c0

def z1056 : W := mkw 0x8dbfe00836dbc482 0x08dbfe00836dbc48 0xbffff8383fffdc0b 0xfbffff8383fffdc0

def z1057 : W := mkw 0x5ffaddb585b01a04 0x05ffaddb585b01a0 0xfffffffffffc1c0f 0xffffffffffffc1c0

def z1058 : W := mkw 0x0960090004b00a00 0x00960090004b00a0 0xbfe018003ffc1c09 0xfbfe018003ffc1c0

def z1059 : W := mkw 0x2616162c2b023482 0x02616162c2b02348 0x2e1c1e3827003c04 0x52e1c1e3827003c0

def z1060 : W := mkw 0x2617166e3b0735cb 0x02617166e3b0735c 0x7e1f1e3e3f1f3fce 0xf7e1f1e3e3f1f3fc

def z1061 : W := mkw 0x4f725db580000000 0x04f725db58000000 0x4e3f7fffc0000006 0xf4e3f7fffc000000

def z1062 : W := mkw 0x2005224a7a0f65db 0x42005224a7a0f65d 0x10000000181fe3f8 0x010000000181fe3f

def z1063 : W := mkw 0x00012242580d6159 0x400012242580d615 0x5023e7c7c01fe3f7 0x05023e7c7c01fe3f

def z1064 : W := mkw 0x0205160a390334c3 0x00205160a390334c 0x6e1f1e3e3f033cce 0xf6e1f1e3e3f033cc

def z1065 : W := mkw 0x2617166e3b0735cb 0x02617166e3b0735c 0x6e3f1efe3f1f3cce 0xf6e3f1efe3f1f3cc

def z1066 : W := mkw 0x0dbbe00014994000 0x00dbbe0001499400 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z1067 : W := mkw 0x1b2016c00d94310c 0x01b2016c00d94310 0xbfe01ec03ffc3c0d 0xfbfe01ec03ffc3c0

def z1068 : W := mkw 0x00012242580d6159 0x400012242580d615 0x7e23e7c7ff1fe3ff 0xe7e23e7c7ff1fe3f

def z1069 : W := mkw 0x0dbac00004900000 0x00dbac0000490000 0xbffc00003ffc0009 0xebffc00003ffc000

def z1070 : W := mkw 0x8dbfe01136dbc020 0x88dbfe01136dbc02 0xbfffe0013fffc03b 0xebfffe0013fffc03

def z1071 : W := mkw 0x4ffaddb580200a00 0x04ffaddb580200a0 0xdfffffffc0e00307 0xfdfffffffc0e0030

def z1072 : W := mkw 0xadbfe02636dbc041 0x0adbfe02636dbc04 0xbfffe0063fffc00b 0xebfffe0063fffc00

def z1073 : W := mkw 0xc49fe03db24bc4a2 0x8c49fe03db24bc4a 0x401fe03fc003c0f2 0x0401fe03fc003c0f

def z1074 : W := mkw 0xc9e8e99184f8ca20 0x8c9e8e99184f8ca2 0x91e0e1c1c0fcc331 0x091e0e1c1c0fcc33

def z1075 : W := mkw 0x8dbfe01936dbc4a2 0x88dbfe01936dbc4a 0xfffff8393ffffcff 0xffffff8393ffffcf

def z1076 : W := mkw 0x2617142e330314c3 0x02617142e330314c 0x2e1c183827031cc0 0x52e1c183827031cc

def z1077 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x6e3ffeffff1ffcfe 0xf6e3ffeffff1ffcf

def z1078 : W := mkw 0x8d37600036dbc000 0x08d37600036dbc00 0xbfe360003fffc009 0xebfe360003fffc00

def z1079 : W := mkw 0xadbfe02e36dbc4c3 0x0adbfe02e36dbc4c 0xfffff83e3ffffccf 0xffffff83e3ffffcc

def z1080 : W := mkw 0x8d33600016994000 0x08d3360001699400 0xbfe3e0003fffc00b 0xebfe3e0003fffc00

def z1081 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xffffe007ffffc00b 0xeffffe007ffffc00

def z1082 : W := mkw 0xcffaddb584d08000 0x0cffaddb584d0800 0xcfffffffc0e00007 0xfcfffffffc0e0000

def z1083 : W := mkw 0x09a8800004900000 0x009a880000490000 0xbffc80003ffc000b 0xebffc80003ffc000

def z1084 : W := mkw 0x0920000004b00a00 0x00920000004b00a0 0xbfe000003ffc3f09 0xebfe000003ffc3f0

def z1085 : W := mkw 0x42c89db580000000 0x042c89db58000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z1086 : W := mkw 0x12401fd109243b0c 0x012401fd109243b0 0x40001ff900003f04 0x140001ff900003f0

def z1087 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xffffe0013fffc0fb 0xeffffe0013fffc0f

def z1088 : W := mkw 0x1b601d8005b01a04 0x01b601d8005b01a0 0xbfe01fc03ffc1c0d 0xfbfe01fc03ffc1c0

def z1089 : W := mkw 0x32401fff09243fef 0x832401fff09243fe 0x40001fff00003ff4 0x140001fff00003ff

def z1090 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x2e1f1e3e3f031c0a 0xf2e1f1e3e3f031c0

def z1091 : W := mkw 0x849fe01b724bc4f3 0xc849fe01b724bc4f 0x401fe03fc003c0f2 0x0401fe03fc003c0f

def z1092 : W := mkw 0x89e9eb535cfdeb79 0xc89e9eb535cfdeb7 0xd1e3e7c7d8ffe3ff 0xad1e3e7c7d8ffe3f

def z1093 : W := mkw 0x0dbf800036d38000 0x00dbf800036d3800 0xbfff80003fffc00b 0xebfff80003fffc00

def z1094 : W := mkw 0x0924000024d28000 0x00924000024d2800 0xbfe000003fffc009 0xebfe000003fffc00

def z1095 : W := mkw 0x0921200254994051 0x4092120025499405 0xffe3e007ffffc0fb 0xeffe3e007ffffc0f

def z1096 : W := mkw 0x1b601fc20db43b4d 0x01b601fc20db43b4 0xffe01fc63ffc3fcd 0xfffe01fc63ffc3fc

def z1097 : W := mkw 0x09600b400cb42b08 0x009600b400cb42b0 0xbfe01fc03ffc3f0d 0xfbfe01fc03ffc3f0

def z1098 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xdfffffffc003c00f 0xfdfffffffc003c00

def z1099 : W := mkw 0x8dbfe00276dbc051 0x48dbfe00276dbc05 0xbfffe006ffffc00b 0xebfffe006ffffc00

def z1100 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x2e1c1e3827001c04 0xf2e1c1e3827001c0

def z1101 : W := mkw 0xa49fe00a324bc4c3 0x0a49fe00a324bc4c 0x001fe0000003c0c2 0x0001fe0000003c0c

def z1102 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e3f1ffe3f033ccf 0xf6e3f1ffe3f033cc

def z1103 : W := mkw 0x59e8c9d184f48b2c 0x859e8c9d184f48b2 0x91e0e1c1c0fcc331 0x091e0e1c1c0fcc33

def z1104 : W := mkw 0x4ffaddb580608a20 0x84ffaddb580608a2 0xcfffffffc0e00007 0xfcfffffffc0e0000

def z1105 : W := mkw 0x2617166e7b0735db 0x42617166e7b0735d 0x7e3f1fffff1f3fff 0xf7e3f1fffff1f3ff

def z1106 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x6e1c1e3e27001c04 0x56e1c1e3e27001c0

def z1107 : W := mkw 0x249fa03f724bc4f3 0xc249fa03f724bc4f 0x401fe03fc003c0f2 0x0401fe03fc003c0f

def z1108 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e3ffe3e3f033ccf 0xf6e3ffe3e3f033cc

def z1109 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x6e1f1e3e3f1f3cce 0xf6e1f1e3e3f1f3cc

def z1110 : W := mkw 0x0be89d9100000000 0x00be89d910000000 0xcfffffffc0000007 0xfcfffffffc000000

def z1111 : W := mkw 0x1b601d8005b01a04 0x01b601d8005b01a0 0xafe018003ffc1c00 0xdafe018003ffc1c0

def z1112 : W := mkw 0x0920000004900000 0x0092000000490000 0xffe081013fffe3ff 0xeffe081013fffe3f

def z1113 : W := mkw 0x0416000822020482 0x0041600082202048 0x6e1c183827033cce 0x76e1c183827033cc

def z1114 : W := mkw 0x00012242580d6159 0x400012242580d615 0x1023e7c7d81fe3f9 0x81023e7c7d81fe3f

def z1115 : W := mkw 0x361716ee3b0735cf 0x0361716ee3b0735c 0x6e1f1efe3f033cce 0xf6e1f1efe3f033cc

def z1116 : W := mkw 0x19e8899104f08a24 0x819e8899104f08a2 0x81c0000000e00000 0x081c0000000e0000

def z1117 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xffdc99393fe3ffff 0xfffdc99393fe3fff

def z1118 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xffe31fc63ffc3f0f 0xfffe31fc63ffc3f0

def z1119 : W := mkw 0x2617142c33031482 0x02617142c3303148 0x2e1c18383f031c08 0x52e1c18383f031c0

def z1120 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x7e3f1ffe3f1fffff 0xf7e3f1ffe3f1ffff

def z1121 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xffe01fc13ffc3ffd 0xfffe01fc13ffc3ff

def z1122 : W := mkw 0x8dbec00026d28000 0x08dbec00026d2800 0xbfdc00003ffc0008 0x4bfdc00003ffc000

def z1123 : W := mkw 0x0412002400000000 0x0041200240000000 0x403fe7ffc0000007 0xa403fe7ffc000000

def z1124 : W := mkw 0x2617166e3b0735cb 0x02617166e3b0735c 0x7e3fffffff1f3fcf 0xf7e3fffffff1f3fc

def z1125 : W := mkw 0x1005224a7dffffff 0xc1005224a7dfffff 0x300000003ffffff8 0x0300000003ffffff

def z1126 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x2e1c183827003c0c 0x72e1c183827003c0

def z1127 : W := mkw 0x4ffaddb580408020 0x84ffaddb58040802 0xcfffffffc000c037 0xfcfffffffc000c03

def z1128 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xffffe6063fffc00f 0xeffffe6063fffc00

def z1129 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xefffffffff00000f 0xfefffffffff00000

def z1130 : W := mkw 0x36571fee3b273fcf 0x036571fee3b273fc 0x401f1ffe00033fc6 0x1401f1ffe00033fc

def z1131 : W := mkw 0x0417020a3a0324c3 0x00417020a3a0324c 0x6e1f1e3e3f033cce 0xf6e1f1e3e3f033cc

def z1132 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfffe6c6ffffc00b 0xebfffe6c6ffffc00

def z1133 : W := mkw 0x2617362e3b0b74c3 0x02617362e3b0b74c 0x6e3f7e3e3f1f3cce 0xf6e3f7e3e3f1f3cc

def z1134 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xafc018003ffc1c00 0x5afc018003ffc1c0

def z1135 : W := mkw 0x19600bc00db43b0c 0x019600bc00db43b0 0xbfe001c03ffc3f09 0xebfe001c03ffc3f0

def z1136 : W := mkw 0x8dbfe01136dbc000 0x08dbfe01136dbc00 0xffffe0393fffc00b 0xeffffe0393fffc00

def z1137 : W := mkw 0x52401fe489243b0c 0x052401fe489243b0 0x00001fc6c0003f04 0x100001fc6c0003f0

def z1138 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbffc00003fffc009 0xebffc00003fffc00

def z1139 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xafe01fc03ffc3f04 0xdafe01fc03ffc3f0

def z1140 : W := mkw 0x0204160829023482 0x0020416082902348 0x2e1c1e383f003c0c 0xf2e1c1e383f003c0

def z1141 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xb1dc193820e3fffd 0x7b1dc193820e3fff

def z1142 : W := mkw 0x89e8c91104f08a20 0x889e8c91104f08a2 0x91c0810100e0c331 0x091c0810100e0c33

def z1143 : W := mkw 0x8dbfe01936dbc4a2 0x88dbfe01936dbc4a 0xbfffe0383fffc00b 0xebfffe0383fffc00

def z1144 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe01fc03ffffffd 0xfbfe01fc03ffffff

def z1145 : W := mkw 0x89e8e95144fccb38 0xc89e8e95144fccb3 0x91e0e1c1c0fcc331 0x091e0e1c1c0fcc33

def z1146 : W := mkw 0x8925200036dbc000 0x08925200036dbc00 0xbfe3e0003fffc00b 0xebfe3e0003fffc00

def z1147 : W := mkw 0x2617366e3b0f75cb 0x02617366e3b0f75c 0x7e3ffffe3f1fffcf 0xf7e3ffffe3f1fffc

def z1148 : W := mkw 0x0920000004900000 0x0092000000490000 0xbfe007c03ffc000d 0xebfe007c03ffc000

def z1149 : W := mkw 0x8dbfe00836dbc482 0x08dbfe00836dbc48 0xffffe0383fffc0cb 0xeffffe0383fffc0c

def z1150 : W := mkw 0x59e8c9d184b40b0c 0x059e8c9d184b40b0 0x91e001c000fc0301 0x091e001c000fc030

def z1151 : W := mkw 0x0b601f800d903000 0x00b601f800d90300 0xbfe01fc03ffc3c0d 0xfbfe01fc03ffc3c0

def z1152 : W := mkw 0xcdbfe03db6dbc4a2 0x8cdbfe03db6dbc4a 0xffffe03fffffc0fb 0xeffffe03fffffc0f

def z1153 : W := mkw 0xe49fe03fb24bc4c3 0x0e49fe03fb24bc4c 0x401fe03fc003c0c2 0x0401fe03fc003c0c

def z1154 : W := mkw 0x8dbfe00836dbc4a2 0x88dbfe00836dbc4a 0xbfffe0003fffc0fb 0xebfffe0003fffc0f

def z1155 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x2e1f1e3e3f003c0c 0xf2e1f1e3e3f003c0

def z1156 : W := mkw 0xcdbfe037f6dbc051 0x4cdbfe037f6dbc05 0xffffe03fffffc0fb 0xeffffe03fffffc0f

def z1157 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xfffc1ff83ffc3f0f 0xffffc1ff83ffc3f0

def z1158 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xafe01ec03ffc3c0c 0xfafe01ec03ffc3c0

def z1159 : W := mkw 0x4fbad4b580000000 0x04fbad4b58000000 0x4e3ffeffc0000006 0xf4e3ffeffc000000

def z1160 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x6e3fffffff1f3ccf 0xf6e3fffffff1f3cc

def z1161 : W := mkw 0x5b601fd18db43b0c 0x05b601fd18db43b0 0xbfe01fc1fffc3f0d 0xfbfe01fc1fffc3f0

def z1162 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe09fc03fffff0f 0xfbfe09fc03fffff0

def z1163 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x2e1c183827033cc8 0x52e1c183827033cc

def z1164 : W := mkw 0x8dbfe00276dbc051 0x48dbfe00276dbc05 0xbfffe0003fffc0fb 0xebfffe0003fffc0f

def z1165 : W := mkw 0x46daddb580000000 0x046daddb58000000 0x403fffffc0000007 0xb403fffffc000000

def z1166 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xdfffffffc000c337 0xfdfffffffc000c33

def z1167 : W := mkw 0x4fbad4b580000000 0x04fbad4b58000000 0x4e3fe7ffc0000007 0xa4e3fe7ffc000000

def z1168 : W := mkw 0x59e8cbd18cb42b0c 0x059e8cbd18cb42b0 0xd1e3e7c7d8fc230f 0xad1e3e7c7d8fc230

def z1169 : W := mkw 0x0921200014994000 0x0092120001499400 0xbfe000003fffc009 0xebfe000003fffc00

def z1170 : W := mkw 0x8005224a7effeffb 0xc8005224a7effeff 0x300000003ffffff8 0x0300000003ffffff

def z1171 : W := mkw 0x1920000005b01a04 0x01920000005b01a0 0xbfe000003ffc1c09 0xebfe000003ffc1c0

def z1172 : W := mkw 0x092002000d903000 0x0092002000d90300 0xbfe000003ffc3c09 0xebfe000003ffc3c0

def z1173 : W := mkw 0x1b601f800db03a04 0x01b601f800db03a0 0xbfe01e003ffc3c0d 0xfbfe01e003ffc3c0

def z1174 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x7e1c99392703ffff 0x77e1c99392703fff

def z1175 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfc019003ffc3f0d 0x7bfc019003ffc3f0

def z1176 : W := mkw 0x1b601fc24db43b5d 0x41b601fc24db43b5 0xffe09fc7ffffffff 0xfffe09fc7fffffff

def z1177 : W := mkw 0x0088801100000000 0x0008880110000000 0x403fe7ffc0000007 0xa403fe7ffc000000

def z1178 : W := mkw 0x8dbfe00276dbc051 0x48dbfe00276dbc05 0xffffe7c7ffffc0ff 0xeffffe7c7ffffc0f

def z1179 : W := mkw 0x5b601ff58db43b0c 0x05b601ff58db43b0 0xbfe01ff83ffc3f0d 0xfbfe01ff83ffc3f0

def z1180 : W := mkw 0x0616162c29023482 0x00616162c2902348 0x6e1f1e3e3f033cce 0xf6e1f1e3e3f033cc

def z1181 : W := mkw 0x12441fc829263f8e 0x012441fc829263f8 0x601c1ff820033fce 0x7601c1ff820033fc

def z1182 : W := mkw 0x49e8c99180000000 0x049e8c9918000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z1183 : W := mkw 0x0612142401001000 0x0061214240100100 0x2e1c183827001c00 0x52e1c183827001c0

def z1184 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xefffffffe0003c0f 0xfefffffffe0003c0

def z1185 : W := mkw 0x52401ff589243b0c 0x052401ff589243b0 0x00001ff800003f04 0x100001ff800003f0

def z1186 : W := mkw 0x40ccc919a0628ea2 0x840ccc919a0628ea 0xf1dcf939e0e3ffff 0x7f1dcf939e0e3fff

def z1187 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x7e3ffefeff1ffccf 0xf7e3ffefeff1ffcc

def z1188 : W := mkw 0x2417020a3b0334c3 0x02417020a3b0334c 0x6e1f18383f033cce 0xf6e1f18383f033cc

def z1189 : W := mkw 0x2617166e7b0735db 0x42617166e7b0735d 0x6e1f1e3e3f033ffe 0xf6e1f1e3e3f033ff

def z1190 : W := mkw 0x40cc8999a0628ea2 0x840cc8999a0628ea 0xf1dc99f9e0e3ffff 0x7f1dc99f9e0e3fff

def z1191 : W := mkw 0x4f725da480000000 0x04f725da48000000 0xcfff7ffec0000007 0xfcfff7ffec000000

def z1192 : W := mkw 0x020416482906358a 0x0020416482906358 0x7e3c9ff93f1fffff 0xf7e3c9ff93f1ffff

def z1193 : W := mkw 0x0920200004984000 0x0092020000498400 0xbfe0e0003ffcc009 0xebfe0e0003ffcc00

def z1194 : W := mkw 0x4dfac9b580000000 0x04dfac9b58000000 0xc1ffe7ffc0000007 0xac1ffe7ffc000000

def z1195 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x7e3ffe3e3f1fffff 0xf7e3ffe3e3f1ffff

def z1196 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x2e1f1e3e3f033cc8 0xd2e1f1e3e3f033cc

def z1197 : W := mkw 0x0dfac91100000000 0x00dfac9110000000 0xcfffffffc0000007 0xfcfffffffc000000

def z1198 : W := mkw 0x4ffaddb580000000 0x04ffaddb58000000 0xffffffffe0e0000f 0xfffffffffe0e0000

def z1199 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x2e1f183827001c02 0xf2e1f183827001c0

def z1200 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x3e1c18383f1ffff8 0x53e1c18383f1ffff

def z1201 : W := mkw 0x19e9abd35cfdeb7d 0xc19e9abd35cfdeb7 0xd1e3e7c7d8ffe3ff 0xad1e3e7c7d8ffe3f

def z1202 : W := mkw 0x12401fc809243fae 0x812401fc809243fa 0x00001fc000003ff4 0x100001fc000003ff

def z1203 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xafdc00003ffc0000 0x4afdc00003ffc000

def z1204 : W := mkw 0x89ada00036dbc000 0x089ada00036dbc00 0xbffc80003fffc00b 0xebffc80003fffc00

def z1205 : W := mkw 0x59e8c99184b00a04 0x059e8c99184b00a0 0x81c0000000e00000 0x081c0000000e0000

def z1206 : W := mkw 0x192002400db43b0c 0x0192002400db43b0 0xbfe007c03ffc3f0d 0xebfe007c03ffc3f0

def z1207 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x6e1f183e27001c02 0x56e1f183e27001c0

def z1208 : W := mkw 0xd9e8e9d184fccb0c 0x0d9e8e9d184fccb0 0x91e0e1c1c0fcc301 0x091e0e1c1c0fcc30

def z1209 : W := mkw 0x12401fc209243b4d 0x012401fc209243b4 0x40001fc600003fc4 0x140001fc600003fc

def z1210 : W := mkw 0x2617366e7b0f75db 0x42617366e7b0f75d 0x6e3f7fffff1f3ffe 0xf6e3f7fffff1f3ff

def z1211 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e3f7efeff033cce 0xf6e3f7efeff033cc

def z1212 : W := mkw 0x4ffaddb580200a20 0x84ffaddb580200a2 0xcfffffffc0000337 0xfcfffffffc000033

def z1213 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x00201fc000003f05 0xb00201fc000003f0

def z1214 : W := mkw 0x8dbec00026d28000 0x08dbec00026d2800 0xaffc00003ffc0000 0xcaffc00003ffc000

def z1215 : W := mkw 0x00cc891920628ea2 0x800cc891920628ea 0xd1dc993900e3fff7 0x1d1dc993900e3fff

def z1216 : W := mkw 0x2617142c33031482 0x02617142c3303148 0x6e1f18383f033cce 0xf6e1f18383f033cc

def z1217 : W := mkw 0x52401fd189243b0c 0x052401fd189243b0 0x00001fc1c0003f04 0x100001fc1c0003f0

def z1218 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xffe09fc13ffc3f0f 0xfffe09fc13ffc3f0

def z1219 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x6e1c183827001c06 0x76e1c183827001c0

def z1220 : W := mkw 0x2616162e2b0234c3 0x02616162e2b0234c 0x6e1c1e3e3f003ccc 0xf6e1c1e3e3f003cc

def z1221 : W := mkw 0x2616162e2b0234c3 0x02616162e2b0234c 0x6e1c1e3e27033cce 0x76e1c1e3e27033cc

def z1222 : W := mkw 0x5b605fc08db43b0c 0x05b605fc08db43b0 0xbfe07fc0fffc3f0d 0xfbfe07fc0fffc3f0

def z1223 : W := mkw 0x32401fca09243fcf 0x032401fca09243fc 0x00001fc000003fc4 0x100001fc000003fc

def z1224 : W := mkw 0x4fbad4a480000000 0x04fbad4a48000000 0xcffffefec0000007 0xfcffffefec000000

def z1225 : W := mkw 0x8dbec00026d28000 0x08dbec00026d2800 0xbfffe0003ffc000b 0xebfffe0003ffc000

def z1226 : W := mkw 0x1b601d8005b01a04 0x01b601d8005b01a0 0xbfe019003ffc3f0d 0xfbfe019003ffc3f0

def z1227 : W := mkw 0x09a8800004d08000 0x009a8800004d0800 0xbfe080003ffcc009 0xebfe080003ffcc00

def z1228 : W := mkw 0x2617162e3b0334c3 0x02617162e3b0334c 0x6e1f9e3f3f03fcfe 0xf6e1f9e3f3f03fcf

def z1229 : W := mkw 0x6617562ebb0334c3 0x06617562ebb0334c 0x6e1f7e3eff033cce 0xf6e1f7e3eff033cc

def z1230 : W := mkw 0x1b2016c00db43b0c 0x01b2016c00db43b0 0xbfe006c03ffc3f09 0xebfe006c03ffc3f0

def z1231 : W := mkw 0x8921200016994000 0x0892120001699400 0xbfe000003ffc0009 0xebfe000003ffc000

def z1232 : W := mkw 0x8dbfe00236dbc041 0x08dbfe00236dbc04 0xffffe0063fffc0cb 0xeffffe0063fffc0c

def z1233 : W := mkw 0x2616166e6b0635db 0x42616166e6b0635d 0x6e1c1fffe7003ff4 0x56e1c1fffe7003ff

def z1234 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xfffff8383fffc00f 0xffffff8383fffc00

def z1235 : W := mkw 0xedbfe03fb6dbc4c3 0x0edbfe03fb6dbc4c 0xffffe03fffffc0cb 0xeffffe03fffffc0c

def z1236 : W := mkw 0x8dbfe00836dbc482 0x08dbfe00836dbc48 0xbfffe0003ffffccb 0xebfffe0003ffffcc

def z1237 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x40001fc100003ff4 0x140001fc100003ff

def z1238 : W := mkw 0x89e8e91104f8ca20 0x889e8e91104f8ca2 0x91e0e00000fcc001 0x091e0e00000fcc00

def z1239 : W := mkw 0x19e889d104b40b0c 0x019e889d104b40b0 0x91e081c100fc0301 0x091e081c100fc030

def z1240 : W := mkw 0xadbfe00a36dbc4c3 0x0adbfe00a36dbc4c 0xbfffe0003fffc0cb 0xebfffe0003fffc0c

def z1241 : W := mkw 0x00c8891100200a00 0x000c8891100200a0 0xf1dc993920e3ffff 0x7f1dc993920e3fff

def z1242 : W := mkw 0x8dbfe00036dbc000 0x08dbfe00036dbc00 0xbfffe1003fffe30f 0xebfffe1003fffe30

def z1243 : W := mkw 0x2617362e7b0b74d3 0x42617362e7b0b74d 0x6e1f7e3eff033cce 0xf6e1f7e3eff033cc

def z1244 : W := mkw 0x2617166e7b0735db 0x42617166e7b0735d 0x6e3fffffff033fff 0xf6e3fffffff033ff

def z1245 : W := mkw 0x2617166e7b0735db 0x42617166e7b0735d 0x6e1f1efeff033cce 0xf6e1f1efeff033cc

def z1246 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe019c03ffc3f09 0x5bfe019c03ffc3f0

def z1247 : W := mkw 0x1b601fd10db43b2c 0x81b601fd10db43b2 0xbfe01fc13ffc3f3d 0xfbfe01fc13ffc3f3

def z1248 : W := mkw 0x1b601fc00db43b0c 0x01b601fc00db43b0 0xbfe01fc03ffc1f01 0xdbfe01fc03ffc1f0

def z1249 : W := mkw 0x2616142c23021482 0x02616142c2302148 0x6e1c183827031cc2 0x56e1c183827031cc

def z1250 : W := mkw 0x0920000004900000 0x0092000000490000 0x9fe000001ffc0001 0x89fe000001ffc000

def z1251 : W := mkw 0x1b601fc24db43b5d 0x41b601fc24db43b5 0xbfe01fc03ffc3ffd 0xfbfe01fc03ffc3ff

def z1252 : W := mkw 0x2617142c33031482 0x02617142c3303148 0x2e1f18383f001c00 0xd2e1f18383f001c0

def z1253 : W := mkw 0x1b601dc005b41b0c 0x01b601dc005b41b0 0xbfe019c03ffc1f09 0xfbfe019c03ffc1f0

def z1254 : W := mkw 0x12cc9fd92966bfae 0x812cc9fd92966bfa 0x401c9ff90003fff6 0x1401c9ff90003fff

def z1255 : W := mkw 0x89ade00036dbc000 0x089ade00036dbc00 0xbfe0e0003fffc009 0xebfe0e0003fffc00

def z1256 : W := mkw 0x2617142c33031482 0x02617142c3303148 0x2e1f183827031c02 0x52e1f183827031c0

def z1257 : W := mkw 0x12401fc009243b0c 0x012401fc009243b0 0x50009fc10003ffff 0x350009fc10003fff

def z1258 : W := mkw 0xa49fe03f324bc4e3 0x8a49fe03f324bc4e 0x401fe03f0003c0f2 0x0401fe03f0003c0f

def z1259 : W := mkw 0x2616162e2b0234c3 0x02616162e2b0234c 0x2e1c1e3e27001c00 0x52e1c1e3e27001c0

def z1260 : W := mkw 0x4ffaddb580200a00 0x04ffaddb580200a0 0xffffffffe0e3ffff 0xfffffffffe0e3fff

def z1261 : W := mkw 0x5b601fe48db43b0c 0x05b601fe48db43b0 0xbfe01fc6fffc3f0d 0xfbfe01fc6fffc3f0

def z1262 : W := mkw 0x8dbae00004d8c000 0x08dbae00004d8c00 0xbfffe0003ffcc00b 0xebfffe0003ffcc00

def z1263 : W := mkw 0x8dbbe00016d9c000 0x08dbbe00016d9c00 0xbfe3e0003ffcc009 0xebfe3e0003ffcc00

def z1264 : W := mkw 0x1b601fe40db43b0c 0x01b601fe40db43b0 0xffe01ffe3ffc3f0d 0xfffe01ffe3ffc3f0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z8,z4,z6]),(0,[z7,z0,z1,z2,z4,z9,z6])],[(0,[z7,z0,z1,z10,z2,z4,z6]),(0,[z7,z11,z0,z12,z1,z2,z6]),(0,[z7,z0,z1,z2,z13,z4,z6]),(1,[z7,z0,z1,z4,z14,z6]),(0,[z7,z0,z15,z1,z2,z4,z6])],[(0,[z7,z0,z16,z1,z2,z4,z6]),(0,[z7,z0,z17,z18,z1,z2,z4]),(0,[z7,z0,z1,z19,z20,z4,z6]),(0,[z7,z0,z21,z1,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z22]),(0,[z7,z0,z1,z2,z4,z23,z6])],[(0,[z24,z7,z0,z1,z2,z4,z6]),(1,[z7,z0,z25,z2,z4,z6]),(0,[z7,z0,z1,z26,z2,z4,z6]),(0,[z7,z0,z27,z2,z20,z4,z6]),(0,[z7,z0,z17,z28,z1,z2,z4]),(1,[z7,z0,z17,z2,z4,z29]),(0,[z7,z0,z1,z30,z2,z22,z6])],[(0,[z31,z7,z0,z1,z2,z4,z6]),(1,[z7,z0,z1,z2,z4,z32]),(0,[z7,z0,z1,z2,z4,z33,z6]),(0,[z34,z7,z0,z1,z2,z35,z6]),(1,[z7,z0,z1,z2,z4,z36]),(0,[z7,z0,z1,z2,z4,z37,z6]),(0,[z7,z0,z1,z2,z4,z38,z6])],[(0,[z7,z0,z1,z19,z39,z4,z6]),(0,[z7,z40,z0,z1,z2,z4,z6]),(1,[z7,z0,z41,z20,z4,z6]),(1,[z7,z0,z1,z2,z4,z42])],[(1,[z7,z0,z1,z2,z4,z43]),(0,[z7,z0,z1,z2,z44,z4,z6]),(0,[z45,z7,z0,z1,z2,z5,z6]),(0,[z7,z0,z1,z2,z4,z46,z6]),(0,[z7,z0,z1,z2,z4,z47,z6]),(0,[z7,z48,z1,z49,z2,z4,z6])],[(0,[z50,z7,z0,z51,z1,z2,z4]),(0,[z52,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z53,z1,z19,z4,z6]),(0,[z7,z0,z54,z1,z2,z4,z6]),(0,[z55,z7,z0,z1,z2,z4,z6]),(0,[z7,z48,z0,z56,z1,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z57]),(0,[z7,z0,z17,z1,z1,z2,z4])]],
   [[(0,[z7,z0,z1,z19,z58,z4,z6]),(0,[z7,z0,z1,z2,z4,z59,z60]),(0,[z7,z61,z0,z62,z2,z4,z6]),(0,[z7,z63,z0,z1,z2,z4,z6]),(1,[z7,z0,z17,z1,z2,z64])],[(0,[z65,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z19,z4,z66,z6]),(0,[z7,z0,z1,z2,z4,z67,z68]),(0,[z7,z0,z1,z2,z4,z69,z6]),(0,[z7,z0,z1,z2,z70,z4,z6]),(0,[z7,z0,z1,z2,z4,z71,z6]),(0,[z7,z0,z17,z1,z2,z4,z35]),(0,[z72,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z73,z17,z1,z2,z4]),(0,[z7,z0,z17,z1,z2,z64,z6]),(0,[z7,z0,z51,z1,z2,z4,z29])],[(0,[z7,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z74,z4,z6]),(0,[z75,z7,z0,z76,z2,z4,z6]),(0,[z7,z0,z1,z77,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z78,z6]),(0,[z7,z0,z79,z1,z2,z4,z35])],[(0,[z7,z0,z18,z1,z2,z80,z6]),(0,[z34,z7,z0,z81,z2,z4,z6]),(0,[z34,z7,z0,z1,z2,z5,z6]),(0,[z7,z0,z17,z1,z2,z4,z5]),(0,[z7,z0,z1,z2,z4,z82,z6]),(0,[z7,z83,z0,z1,z2,z4,z6])],[(0,[z84,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z85,z4,z6])],[(0,[z7,z0,z86,z1,z19,z4,z6]),(1,[z7,z0,z53,z1,z2,z6]),(0,[z7,z0,z87,z1,z88,z4,z6]),(0,[z89,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z6]),(0,[z7,z90,z0,z17,z2,z4,z6]),(0,[z7,z0,z1,z91,z2,z4,z6]),(0,[z7,z0,z92,z1,z2,z4,z6])],[(0,[z7,z0,z1,z2,z4,z93,z6]),(0,[z7,z0,z17,z1,z2,z3,z4]),(0,[z7,z0,z1,z2,z4,z6,z94]),(0,[z7,z0,z1,z2,z4,z6,z95]),(0,[z7,z0,z96,z1,z30,z4,z6])],[(0,[z7,z0,z1,z19,z97,z4,z6]),(0,[z7,z98,z0,z1,z88,z4,z6]),(0,[z7,z0,z1,z99,z2,z4,z6]),(1,[z7,z0,z1,z100,z4,z6]),(0,[z101,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z102,z6]),(0,[z103,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z41,z51,z1,z2,z4]),(0,[z7,z0,z104,z17,z1,z2,z4]),(1,[z7,z0,z105,z2,z4,z6])]],
   [[(1,[z7,z106,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z107])],[(0,[z7,z0,z1,z108,z2,z4,z6]),(0,[z7,z0,z109,z1,z2,z4,z6]),(0,[z7,z61,z90,z1,z2,z4,z6])],[(0,[z34,z7,z0,z1,z2,z4,z33]),(0,[z7,z0,z1,z2,z4,z110,z6]),(0,[z7,z0,z1,z2,z4,z111,z6]),(0,[z7,z0,z1,z2,z112,z4,z6])],[(0,[z7,z0,z1,z113,z2,z4,z6]),(0,[z7,z61,z0,z1,z19,z4,z6]),(0,[z7,z0,z28,z1,z88,z4,z6]),(0,[z7,z114,z0,z1,z2,z4,z6]),(0,[z7,z90,z0,z26,z2,z4,z6]),(1,[z7,z0,z1,z2,z4,z115]),(0,[z7,z0,z1,z2,z4,z116,z6])],[(0,[z7,z0,z1,z88,z4,z22,z6]),(0,[z7,z48,z0,z1,z2,z117,z6])],[(0,[z7,z48,z0,z1,z19,z4,z6]),(0,[z7,z0,z118,z1,z2,z4,z6]),(0,[z7,z0,z51,z51,z1,z2,z4]),(0,[z7,z0,z51,z1,z2,z39,z4])],[(0,[z52,z7,z0,z1,z119,z4,z6]),(0,[z7,z0,z120,z1,z2,z4,z6]),(0,[z7,z0,z121,z1,z19,z4,z6]),(0,[z7,z0,z122,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z123]),(0,[z7,z0,z1,z2,z4,z6,z124]),(0,[z7,z0,z1,z2,z4,z125,z6])],[(0,[z7,z126,z127,z1,z2,z4,z6]),(0,[z7,z0,z17,z1,z26,z2,z4]),(0,[z128,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z129]),(0,[z7,z0,z130,z1,z2,z4,z6]),(0,[z7,z0,z131,z51,z1,z2,z4])]],
   [[(0,[z0,z18,z1,z132,z2,z4,z6]),(0,[z7,z0,z18,z1,z19,z4,z6]),(0,[z7,z0,z1,z19,z4,z60,z6]),(0,[z7,z0,z1,z2,z4,z6,z133]),(0,[z7,z0,z1,z2,z4,z4,z6])],[(0,[z7,z134,z0,z1,z19,z4,z6]),(0,[z34,z0,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z135,z4,z6])],[(0,[z136,z7,z0,z1,z2,z4,z6]),(0,[z84,z7,z0,z1,z88,z4,z6]),(0,[z137,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z1,z88,z4,z67,z6]),(0,[z34,z7,z138,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z36]),(0,[z7,z0,z51,z56,z1,z2,z4]),(0,[z7,z0,z28,z1,z2,z35,z6]),(0,[z7,z0,z139,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z140])],[(0,[z7,z0,z1,z2,z4,z141,z6]),(0,[z7,z0,z1,z142,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z143]),(0,[z144,z7,z0,z1,z2,z4,z6])],[(0,[z7,z0,z17,z1,z19,z4,z6]),(0,[z7,z0,z145,z1,z2,z4,z6]),(0,[z7,z0,z17,z2,z4,z35,z6]),(0,[z7,z0,z1,z2,z146,z4,z6])],[(0,[z7,z1,z49,z2,z147,z4,z6]),(0,[z7,z0,z1,z4,z14,z6,z148]),(1,[z7,z0,z41,z17,z2,z4]),(1,[z7,z0,z17,z1,z2,z4])],[(0,[z7,z0,z51,z18,z1,z2,z4]),(0,[z7,z149,z0,z1,z2,z4,z6]),(0,[z45,z7,z0,z1,z2,z3,z6]),(0,[z7,z0,z1,z150,z2,z4,z6]),(0,[z7,z0,z151,z17,z1,z2,z4])],[(0,[z7,z0,z1,z2,z152,z4,z6]),(0,[z7,z0,z17,z1,z2,z147,z4]),(1,[z7,z0,z153,z2,z4,z6]),(1,[z7,z0,z17,z2,z4,z35]),(0,[z7,z0,z17,z154,z1,z2,z4]),(0,[z7,z155,z0,z1,z2,z4,z6])]],
   [[(0,[z7,z0,z156,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z157,z6]),(0,[z7,z0,z1,z19,z4,z35,z6]),(1,[z7,z0,z158,z1,z4,z6]),(0,[z7,z0,z1,z2,z4,z159,z6]),(0,[z7,z160,z0,z17,z1,z2,z4]),(0,[z7,z0,z2,z4,z116,z6,z148]),(0,[z7,z161,z0,z1,z2,z4,z6]),(0,[z7,z0,z96,z56,z1,z4,z6]),(0,[z7,z0,z51,z1,z2,z162,z4])],[(0,[z163,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z164,z4,z6]),(1,[z7,z0,z1,z165,z2,z6]),(0,[z7,z0,z1,z113,z88,z4,z6]),(0,[z7,z0,z1,z166,z88,z4,z6]),(0,[z7,z0,z1,z2,z167,z4,z6])],[(0,[z7,z0,z168,z18,z2,z4,z6]),(0,[z137,z7,z0,z51,z1,z2,z4]),(0,[z7,z169,z0,z1,z19,z4,z6]),(0,[z7,z0,z1,z27,z88,z4,z6]),(0,[z7,z170,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z171,z4,z6])],[(0,[z50,z84,z0,z1,z2,z4,z6]),(0,[z34,z7,z0,z1,z2,z3,z6]),(0,[z7,z0,z1,z2,z4,z6,z68]),(0,[z7,z61,z0,z2,z4,z172,z6]),(0,[z7,z0,z1,z49,z2,z4,z6]),(0,[z7,z0,z51,z1,z1,z2,z4]),(0,[z7,z173,z0,z1,z2,z4,z6]),(0,[z7,z0,z174,z1,z2,z4,z6])],[(0,[z7,z126,z12,z1,z2,z4,z6]),(0,[z7,z0,z175,z1,z26,z4,z6]),(0,[z7,z0,z1,z176,z2,z4,z6])],[(0,[z7,z0,z1,z2,z177,z4,z6]),(0,[z7,z0,z51,z1,z2,z4,z35]),(1,[z7,z0,z51,z1,z2,z4]),(0,[z7,z0,z178,z1,z2,z4,z6]),(1,[z7,z0,z179,z2,z4,z6])],[(0,[z75,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z147,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z180])],[(0,[z7,z0,z1,z19,z181,z4,z6]),(0,[z7,z0,z1,z19,z4,z6,z182]),(0,[z7,z0,z51,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z60,z6,z68]),(0,[z183,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z184,z6]),(0,[z7,z0,z168,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z185,z4,z6]),(0,[z7,z0,z96,z1,z4,z22,z6])]],
   [[(0,[z50,z7,z0,z186,z2,z4,z6]),(0,[z7,z0,z12,z1,z19,z4,z6]),(0,[z187,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z68,z182]),(0,[z7,z188,z0,z1,z2,z4,z189]),(0,[z7,z160,z0,z51,z1,z2,z4]),(0,[z7,z0,z190,z1,z2,z4,z6]),(0,[z7,z0,z28,z168,z2,z4,z6]),(0,[z7,z191,z0,z1,z2,z4,z6])],[(1,[z7,z0,z53,z1,z19,z6]),(0,[z7,z0,z192,z1,z88,z4,z6]),(0,[z7,z0,z1,z2,z193,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z182])],[(0,[z50,z7,z0,z1,z19,z4,z6]),(0,[z31,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z1,z19,z19,z4,z6]),(0,[z7,z0,z1,z2,z181,z194,z6])],[(0,[z7,z127,z0,z1,z2,z4,z6]),(0,[z7,z0,z195,z1,z2,z4,z6]),(0,[z7,z196,z0,z1,z88,z4,z6])],[(1,[z7,z0,z1,z119,z4,z6]),(0,[z7,z0,z197,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z97,z5,z6]),(0,[z7,z0,z17,z1,z2,z185,z4]),(0,[z7,z0,z1,z2,z4,z198,z6])],[(0,[z7,z0,z53,z1,z2,z19,z6]),(0,[z7,z0,z1,z88,z44,z4,z6]),(0,[z7,z0,z1,z199,z2,z4,z6]),(0,[z7,z0,z1,z200,z2,z4,z6]),(0,[z7,z0,z201,z51,z1,z2,z4]),(0,[z7,z0,z86,z51,z1,z2,z4]),(0,[z7,z202,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z203,z6])],[(0,[z52,z7,z0,z132,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z204,z6]),(0,[z187,z7,z0,z1,z205,z4,z6]),(0,[z7,z61,z0,z1,z2,z177,z6]),(0,[z7,z126,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z206,z6]),(0,[z207,z7,z0,z1,z2,z4,z6])],[(0,[z7,z0,z1,z208,z2,z4,z6]),(0,[z7,z0,z1,z209,z2,z4,z6]),(0,[z7,z188,z0,z1,z88,z4,z6]),(0,[z210,z7,z0,z1,z2,z4,z6]),(0,[z7,z196,z0,z1,z2,z4,z67]),(1,[z7,z0,z211,z1,z4,z6]),(0,[z7,z0,z17,z1,z30,z2,z4]),(0,[z7,z0,z1,z2,z212,z4,z6]),(1,[z7,z0,z86,z1,z2,z182])]],
   [[(0,[z7,z0,z1,z2,z4,z6,z213]),(0,[z7,z0,z1,z19,z4,z172,z6]),(0,[z7,z0,z1,z214,z88,z4,z6]),(1,[z7,z0,z1,z215,z4,z6]),(0,[z7,z0,z1,z2,z216,z4,z6]),(0,[z187,z7,z0,z51,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z22,z6])],[(1,[z7,z0,z217,z1,z2,z4]),(0,[z7,z90,z0,z1,z88,z4,z6]),(0,[z7,z0,z1,z88,z74,z4,z6]),(0,[z7,z0,z1,z49,z88,z4,z6]),(0,[z7,z0,z1,z2,z218,z4,z6]),(0,[z7,z0,z27,z2,z4,z172,z6])],[(0,[z52,z7,z0,z1,z19,z4,z6]),(0,[z75,z7,z0,z25,z2,z4,z6]),(1,[z7,z0,z175,z1,z4,z6]),(0,[z7,z0,z151,z1,z2,z4,z219])],[(0,[z7,z61,z0,z51,z1,z2,z4]),(0,[z7,z0,z51,z1,z26,z2,z4]),(0,[z7,z160,z0,z1,z2,z194,z6]),(0,[z7,z0,z153,z1,z2,z4,z6]),(0,[z7,z0,z220,z1,z2,z4,z6]),(0,[z7,z0,z96,z1,z2,z39,z6])],[(0,[z221,z7,z0,z1,z2,z4,z6]),(1,[z7,z48,z1,z49,z4,z6]),(0,[z7,z0,z211,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z222,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z223])],[(1,[z7,z0,z1,z2,z64,z6])],[],[(0,[z7,z0,z224,z1,z2,z4,z6]),(0,[z7,z0,z225,z1,z2,z4,z6]),(0,[z226,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z227,z19,z4,z6]),(0,[z7,z0,z1,z228,z2,z4,z6]),(0,[z7,z0,z1,z2,z229,z4,z6]),(0,[z7,z0,z1,z2,z4,z230,z6])]],
   [[(0,[z7,z0,z51,z1,z19,z4,z6]),(1,[z34,z0,z1,z2,z5,z6]),(0,[z7,z0,z1,z2,z4,z231,z6])],[(0,[z7,z0,z1,z2,z4,z43,z6]),(0,[z7,z0,z1,z2,z232,z4,z6]),(0,[z7,z0,z1,z30,z2,z97,z6]),(0,[z7,z0,z1,z2,z233,z4,z6]),(0,[z7,z0,z1,z2,z234,z4,z6])],[(0,[z235,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z39,z4,z22,z6])],[(1,[z7,z0,z1,z2,z80,z6]),(0,[z45,z7,z0,z1,z88,z4,z6]),(0,[z7,z0,z51,z1,z2,z147,z4]),(0,[z7,z0,z41,z96,z1,z4,z6])],[(0,[z7,z0,z236,z1,z132,z2,z4]),(0,[z7,z0,z1,z2,z4,z237,z6]),(0,[z7,z0,z1,z2,z4,z6,z238]),(1,[z7,z0,z168,z2,z181,z6])],[(1,[z7,z0,z1,z165,z19,z6]),(0,[z7,z0,z1,z2,z4,z239,z6]),(0,[z7,z0,z1,z240,z2,z4,z6]),(0,[z7,z0,z1,z2,z241,z4,z6]),(0,[z7,z0,z56,z1,z20,z4,z6])],[(0,[z7,z242,z0,z1,z2,z4,z6]),(0,[z7,z243,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z244,z4,z6]),(0,[z245,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z246,z1,z19,z4,z6]),(0,[z247,z7,z0,z1,z2,z4,z6])],[(0,[z7,z0,z248,z1,z2,z4,z6]),(0,[z249,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z250,z6])]],
   [[(0,[z7,z0,z1,z2,z251,z4,z6]),(0,[z34,z7,z0,z1,z88,z4,z6]),(1,[z7,z0,z1,z252,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z60]),(0,[z7,z0,z1,z2,z4,z60,z182]),(0,[z7,z0,z56,z1,z39,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z172])],[(0,[z7,z0,z253,z1,z2,z4,z6]),(0,[z254,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z255,z6]),(0,[z7,z0,z1,z2,z256,z4,z6]),(0,[z7,z0,z17,z56,z1,z2,z4])],[(0,[z45,z7,z0,z1,z2,z35,z6])],[(0,[z257,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z258])],[(0,[z7,z11,z0,z1,z2,z4,z6]),(0,[z7,z98,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z259,z4,z6]),(0,[z7,z0,z1,z2,z97,z3,z6]),(1,[z7,z0,z1,z260,z4,z6]),(0,[z7,z261,z0,z1,z2,z4,z6]),(1,[z7,z134,z1,z2,z4,z67]),(0,[z262,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z263,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z264,z4,z6])],[(0,[z84,z7,z12,z1,z2,z4,z6]),(0,[z137,z7,z0,z1,z19,z4,z6]),(0,[z265,z7,z0,z1,z2,z4,z6]),(0,[z75,z187,z0,z1,z2,z4,z6]),(0,[z7,z0,z41,z17,z2,z4,z6]),(0,[z7,z0,z51,z1,z2,z4,z182]),(0,[z7,z0,z266,z1,z2,z4,z6])],[(1,[z7,z0,z186,z2,z4,z6]),(0,[z7,z0,z1,z165,z2,z4,z6]),(0,[z7,z0,z1,z88,z152,z4,z6]),(0,[z7,z0,z1,z2,z267,z4,z6]),(0,[z7,z0,z268,z1,z2,z4,z6])],[(0,[z7,z0,z269,z1,z2,z4,z6]),(0,[z7,z0,z1,z270,z2,z4,z6]),(1,[z7,z0,z1,z2,z117,z6]),(0,[z7,z0,z1,z2,z117,z4,z6]),(0,[z7,z0,z51,z1,z2,z4,z59]),(1,[z7,z0,z1,z30,z39,z6])]],
   [[(0,[z7,z0,z1,z2,z271,z4,z6]),(0,[z7,z0,z12,z51,z1,z2,z4]),(0,[z272,z7,z0,z1,z2,z4,z6]),(1,[z7,z0,z17,z132,z2,z4]),(0,[z7,z0,z217,z1,z132,z2,z4]),(1,[z7,z0,z1,z19,z4,z6]),(0,[z7,z0,z273,z1,z88,z4,z6]),(0,[z7,z274,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z275]),(0,[z7,z160,z0,z1,z2,z97,z6]),(0,[z7,z0,z1,z2,z4,z6,z276]),(0,[z7,z0,z28,z1,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z277,z4]),(0,[z7,z0,z51,z2,z4,z172,z6])],[(1,[z7,z0,z1,z2,z4,z278]),(0,[z7,z0,z151,z1,z19,z4,z6]),(0,[z7,z0,z1,z88,z171,z4,z6]),(0,[z7,z279,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z148]),(0,[z7,z0,z280,z1,z2,z4,z6]),(0,[z7,z0,z1,z4,z219,z6,z223])],[(0,[z7,z0,z1,z2,z4,z281,z6]),(0,[z7,z0,z1,z88,z4,z6,z68]),(0,[z7,z0,z282,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z283,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z284]),(0,[z7,z0,z154,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z285]),(0,[z7,z0,z1,z2,z4,z286,z6])],[(0,[z7,z160,z0,z1,z19,z4,z6]),(0,[z287,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z64]),(0,[z7,z0,z51,z288,z1,z2,z4]),(0,[z7,z0,z51,z1,z30,z2,z4])],[(0,[z289,z7,z0,z1,z2,z4,z6]),(0,[z75,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z290,z1,z2,z4,z6]),(0,[z7,z0,z1,z291,z2,z4,z6]),(0,[z262,z7,z0,z51,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z292,z6])],[(0,[z7,z0,z1,z88,z147,z4,z6]),(0,[z7,z0,z1,z293,z2,z4,z6]),(0,[z7,z0,z288,z1,z2,z4,z6]),(0,[z294,z7,z0,z1,z2,z4,z6])],[(0,[z295,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z51,z1,z132,z2,z4]),(0,[z296,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z194]),(0,[z7,z0,z1,z297,z2,z4,z6])],[(0,[z50,z7,z0,z1,z2,z4,z298]),(0,[z7,z0,z1,z2,z4,z299,z6]),(0,[z7,z300,z0,z1,z2,z4,z6]),(0,[z7,z0,z17,z1,z301,z2,z4]),(0,[z7,z0,z302,z1,z2,z4,z6])]],
   [[(0,[z7,z0,z1,z303,z2,z4,z6]),(0,[z7,z0,z1,z2,z194,z35,z6]),(0,[z304,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z305,z2,z4,z6]),(0,[z7,z0,z51,z1,z2,z4,z223])],[(0,[z7,z127,z0,z17,z1,z2,z4]),(0,[z31,z7,z0,z132,z2,z4,z6]),(0,[z7,z306,z0,z1,z2,z4,z6]),(0,[z7,z307,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z194,z6]),(0,[z7,z0,z1,z2,z4,z6,z308]),(0,[z7,z0,z151,z1,z4,z6,z223])],[(0,[z52,z7,z0,z51,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z6,z309]),(0,[z7,z0,z1,z88,z88,z4,z6]),(0,[z7,z310,z0,z1,z2,z4,z6]),(0,[z311,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z312,z1,z2,z4,z6]),(0,[z7,z0,z86,z1,z2,z6,z182])],[(0,[z187,z7,z0,z1,z19,z4,z6]),(0,[z7,z0,z1,z2,z313,z4,z6]),(0,[z7,z314,z0,z1,z2,z4,z6]),(1,[z7,z0,z1,z77,z4,z6]),(0,[z7,z126,z160,z1,z2,z4,z6])],[(0,[z315,z7,z0,z1,z2,z4,z6]),(0,[z316,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z317,z2,z4,z6]),(0,[z75,z7,z0,z51,z1,z2,z4]),(0,[z7,z126,z0,z17,z1,z2,z4]),(0,[z7,z0,z318,z1,z4,z6,z148]),(0,[z319,z7,z0,z1,z2,z4,z6]),(0,[z320,z7,z0,z1,z2,z4,z6])],[(0,[z7,z0,z1,z2,z321,z4,z6]),(0,[z31,z7,z0,z1,z19,z4,z6]),(0,[z322,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z323,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z324])],[(0,[z50,z7,z0,z1,z2,z325,z6]),(0,[z7,z0,z1,z1,z2,z4,z6]),(0,[z7,z0,z1,z166,z2,z4,z6]),(0,[z31,z7,z0,z1,z2,z4,z278]),(0,[z7,z0,z1,z326,z88,z4,z6]),(0,[z7,z0,z327,z1,z2,z4,z6]),(0,[z7,z0,z1,z328,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z64,z6])],[(0,[z7,z0,z1,z329,z2,z4,z6]),(0,[z7,z330,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z27,z2,z4,z6])]],
   [[(0,[z7,z0,z1,z2,z4,z331,z6]),(1,[z7,z126,z1,z2,z97,z6]),(0,[z7,z0,z1,z2,z4,z332,z6]),(0,[z7,z0,z333,z1,z2,z4,z6])],[(0,[z7,z334,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z335,z6]),(0,[z7,z0,z336,z1,z2,z4,z6]),(0,[z7,z0,z1,z19,z4,z6,z68]),(0,[z7,z196,z0,z1,z2,z4,z148]),(0,[z7,z0,z1,z337,z2,z4,z6])],[(0,[z221,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z338,z6]),(0,[z339,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z340,z6]),(0,[z7,z0,z17,z220,z1,z2,z4]),(0,[z341,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z1,z30,z39,z4,z6]),(0,[z7,z0,z1,z342,z2,z4,z6])],[(0,[z7,z0,z1,z2,z4,z343,z6]),(0,[z7,z0,z18,z2,z4,z35,z6]),(0,[z7,z7,z0,z1,z19,z4,z6])],[(0,[z7,z0,z1,z2,z4,z80,z6]),(0,[z344,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z51,z1,z2,z4,z60]),(0,[z7,z0,z1,z345,z2,z4,z6]),(0,[z7,z0,z51,z1,z2,z4,z172])],[(0,[z7,z346,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z32]),(0,[z7,z0,z158,z1,z26,z4,z6]),(0,[z7,z0,z1,z347,z2,z4,z6]),(0,[z7,z0,z86,z1,z2,z4,z182])],[(1,[z7,z0,z236,z1,z2,z4]),(0,[z7,z0,z192,z1,z2,z4,z6]),(0,[z7,z348,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z349,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z42]),(1,[z7,z0,z51,z2,z4,z172])],[(0,[z7,z0,z1,z350,z2,z4,z6]),(0,[z7,z0,z51,z1,z88,z2,z4]),(0,[z7,z351,z0,z1,z2,z4,z6]),(0,[z7,z0,z86,z1,z2,z4,z59])]],
   [[(1,[z7,z0,z1,z352,z4,z6]),(0,[z7,z0,z1,z2,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z353,z6]),(0,[z7,z0,z1,z354,z2,z4,z6]),(0,[z7,z196,z0,z1,z2,z4,z6])],[(0,[z7,z0,z1,z2,z3,z4,z6]),(0,[z7,z0,z151,z1,z2,z4,z223]),(0,[z7,z0,z1,z355,z2,z4,z6])],[(1,[z7,z11,z0,z1,z2,z6]),(0,[z221,z7,z0,z51,z1,z2,z4]),(0,[z7,z0,z1,z25,z2,z4,z6]),(0,[z7,z0,z1,z2,z356,z4,z6])],[(0,[z7,z0,z1,z2,z4,z357,z6]),(0,[z7,z0,z1,z2,z5,z194,z6]),(1,[z7,z0,z1,z2,z177,z6]),(0,[z7,z0,z1,z2,z358,z4,z6])],[(0,[z7,z0,z1,z19,z4,z6,z359]),(0,[z7,z0,z1,z88,z4,z239,z6]),(0,[z7,z0,z1,z360,z2,z4,z6]),(0,[z7,z0,z1,z2,z361,z4,z6]),(0,[z7,z62,z1,z26,z2,z4,z6]),(0,[z7,z188,z0,z1,z2,z4,z6])],[(0,[z7,z0,z56,z1,z19,z4,z6]),(0,[z7,z0,z96,z1,z88,z4,z6]),(0,[z7,z188,z0,z1,z2,z4,z94]),(0,[z7,z0,z1,z362,z2,z4,z6]),(0,[z7,z363,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z27,z2,z4,z42]),(0,[z7,z0,z1,z214,z2,z4,z6])],[(0,[z50,z7,z0,z195,z2,z4,z6]),(0,[z7,z0,z1,z19,z4,z22,z6]),(1,[z7,z0,z1,z205,z4,z6]),(0,[z7,z0,z1,z2,z4,z59,z68]),(0,[z7,z90,z0,z1,z2,z4,z6]),(1,[z7,z0,z269,z1,z2,z4]),(0,[z7,z0,z364,z1,z2,z4,z6])],[(0,[z7,z0,z365,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z366,z4,z6]),(0,[z7,z0,z1,z30,z2,z194,z6]),(0,[z7,z367,z0,z1,z2,z4,z6]),(0,[z368,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z369,z6]),(0,[z7,z0,z2,z4,z6,z123,z223])]],
   [[(0,[z7,z0,z132,z2,z4,z35,z6]),(0,[z45,z7,z0,z96,z1,z2,z6]),(0,[z7,z0,z1,z2,z97,z35,z6]),(0,[z7,z0,z1,z2,z4,z6,z370]),(0,[z7,z0,z17,z168,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z371,z6]),(0,[z7,z0,z1,z2,z59,z6,z182])],[(0,[z221,z137,z0,z1,z2,z4,z6]),(0,[z7,z0,z41,z1,z88,z4,z6]),(0,[z7,z61,z0,z17,z2,z4,z6]),(0,[z7,z0,z51,z62,z1,z2,z4]),(0,[z7,z0,z153,z2,z4,z6,z148]),(0,[z7,z0,z1,z2,z4,z372,z6]),(0,[z7,z0,z151,z51,z1,z2,z4]),(1,[z7,z0,z96,z1,z22,z6])],[(0,[z7,z373,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z374,z6]),(0,[z7,z375,z0,z1,z2,z4,z6]),(0,[z7,z160,z1,z2,z4,z194,z6]),(0,[z7,z0,z51,z1,z2,z4,z194]),(0,[z7,z0,z1,z2,z4,z14,z6]),(0,[z7,z0,z376,z51,z1,z2,z4]),(0,[z377,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z378,z6])],[(0,[z7,z379,z0,z12,z1,z2,z6]),(0,[z7,z0,z18,z2,z4,z172,z6]),(0,[z7,z0,z1,z2,z4,z5,z6]),(0,[z380,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z318,z1,z2,z4,z6]),(0,[z7,z0,z381,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z382,z6])],[(0,[z7,z383,z0,z1,z2,z4,z6]),(0,[z7,z0,z18,z1,z2,z384,z6]),(0,[z7,z0,z1,z19,z4,z67,z6]),(0,[z7,z0,z76,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z385]),(0,[z7,z0,z2,z171,z4,z23,z6])],[(1,[z7,z0,z1,z2,z4,z298]),(0,[z34,z7,z0,z96,z1,z2,z6]),(0,[z7,z188,z0,z1,z147,z4,z6])],[(0,[z386,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z132,z88,z4,z6]),(0,[z221,z0,z1,z88,z2,z4,z6]),(0,[z7,z0,z387,z1,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z59]),(0,[z7,z0,z388,z51,z1,z2,z4]),(0,[z7,z0,z179,z1,z2,z4,z6])],[(0,[z262,z7,z0,z1,z19,z4,z6]),(0,[z7,z0,z51,z1,z88,z4,z6]),(0,[z7,z61,z0,z26,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z389,z6]),(0,[z7,z0,z390,z1,z2,z4,z6]),(0,[z7,z0,z96,z1,z2,z22,z6])]],
   [[(0,[z84,z127,z0,z1,z2,z4,z6]),(0,[z7,z0,z62,z1,z88,z4,z6]),(0,[z7,z0,z1,z88,z4,z6,z148]),(0,[z45,z7,z0,z1,z2,z4,z6]),(0,[z7,z391,z0,z1,z2,z4,z6])],[(0,[z52,z7,z0,z1,z392,z4,z6]),(0,[z7,z0,z1,z393,z2,z4,z6])],[(0,[z7,z0,z1,z19,z4,z237,z6]),(0,[z34,z7,z126,z0,z1,z2,z6]),(0,[z7,z0,z394,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z395,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z29]),(0,[z7,z0,z15,z51,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z6,z396])],[(0,[z7,z0,z1,z2,z4,z397,z6]),(0,[z7,z0,z398,z1,z2,z4,z6]),(0,[z7,z0,z53,z1,z2,z4,z6]),(0,[z75,z7,z0,z1,z260,z4,z6]),(0,[z7,z90,z0,z1,z2,z4,z36]),(0,[z7,z0,z399,z1,z2,z4,z6])],[(1,[z7,z0,z1,z2,z325,z6]),(0,[z400,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z168,z132,z2,z4,z6]),(0,[z7,z0,z18,z26,z2,z4,z6]),(0,[z34,z7,z0,z365,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z401]),(0,[z7,z0,z1,z2,z4,z402,z6]),(0,[z295,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z403,z1,z2,z4,z6]),(1,[z7,z0,z2,z4,z6,z123])],[(0,[z7,z0,z1,z2,z4,z404,z6]),(0,[z84,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z17,z1,z132,z2,z4]),(0,[z31,z7,z0,z51,z1,z2,z4]),(0,[z34,z7,z0,z1,z2,z4,z6])],[(0,[z7,z0,z405,z1,z2,z4,z6]),(0,[z7,z406,z0,z1,z2,z4,z6]),(0,[z304,z7,z0,z17,z1,z2,z4])],[(0,[z7,z407,z0,z1,z2,z4,z6]),(1,[z52,z0,z132,z2,z4,z6]),(0,[z75,z7,z0,z1,z19,z4,z6]),(0,[z187,z7,z0,z1,z2,z4,z60]),(0,[z408,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z409,z2,z4,z6])]],
   [[(0,[z7,z0,z132,z2,z4,z172,z6]),(0,[z7,z0,z168,z1,z19,z4,z6]),(0,[z7,z0,z1,z88,z4,z194,z6]),(0,[z7,z0,z1,z2,z100,z4,z6]),(1,[z7,z0,z1,z2,z4,z189]),(0,[z7,z48,z0,z1,z2,z102,z6]),(0,[z7,z0,z1,z2,z4,z6,z410])],[(1,[z7,z0,z1,z411,z4,z6]),(0,[z7,z0,z1,z2,z4,z412,z6]),(0,[z7,z0,z413,z1,z2,z4,z6])],[(0,[z414,z7,z0,z1,z2,z4,z6]),(0,[z52,z0,z1,z132,z2,z4,z6])],[(0,[z415,z7,z0,z1,z2,z4,z6]),(0,[z7,z416,z0,z1,z2,z4,z6]),(0,[z7,z417,z0,z1,z2,z4,z6]),(0,[z7,z0,z51,z1,z214,z2,z4]),(0,[z7,z418,z0,z1,z2,z4,z6])],[(0,[z7,z127,z0,z1,z19,z4,z6]),(0,[z137,z7,z0,z1,z88,z4,z6]),(1,[z7,z0,z17,z1,z19,z4]),(0,[z7,z126,z0,z1,z2,z97,z6])],[(0,[z84,z7,z0,z51,z1,z2,z4]),(0,[z7,z0,z197,z1,z19,z4,z6]),(0,[z7,z0,z273,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z419,z6])],[(0,[z420,z7,z0,z1,z2,z4,z6])],[(0,[z50,z7,z127,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z421]),(0,[z7,z0,z1,z19,z4,z6,z148]),(0,[z7,z0,z1,z30,z19,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z422]),(0,[z7,z0,z1,z2,z4,z423,z6]),(0,[z7,z0,z168,z2,z181,z4,z6])]],
   [[(0,[z7,z424,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z425,z6]),(0,[z7,z0,z1,z2,z4,z6,z426]),(0,[z7,z0,z1,z2,z427,z4,z6])],[(0,[z7,z48,z0,z1,z2,z4,z6]),(0,[z7,z0,z428,z1,z2,z4,z6])],[(0,[z7,z0,z1,z2,z4,z6,z429]),(0,[z45,z7,z0,z1,z30,z2,z6]),(0,[z7,z0,z1,z2,z4,z430,z6]),(0,[z75,z7,z0,z1,z77,z4,z6]),(0,[z7,z90,z0,z1,z2,z4,z115]),(0,[z7,z0,z431,z1,z2,z4,z6]),(0,[z7,z134,z196,z1,z2,z4,z6]),(1,[z7,z0,z28,z2,z35,z6]),(0,[z7,z0,z1,z2,z432,z4,z6])],[(0,[z7,z0,z1,z2,z4,z433,z6]),(0,[z7,z434,z0,z1,z2,z4,z6]),(1,[z7,z0,z151,z1,z4,z223])],[(1,[z7,z0,z195,z2,z4,z6]),(1,[z7,z0,z51,z1,z19,z4]),(0,[z7,z0,z1,z2,z4,z435,z6])],[(0,[z221,z7,z0,z1,z19,z4,z6]),(0,[z0,z1,z88,z2,z19,z4,z6]),(0,[z7,z0,z175,z1,z2,z4,z6]),(0,[z7,z188,z0,z1,z49,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z436])],[(0,[z7,z0,z17,z1,z88,z2,z4]),(0,[z7,z0,z1,z2,z437,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z438]),(0,[z7,z196,z0,z17,z1,z2,z4]),(0,[z7,z439,z0,z1,z2,z4,z6]),(0,[z7,z0,z440,z1,z2,z4,z6]),(0,[z7,z0,z105,z1,z2,z4,z6])],[(1,[z7,z0,z1,z392,z4,z6]),(0,[z7,z0,z441,z1,z2,z4,z6]),(0,[z7,z0,z1,z88,z2,z4,z6]),(1,[z221,z0,z1,z88,z4,z6]),(0,[z7,z0,z86,z1,z88,z4,z6]),(0,[z34,z7,z0,z1,z30,z2,z6]),(0,[z7,z0,z1,z2,z442,z4,z6]),(0,[z7,z188,z0,z151,z1,z4,z6]),(0,[z7,z0,z51,z1,z2,z97,z4]),(0,[z7,z0,z1,z2,z4,z219,z67]),(0,[z7,z0,z1,z2,z181,z6,z182]),(0,[z7,z443,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z444])]],
   [[(0,[z7,z0,z1,z119,z2,z4,z6]),(0,[z7,z0,z1,z88,z3,z4,z6]),(0,[z7,z445,z0,z1,z2,z4,z6]),(0,[z7,z0,z168,z2,z4,z172,z6]),(0,[z7,z0,z130,z51,z1,z2,z4]),(0,[z7,z446,z0,z1,z2,z4,z6])],[(0,[z7,z0,z1,z2,z447,z4,z6]),(0,[z7,z0,z1,z2,z4,z448,z6]),(0,[z7,z0,z1,z2,z20,z4,z6]),(0,[z7,z449,z0,z1,z2,z4,z6]),(0,[z450,z7,z0,z1,z2,z4,z6])],[(0,[z187,z7,z0,z1,z88,z4,z6]),(1,[z75,z0,z1,z2,z4,z60]),(0,[z7,z48,z0,z1,z147,z4,z6]),(0,[z7,z0,z1,z2,z4,z148,z223])],[(0,[z7,z0,z1,z326,z2,z4,z6]),(0,[z7,z0,z451,z1,z2,z4,z6]),(0,[z7,z0,z1,z452,z2,z4,z6])],[(0,[z50,z7,z0,z1,z2,z93,z6]),(0,[z50,z7,z12,z1,z2,z4,z6]),(0,[z7,z0,z453,z1,z2,z4,z6]),(1,[z7,z90,z62,z2,z4,z6]),(0,[z7,z90,z0,z17,z1,z2,z4]),(1,[z7,z0,z318,z1,z4,z6]),(0,[z7,z0,z168,z1,z2,z181,z6]),(0,[z7,z0,z1,z2,z39,z4,z6]),(0,[z7,z0,z1,z454,z2,z4,z6])],[(0,[z7,z0,z1,z2,z455,z4,z6]),(1,[z7,z0,z1,z350,z4,z6]),(0,[z7,z0,z1,z2,z384,z4,z6]),(0,[z7,z61,z0,z1,z88,z4,z6]),(1,[z7,z0,z81,z2,z4,z6]),(1,[z7,z61,z26,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z456]),(0,[z7,z0,z1,z2,z457,z4,z6])],[(0,[z7,z169,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z88,z4,z458,z6]),(0,[z34,z7,z106,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z459]),(0,[z7,z0,z1,z2,z4,z6,z460])],[(0,[z7,z0,z1,z2,z58,z4,z6]),(0,[z7,z48,z0,z1,z88,z4,z6]),(0,[z7,z0,z51,z1,z27,z2,z4])]],
   [[(0,[z7,z0,z17,z62,z1,z2,z4])],[(0,[z461,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z462,z6]),(0,[z7,z0,z463,z1,z2,z4,z6]),(0,[z464,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z51,z1,z2,z20,z4]),(0,[z465,z7,z0,z1,z2,z4,z6])],[(0,[z7,z0,z236,z1,z2,z4,z6]),(0,[z7,z0,z18,z1,z88,z4,z6]),(0,[z7,z0,z1,z88,z4,z5,z6]),(0,[z7,z0,z466,z1,z2,z4,z6])],[(0,[z7,z467,z0,z1,z2,z4,z6]),(0,[z468,z7,z0,z1,z2,z4,z6]),(0,[z7,z134,z0,z1,z88,z4,z6]),(0,[z7,z0,z269,z1,z26,z2,z4]),(0,[z7,z0,z1,z2,z4,z59,z6])],[(1,[z7,z0,z1,z303,z4,z6]),(1,[z7,z0,z17,z1,z88,z4]),(1,[z7,z0,z1,z2,z4,z33]),(0,[z7,z90,z0,z51,z1,z2,z4]),(0,[z7,z469,z0,z1,z2,z4,z6]),(0,[z7,z470,z0,z1,z2,z4,z6]),(0,[z7,z0,z471,z1,z2,z4,z6]),(0,[z7,z472,z0,z1,z2,z4,z6])],[(0,[z7,z0,z1,z2,z4,z473,z6]),(0,[z7,z188,z0,z41,z1,z4,z6]),(0,[z7,z0,z474,z1,z2,z4,z6]),(0,[z7,z0,z1,z475,z2,z4,z6]),(0,[z7,z0,z41,z56,z2,z4,z6]),(0,[z7,z0,z105,z2,z171,z4,z6])],[(0,[z50,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z17,z1,z88,z4,z6]),(0,[z45,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z1,z2,z97,z4,z6]),(1,[z7,z0,z476,z1,z2,z4]),(0,[z7,z0,z1,z2,z477,z20,z4])],[(0,[z7,z0,z1,z478,z2,z4,z6]),(0,[z7,z0,z1,z19,z3,z4,z6]),(0,[z7,z0,z1,z26,z19,z4,z6]),(0,[z7,z0,z1,z165,z19,z4,z6]),(0,[z7,z1,z2,z97,z4,z194,z6]),(0,[z7,z134,z0,z1,z2,z4,z67]),(1,[z7,z0,z1,z4,z9,z6]),(0,[z479,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z277,z4,z6])]],
   [[(1,[z7,z160,z1,z2,z194,z6]),(0,[z7,z0,z1,z27,z2,z4,z340]),(0,[z7,z0,z480,z1,z2,z4,z6]),(0,[z7,z0,z168,z51,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z481,z6])],[(0,[z7,z0,z28,z1,z19,z4,z6]),(0,[z7,z0,z1,z88,z4,z6,z29]),(0,[z7,z0,z1,z2,z215,z4,z6]),(0,[z7,z0,z17,z1,z49,z2,z4]),(0,[z7,z482,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z483,z2,z4,z6]),(0,[z7,z0,z41,z1,z27,z4,z6]),(0,[z484,z7,z0,z1,z2,z4,z6])],[(0,[z485,z7,z0,z1,z2,z4,z6]),(0,[z31,z7,z0,z1,z350,z4,z6]),(0,[z7,z0,z1,z2,z486,z4,z6]),(0,[z7,z0,z1,z205,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z67]),(0,[z7,z0,z96,z1,z2,z4,z6])],[(0,[z487,z7,z0,z1,z2,z4,z6]),(0,[z137,z0,z1,z2,z19,z4,z6]),(0,[z7,z0,z1,z19,z171,z4,z6]),(0,[z34,z7,z0,z17,z1,z2,z4]),(0,[z75,z7,z0,z1,z2,z4,z60]),(0,[z7,z0,z1,z301,z2,z4,z6]),(0,[z7,z0,z488,z1,z2,z4,z6])],[(0,[z7,z489,z0,z1,z2,z4,z6]),(0,[z7,z127,z0,z51,z1,z2,z4]),(1,[z7,z0,z1,z2,z384,z6]),(1,[z7,z0,z51,z1,z88,z4]),(0,[z7,z0,z56,z1,z88,z4,z6]),(0,[z7,z0,z1,z88,z4,z219,z6]),(1,[z7,z138,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z490,z6]),(0,[z7,z0,z491,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z492,z6])],[(1,[z50,z12,z1,z2,z4,z6]),(0,[z493,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z171,z59,z6])],[(0,[z7,z0,z217,z1,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z68]),(0,[z7,z0,z1,z2,z4,z494,z6]),(0,[z7,z0,z41,z1,z2,z4,z6])],[(0,[z7,z0,z1,z19,z147,z4,z6]),(0,[z7,z0,z1,z2,z4,z60,z6]),(0,[z7,z0,z495,z1,z2,z4,z6]),(0,[z7,z126,z0,z51,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z67,z223]),(0,[z496,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z497,z4,z6]),(0,[z7,z0,z1,z214,z2,z4,z219])]],
   [[(0,[z84,z7,z0,z1,z19,z4,z6]),(0,[z7,z498,z0,z1,z2,z4,z6]),(0,[z7,z0,z62,z18,z2,z4,z6]),(0,[z7,z0,z499,z1,z2,z4,z6]),(0,[z500,z7,z0,z1,z2,z4,z6])],[(0,[z7,z12,z1,z2,z4,z194,z6]),(0,[z7,z501,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z502]),(0,[z7,z0,z1,z2,z503,z4,z6])],[(0,[z7,z0,z1,z2,z325,z4,z6]),(0,[z7,z0,z12,z1,z88,z4,z6]),(0,[z7,z0,z1,z504,z2,z4,z6]),(0,[z7,z505,z0,z1,z2,z4,z6]),(0,[z7,z48,z0,z1,z49,z4,z6]),(0,[z506,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z507,z1,z2,z4,z6]),(0,[z7,z0,z17,z1,z214,z2,z4])],[(0,[z7,z0,z1,z132,z2,z4,z6]),(0,[z7,z0,z1,z227,z2,z4,z6]),(0,[z7,z0,z1,z508,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z171,z4]),(0,[z7,z0,z1,z2,z509,z4,z6]),(0,[z7,z0,z1,z2,z510,z4,z6]),(1,[z7,z0,z2,z4,z23,z6])],[(0,[z50,z7,z0,z1,z88,z4,z6]),(0,[z511,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z512,z4,z6]),(0,[z7,z0,z51,z1,z2,z4,z6])],[(0,[z7,z0,z1,z186,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z278,z6]),(0,[z7,z0,z62,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z189,z6])],[(0,[z50,z0,z12,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z513]),(0,[z514,z7,z0,z1,z2,z4,z6]),(0,[z262,z7,z0,z1,z88,z4,z6])],[(0,[z7,z515,z0,z1,z2,z4,z6]),(1,[z7,z61,z0,z17,z2,z4]),(0,[z7,z516,z0,z1,z2,z4,z6]),(0,[z7,z1,z2,z4,z67,z6,z148]),(0,[z517,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z35,z6]),(0,[z518,z7,z0,z1,z2,z4,z6])]],
   [[(0,[z52,z31,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z19,z4,z6,z29]),(0,[z7,z0,z1,z27,z19,z4,z6]),(0,[z7,z0,z1,z2,z4,z519,z6]),(0,[z7,z0,z1,z2,z520,z4,z6]),(0,[z7,z0,z1,z521,z2,z4,z6]),(0,[z7,z0,z1,z2,z522,z4,z6])],[(0,[z7,z0,z1,z2,z477,z4,z6]),(0,[z7,z0,z523,z1,z2,z4,z6])],[(0,[z7,z0,z246,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z458,z6]),(0,[z7,z126,z0,z1,z2,z194,z6]),(0,[z7,z0,z524,z1,z2,z4,z6])],[(0,[z7,z0,z1,z2,z4,z67,z60]),(0,[z7,z0,z525,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z526,z6]),(0,[z527,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z528,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z529])],[(0,[z52,z7,z0,z1,z88,z4,z6]),(0,[z7,z0,z1,z2,z4,z530,z6]),(0,[z7,z90,z0,z62,z2,z4,z6]),(0,[z7,z0,z531,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z532,z6])],[(0,[z7,z0,z1,z2,z4,z6,z533]),(0,[z7,z0,z1,z2,z260,z4,z6]),(0,[z7,z534,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z535,z4,z6]),(0,[z7,z0,z1,z2,z4,z536,z6]),(0,[z7,z0,z28,z1,z2,z181,z6]),(0,[z7,z0,z1,z2,z537,z4,z6]),(0,[z7,z538,z0,z1,z2,z4,z6])],[(0,[z34,z7,z0,z1,z215,z4,z6]),(0,[z7,z0,z17,z1,z2,z97,z4]),(0,[z7,z0,z1,z2,z181,z4,z6]),(0,[z7,z0,z539,z1,z2,z4,z6]),(0,[z540,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z182])],[(0,[z7,z0,z62,z132,z2,z4,z6]),(0,[z7,z501,z0,z1,z88,z4,z6]),(0,[z7,z0,z1,z2,z541,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z542]),(0,[z7,z0,z1,z543,z2,z4,z6]),(0,[z7,z449,z0,z17,z1,z2,z4]),(0,[z7,z0,z544,z1,z2,z4,z6])]],
   [[(0,[z7,z0,z1,z88,z20,z4,z6]),(0,[z45,z7,z126,z0,z1,z2,z6])],[(0,[z137,z7,z0,z1,z2,z4,z6]),(0,[z7,z196,z0,z1,z19,z4,z6]),(0,[z7,z0,z1,z2,z19,z4,z6]),(0,[z7,z0,z545,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z546]),(0,[z7,z0,z1,z2,z4,z219,z148]),(0,[z7,z0,z1,z4,z9,z35,z6]),(0,[z7,z0,z1,z2,z4,z6,z547])],[(0,[z7,z48,z0,z41,z1,z4,z6]),(0,[z7,z0,z1,z2,z4,z548,z6]),(0,[z7,z0,z1,z2,z4,z549,z6])],[(0,[z7,z0,z1,z88,z39,z4,z6]),(0,[z7,z0,z1,z2,z550,z4,z6]),(0,[z7,z61,z0,z1,z2,z69,z6]),(0,[z7,z0,z1,z2,z4,z551,z6]),(0,[z7,z0,z17,z1,z2,z277,z6]),(0,[z7,z0,z552,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z553])],[(0,[z7,z554,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z555,z2,z4,z6]),(0,[z7,z556,z0,z1,z2,z4,z6]),(0,[z557,z7,z0,z1,z2,z4,z6]),(1,[z7,z0,z2,z4,z116,z6]),(0,[z7,z0,z1,z558,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z559]),(0,[z7,z0,z560,z1,z2,z4,z6])],[(0,[z7,z0,z1,z2,z4,z6,z561]),(0,[z7,z0,z51,z1,z49,z2,z4]),(0,[z7,z0,z476,z1,z2,z20,z4]),(0,[z7,z0,z1,z2,z562,z4,z6]),(0,[z7,z0,z1,z2,z35,z6,z182])],[(0,[z7,z0,z1,z214,z19,z4,z6]),(0,[z7,z0,z1,z30,z88,z4,z6]),(0,[z7,z0,z563,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z564,z6]),(0,[z7,z0,z1,z2,z4,z565,z6]),(0,[z7,z0,z51,z1,z2,z4,z67]),(0,[z7,z0,z17,z1,z27,z2,z4]),(0,[z7,z0,z168,z1,z2,z35,z6]),(1,[z7,z0,z79,z1,z2,z4]),(0,[z7,z0,z51,z1,z2,z212,z4])],[(0,[z7,z90,z0,z1,z19,z4,z6]),(0,[z7,z0,z1,z49,z19,z4,z6]),(0,[z7,z160,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z172,z6])]],
   [[(0,[z84,z7,z0,z1,z352,z4,z6]),(1,[z7,z0,z1,z164,z4,z6]),(1,[z7,z0,z1,z361,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z566]),(0,[z7,z0,z17,z1,z2,z20,z4]),(0,[z7,z0,z1,z2,z4,z219,z6])],[(1,[z31,z0,z18,z2,z4,z6]),(0,[z45,z7,z0,z1,z252,z4,z6]),(0,[z7,z0,z567,z1,z2,z4,z6]),(0,[z7,z0,z28,z51,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z6,z223]),(0,[z7,z0,z1,z2,z4,z6,z568])],[(0,[z7,z0,z1,z88,z4,z59,z6]),(0,[z7,z0,z51,z1,z2,z4,z68]),(0,[z7,z0,z1,z569,z2,z4,z6]),(0,[z7,z0,z1,z570,z2,z4,z6])],[(0,[z7,z0,z1,z2,z4,z571,z6]),(0,[z75,z0,z1,z2,z4,z60,z6]),(0,[z7,z0,z1,z2,z572,z4,z6]),(0,[z7,z0,z573,z1,z2,z4,z6])],[(0,[z7,z188,z0,z1,z4,z219,z6]),(0,[z7,z0,z1,z2,z574,z4,z6]),(0,[z7,z0,z201,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z575]),(0,[z7,z0,z86,z1,z2,z4,z6])],[(0,[z7,z0,z1,z2,z4,z576,z6]),(0,[z7,z0,z1,z165,z2,z19,z6]),(0,[z7,z0,z1,z88,z97,z4,z6]),(0,[z7,z138,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z252,z2,z4,z6]),(0,[z7,z577,z0,z1,z2,z4,z6]),(0,[z479,z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z17,z51,z2,z4,z6]),(0,[z7,z0,z1,z214,z4,z219,z6])],[(0,[z7,z578,z0,z1,z2,z4,z6]),(0,[z7,z0,z579,z1,z2,z4,z6]),(0,[z7,z0,z158,z1,z2,z4,z6]),(0,[z7,z0,z211,z1,z4,z35,z6]),(0,[z7,z580,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z581])],[(0,[z187,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z51,z1,z2,z171,z4]),(0,[z7,z0,z1,z2,z4,z6,z582])]],
   [[(1,[z137,z0,z1,z19,z4,z6]),(0,[z7,z0,z1,z2,z4,z115,z6]),(1,[z7,z0,z17,z1,z2,z277]),(0,[z7,z0,z96,z17,z1,z2,z4])],[(0,[z50,z7,z0,z1,z271,z4,z6]),(0,[z31,z0,z18,z1,z2,z4,z6]),(0,[z45,z7,z0,z1,z19,z4,z6]),(0,[z7,z134,z0,z1,z2,z4,z148]),(0,[z7,z0,z583,z1,z2,z4,z6]),(0,[z7,z0,z584,z1,z2,z4,z6])],[(1,[z7,z0,z17,z18,z2,z4]),(1,[z7,z0,z1,z88,z4,z6]),(0,[z7,z126,z0,z1,z19,z4,z6]),(0,[z45,z7,z160,z0,z1,z2,z6]),(0,[z7,z61,z0,z1,z2,z4,z6]),(0,[z7,z0,z2,z181,z4,z35,z6]),(0,[z7,z0,z17,z1,z2,z4,z219]),(0,[z7,z0,z1,z2,z162,z4,z6])],[(0,[z7,z0,z1,z19,z455,z4,z6]),(0,[z7,z0,z151,z1,z88,z4,z6]),(0,[z187,z7,z0,z1,z361,z4,z6]),(0,[z7,z0,z1,z2,z4,z68,z148]),(0,[z7,z0,z585,z1,z2,z4,z6]),(0,[z7,z188,z48,z1,z2,z4,z6]),(0,[z7,z586,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z587]),(0,[z7,z0,z1,z2,z171,z4,z182])],[(0,[z50,z7,z0,z1,z478,z4,z6]),(0,[z7,z0,z132,z26,z2,z4,z6]),(0,[z34,z45,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z588,z6]),(0,[z7,z0,z1,z2,z4,z6,z589]),(0,[z590,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z591,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z148]),(0,[z7,z0,z41,z17,z1,z2,z4]),(0,[z7,z0,z1,z2,z592,z4,z6])],[(0,[z31,z7,z0,z1,z164,z4,z6]),(0,[z7,z0,z121,z1,z2,z4,z6]),(1,[z0,z1,z88,z19,z4,z6]),(0,[z7,z160,z0,z1,z88,z4,z6]),(0,[z34,z7,z0,z1,z2,z4,z32]),(0,[z7,z0,z1,z593,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z181,z4]),(0,[z7,z0,z1,z2,z171,z4,z59])],[(0,[z7,z0,z1,z2,z4,z6,z298]),(0,[z7,z0,z17,z18,z2,z4,z6]),(0,[z34,z7,z0,z1,z19,z4,z6]),(0,[z7,z0,z1,z88,z4,z60,z6])],[(0,[z7,z0,z1,z2,z4,z594,z6]),(0,[z7,z0,z18,z1,z2,z4,z6]),(0,[z34,z7,z160,z0,z1,z2,z6]),(0,[z45,z0,z1,z2,z3,z4,z6]),(0,[z7,z90,z0,z2,z4,z172,z6]),(0,[z7,z0,z41,z1,z20,z4,z6]),(0,[z7,z0,z1,z30,z2,z39,z6])]],
   [[(0,[z7,z0,z1,z2,z4,z595,z6]),(0,[z7,z134,z0,z1,z2,z4,z6]),(0,[z7,z196,z1,z2,z4,z6,z148]),(0,[z7,z0,z476,z1,z2,z4,z6]),(0,[z7,z0,z96,z51,z1,z2,z4])],[(0,[z7,z0,z1,z2,z352,z4,z6]),(0,[z7,z0,z1,z19,z4,z59,z6]),(0,[z7,z0,z1,z2,z4,z6,z596])],[(0,[z7,z0,z1,z19,z4,z194,z6]),(0,[z597,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z598,z2,z4,z6]),(1,[z7,z90,z0,z17,z2,z4]),(0,[z7,z0,z599,z1,z2,z4,z6]),(0,[z7,z0,z41,z1,z39,z4,z6]),(0,[z7,z0,z1,z2,z171,z181,z6])],[(0,[z7,z0,z1,z228,z19,z4,z6]),(0,[z45,z7,z0,z1,z100,z4,z6]),(0,[z7,z0,z600,z1,z2,z4,z6]),(0,[z601,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z4,z6])],[(0,[z7,z0,z1,z19,z313,z4,z6]),(1,[z7,z0,z248,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z602,z6]),(0,[z7,z0,z56,z1,z27,z4,z6]),(1,[z7,z0,z17,z27,z2,z4]),(0,[z7,z0,z17,z27,z2,z4,z6]),(0,[z7,z0,z79,z1,z2,z4,z6]),(0,[z603,z7,z0,z1,z2,z4,z6])],[(0,[z7,z0,z604,z1,z2,z4,z6]),(0,[z7,z188,z0,z17,z1,z2,z4]),(0,[z7,z0,z605,z1,z2,z4,z6])],[(0,[z606,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z26,z88,z4,z6]),(0,[z7,z0,z1,z88,z4,z35,z6]),(0,[z7,z0,z248,z1,z26,z2,z4]),(0,[z7,z0,z1,z214,z2,z4,z223])],[(0,[z31,z7,z0,z1,z88,z4,z6]),(0,[z7,z0,z1,z2,z4,z607,z6]),(0,[z7,z0,z608,z1,z2,z4,z6])]],
   [[(0,[z7,z0,z609,z1,z2,z4,z6]),(0,[z610,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z611,z1,z2,z4,z6])],[(1,[z7,z379,z0,z1,z2,z6]),(0,[z7,z0,z1,z2,z4,z6,z612]),(0,[z7,z196,z0,z51,z1,z2,z4]),(0,[z7,z0,z56,z1,z2,z4,z6]),(0,[z7,z0,z41,z2,z20,z4,z6]),(0,[z7,z0,z179,z2,z4,z6,z223])],[(0,[z7,z613,z0,z1,z2,z4,z6]),(0,[z7,z0,z614,z1,z2,z4,z6]),(0,[z7,z0,z56,z27,z2,z4,z6]),(0,[z615,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z616,z6])],[(0,[z7,z0,z1,z2,z4,z6,z617]),(0,[z7,z0,z1,z2,z4,z66,z6]),(0,[z7,z0,z1,z2,z4,z6,z618]),(0,[z7,z0,z619,z1,z2,z4,z6]),(0,[z7,z0,z96,z1,z2,z194,z6])],[(0,[z7,z0,z620,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z621,z6]),(0,[z7,z0,z1,z622,z2,z4,z6])],[(0,[z7,z0,z17,z132,z2,z4,z6]),(0,[z7,z7,z0,z1,z88,z4,z6]),(0,[z7,z0,z1,z88,z181,z4,z6]),(0,[z7,z0,z1,z88,z4,z6,z182]),(0,[z45,z7,z0,z1,z2,z181,z6]),(0,[z187,z7,z0,z1,z2,z4,z68]),(0,[z7,z188,z0,z51,z1,z2,z4]),(1,[z7,z0,z1,z214,z4,z219])],[(0,[z623,z7,z0,z1,z2,z4,z6]),(0,[z624,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z625,z4,z6]),(0,[z626,z7,z0,z1,z2,z4,z6])],[(0,[z7,z0,z12,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z627,z4,z6]),(1,[z7,z0,z1,z2,z4,z213]),(0,[z7,z0,z17,z1,z2,z19,z4])]],
   [[(0,[z7,z0,z1,z88,z19,z4,z6]),(0,[z7,z0,z628,z1,z2,z4,z6]),(0,[z187,z0,z1,z2,z4,z6,z68]),(0,[z629,z7,z0,z1,z2,z4,z6]),(0,[z7,z630,z0,z1,z2,z4,z6]),(0,[z631,z7,z0,z1,z2,z4,z6])],[(1,[z7,z188,z1,z147,z4,z6]),(0,[z7,z48,z0,z1,z4,z219,z6]),(0,[z7,z0,z1,z632,z2,z4,z6]),(0,[z7,z0,z1,z633,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z634,z6])],[(0,[z7,z0,z1,z99,z88,z4,z6]),(0,[z34,z7,z0,z1,z2,z181,z6]),(0,[z7,z0,z635,z1,z2,z4,z6]),(0,[z7,z134,z1,z2,z4,z67,z6]),(0,[z7,z636,z0,z1,z2,z4,z6])],[(0,[z262,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z637,z1,z2,z4,z6]),(1,[z7,z0,z76,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z60,z148]),(0,[z7,z0,z638,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z639,z4,z6]),(1,[z7,z0,z1,z2,z477,z4]),(0,[z7,z373,z0,z51,z1,z2,z4]),(0,[z7,z0,z51,z1,z2,z4,z22])],[(0,[z7,z640,z0,z1,z2,z4,z6]),(0,[z52,z7,z0,z18,z2,z4,z6]),(0,[z641,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z109,z1,z88,z4,z6]),(0,[z642,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z28,z2,z4,z35,z6]),(0,[z7,z0,z1,z2,z643,z4,z6])],[(0,[z7,z0,z644,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z3,z194,z6]),(0,[z7,z645,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z646,z2,z4,z6]),(1,[z7,z0,z1,z2,z171,z59])],[(0,[z7,z127,z1,z2,z4,z194,z6]),(0,[z7,z0,z1,z88,z4,z172,z6]),(0,[z7,z0,z647,z1,z2,z4,z6]),(0,[z7,z0,z1,z648,z2,z4,z6]),(0,[z7,z0,z51,z1,z2,z4,z219])],[(1,[z7,z0,z1,z271,z4,z6]),(0,[z7,z0,z1,z2,z649,z4,z6]),(1,[z7,z0,z1,z2,z277,z6]),(0,[z386,z7,z0,z51,z1,z2,z4]),(0,[z7,z0,z151,z1,z214,z4,z6])]],
   [[(0,[z7,z0,z1,z88,z4,z6,z223]),(0,[z7,z0,z51,z1,z2,z4,z148]),(0,[z7,z650,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z651,z6])],[(0,[z7,z0,z0,z1,z2,z4,z6]),(0,[z52,z7,z0,z1,z2,z4,z6]),(0,[z45,z7,z0,z51,z1,z2,z4]),(0,[z652,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z51,z1,z2,z181,z4]),(0,[z7,z0,z573,z17,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z653,z6])],[(1,[z7,z0,z1,z478,z4,z6]),(0,[z7,z0,z1,z2,z654,z4,z6]),(0,[z7,z0,z1,z2,z655,z4,z6])],[(0,[z7,z0,z73,z1,z2,z4,z6]),(0,[z7,z126,z1,z2,z97,z4,z6])],[(0,[z31,z7,z0,z1,z2,z4,z213]),(0,[z7,z0,z1,z19,z4,z5,z6]),(0,[z7,z61,z1,z26,z2,z4,z6]),(0,[z7,z0,z656,z1,z2,z4,z6])],[],[(0,[z657,z7,z0,z1,z2,z4,z6]),(0,[z34,z7,z0,z51,z1,z2,z4])],[(0,[z658,z7,z0,z1,z2,z4,z6]),(1,[z84,z127,z1,z2,z4,z6]),(0,[z7,z0,z1,z411,z2,z4,z6]),(0,[z7,z0,z1,z2,z659,z4,z6]),(0,[z7,z0,z51,z1,z2,z3,z4]),(0,[z7,z90,z62,z1,z2,z4,z6]),(0,[z7,z48,z0,z151,z1,z4,z6]),(0,[z7,z0,z660,z1,z2,z4,z6]),(0,[z7,z0,z17,z168,z1,z2,z4]),(0,[z7,z0,z17,z2,z4,z6,z29]),(0,[z7,z0,z2,z4,z172,z6,z29]),(0,[z7,z0,z1,z661,z2,z4,z6]),(0,[z7,z0,z662,z1,z2,z4,z6])]],
   [[(0,[z50,z7,z0,z1,z2,z4,z43]),(0,[z7,z0,z663,z1,z2,z4,z6]),(0,[z7,z0,z1,z664,z2,z4,z6]),(1,[z7,z0,z1,z2,z69,z6]),(0,[z7,z61,z0,z17,z1,z2,z4]),(0,[z7,z0,z96,z1,z2,z97,z6]),(0,[z408,z7,z0,z51,z1,z2,z4])],[(1,[z187,z0,z1,z2,z4,z68]),(0,[z7,z0,z104,z1,z2,z4,z6]),(1,[z7,z0,z56,z27,z4,z6]),(0,[z7,z0,z131,z1,z2,z4,z6]),(0,[z665,z7,z0,z1,z2,z4,z6])],[(0,[z7,z666,z0,z1,z2,z4,z6]),(0,[z7,z188,z0,z56,z1,z4,z6]),(0,[z7,z48,z0,z17,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z6,z667]),(0,[z7,z0,z1,z2,z4,z532,z35]),(1,[z7,z0,z17,z51,z2,z4])],[(0,[z7,z330,z0,z1,z19,z4,z6]),(0,[z7,z0,z96,z1,z19,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z359]),(0,[z7,z0,z1,z2,z181,z4,z284]),(0,[z7,z0,z431,z17,z1,z2,z4]),(0,[z7,z0,z1,z30,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z668,z6]),(0,[z7,z669,z0,z1,z2,z4,z6])],[(0,[z84,z7,z0,z1,z303,z4,z6]),(0,[z7,z0,z1,z81,z2,z4,z6]),(0,[z7,z188,z1,z2,z147,z4,z6]),(0,[z7,z417,z0,z51,z1,z2,z4])],[(1,[z7,z0,z1,z2,z93,z6]),(1,[z7,z196,z1,z2,z4,z148]),(0,[z7,z0,z670,z1,z2,z4,z6]),(0,[z7,z0,z1,z671,z2,z4,z6]),(1,[z7,z0,z1,z2,z4,z532]),(0,[z7,z0,z17,z1,z2,z4,z29])],[(0,[z127,z0,z12,z1,z2,z4,z6]),(0,[z7,z0,z1,z19,z4,z219,z6]),(0,[z7,z672,z0,z1,z2,z4,z6]),(0,[z7,z0,z673,z1,z2,z4,z6]),(1,[z7,z0,z1,z2,z102,z6]),(0,[z7,z0,z1,z674,z2,z4,z6]),(0,[z7,z134,z0,z17,z1,z2,z4])],[(0,[z7,z0,z41,z1,z19,z4,z6]),(0,[z7,z0,z1,z19,z4,z6,z223]),(0,[z7,z0,z1,z2,z4,z675,z6]),(0,[z7,z0,z1,z676,z2,z4,z6])]],
   [[(0,[z7,z0,z1,z2,z392,z4,z6]),(0,[z7,z0,z677,z1,z2,z4,z6])],[(0,[z7,z0,z1,z2,z4,z678,z6]),(0,[z7,z379,z0,z1,z2,z4,z6]),(0,[z7,z679,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z680]),(0,[z75,z7,z0,z1,z88,z4,z6]),(0,[z341,z7,z0,z1,z2,z4,z6]),(0,[z681,z7,z0,z1,z2,z4,z6]),(1,[z7,z0,z1,z2,z4,z284]),(0,[z7,z0,z1,z2,z181,z4,z371]),(0,[z7,z0,z17,z17,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z682,z6]),(0,[z683,z7,z0,z1,z2,z4,z6])],[(0,[z7,z0,z684,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z685,z6]),(0,[z7,z0,z168,z1,z88,z4,z6]),(0,[z7,z48,z0,z51,z1,z2,z4]),(0,[z7,z0,z686,z1,z2,z4,z6]),(0,[z7,z0,z1,z687,z2,z4,z6]),(0,[z603,z7,z0,z17,z1,z2,z4])],[(0,[z7,z0,z51,z1,z2,z19,z4]),(0,[z7,z0,z1,z688,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z67,z6])],[(0,[z7,z0,z1,z132,z19,z4,z6]),(0,[z7,z689,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z508,z19,z4,z6]),(0,[z690,z7,z0,z1,z2,z4,z6]),(1,[z45,z0,z1,z2,z3,z6]),(0,[z7,z0,z1,z2,z171,z35,z6]),(0,[z7,z0,z1,z2,z4,z6,z691])],[(0,[z84,z7,z127,z1,z2,z4,z6]),(0,[z7,z0,z692,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z6,z693]),(1,[z7,z0,z1,z2,z4,z340])],[(0,[z7,z127,z0,z1,z88,z4,z6]),(0,[z7,z0,z62,z1,z19,z4,z6]),(1,[z7,z0,z365,z2,z4,z6]),(0,[z7,z134,z0,z51,z1,z2,z4]),(1,[z7,z0,z17,z168,z2,z4])],[(1,[z7,z0,z1,z2,z4,z6]),(0,[z34,z7,z0,z1,z411,z4,z6]),(1,[z7,z0,z1,z2,z4,z371]),(0,[z7,z0,z17,z86,z1,z2,z4]),(0,[z7,z0,z51,z1,z2,z4,z372]),(0,[z7,z0,z1,z2,z694,z4,z6])]],
   [[(0,[z7,z188,z0,z1,z19,z4,z6]),(1,[z7,z0,z1,z2,z4,z94]),(0,[z7,z0,z151,z1,z2,z4,z6])],[(0,[z7,z0,z695,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z696,z4,z6]),(0,[z7,z126,z0,z1,z88,z4,z6]),(0,[z75,z7,z0,z1,z2,z4,z68]),(0,[z7,z0,z376,z1,z2,z4,z6]),(0,[z7,z0,z1,z697,z2,z4,z6]),(0,[z7,z0,z2,z4,z35,z172,z6]),(0,[z7,z0,z17,z51,z1,z2,z4]),(0,[z7,z0,z17,z1,z2,z39,z4]),(0,[z7,z0,z1,z2,z4,z698,z6])],[(0,[z7,z0,z106,z1,z2,z4,z6]),(0,[z7,z699,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z700,z4,z6])],[(0,[z7,z701,z0,z1,z2,z4,z6]),(0,[z7,z0,z51,z584,z1,z2,z4]),(0,[z7,z0,z51,z1,z632,z2,z4])],[(0,[z702,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z88,z4,z6,z133]),(0,[z7,z0,z1,z2,z703,z4,z6]),(0,[z7,z0,z1,z2,z181,z97,z6])],[(0,[z7,z0,z12,z17,z1,z2,z4]),(0,[z7,z0,z388,z1,z2,z4,z6])],[(0,[z704,z7,z0,z1,z2,z4,z6])],[(0,[z50,z7,z0,z17,z1,z2,z4]),(0,[z31,z7,z0,z18,z2,z4,z6]),(0,[z221,z7,z0,z1,z88,z4,z6]),(0,[z7,z0,z87,z1,z2,z4,z6]),(0,[z705,z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z706,z1,z2,z4,z6]),(0,[z7,z0,z41,z2,z4,z172,z6]),(0,[z7,z0,z86,z1,z2,z171,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z0,z707,z186,z2,z4]),(0,[z7,z0,z707,z1,z2,z4]),(0,[z0,z1,z2,z4,z708,z68]),(0,[z7,z0,z709,z1,z4,z6])],[(0,[z7,z0,z1,z710,z4,z6]),(0,[z7,z711,z1,z2,z4,z6]),(0,[z7,z1,z2,z4,z712,z6]),(0,[z7,z0,z41,z17,z2,z4])],[(0,[z7,z0,z1,z2,z713,z6]),(0,[z7,z0,z225,z17,z2,z4]),(0,[z7,z0,z51,z1,z2,z714])],[(0,[z7,z0,z17,z1,z19,z277]),(0,[z7,z0,z17,z648,z2,z4]),(0,[z7,z0,z17,z2,z4,z35])],[(0,[z84,z715,z1,z2,z4,z6]),(0,[z7,z90,z62,z19,z4,z6]),(0,[z34,z138,z1,z2,z5,z6]),(0,[z7,z61,z0,z17,z2,z69]),(0,[z7,z0,z1,z2,z171,z59])],[(0,[z7,z0,z81,z19,z4,z6]),(0,[z7,z61,z26,z19,z4,z6]),(0,[z7,z0,z1,z19,z4,z716]),(0,[z7,z0,z1,z19,z717,z6]),(0,[z7,z0,z1,z165,z2,z6])],[(0,[z7,z0,z1,z2,z718,z6]),(0,[z7,z0,z1,z2,z277,z6]),(0,[z7,z0,z201,z1,z162,z4])],[(0,[z7,z0,z1,z719,z4,z6]),(0,[z7,z0,z17,z2,z395,z4]),(0,[z7,z0,z51,z2,z643,z4])],[(0,[z7,z0,z79,z132,z2,z4])],[(0,[z7,z720,z0,z1,z2,z6])],[(0,[z7,z0,z51,z1,z2,z93]),(0,[z7,z11,z0,z51,z1,z2]),(0,[z7,z0,z1,z2,z721,z6]),(0,[z7,z0,z4,z116,z14,z6])],[(0,[z7,z0,z722,z2,z4,z6])],[],[(0,[z7,z0,z1,z165,z313,z6]),(0,[z540,z0,z1,z88,z4,z6]),(0,[z7,z0,z1,z723,z4,z6]),(0,[z75,z0,z1,z77,z4,z60]),(0,[z7,z0,z17,z1,z30,z39])],[(0,[z84,z127,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z724]),(0,[z7,z0,z56,z27,z4,z340]),(0,[z7,z0,z28,z2,z725,z6])],[(0,[z7,z0,z17,z27,z19,z4]),(0,[z7,z0,z17,z1,z205,z4]),(0,[z7,z0,z1,z2,z69,z6]),(0,[z7,z0,z51,z1,z2,z726])]],
   [[(0,[z7,z0,z1,z119,z4,z6]),(0,[z7,z160,z1,z19,z194,z6]),(0,[z7,z0,z56,z27,z4,z6])],[(0,[z7,z0,z1,z2,z325,z298]),(0,[z7,z0,z17,z76,z2,z4]),(0,[z7,z0,z153,z88,z4,z6]),(0,[z7,z0,z1,z727,z4,z6]),(0,[z7,z0,z151,z4,z123,z223])],[(0,[z7,z0,z17,z132,z2,z277]),(0,[z7,z0,z728,z2,z4,z6]),(0,[z7,z556,z0,z17,z2,z4]),(0,[z7,z0,z17,z56,z27,z4]),(0,[z7,z0,z1,z2,z725,z6])],[(0,[z7,z0,z86,z1,z2,z182])],[(0,[z7,z0,z729,z1,z2,z4]),(0,[z7,z0,z1,z730,z4,z6]),(0,[z7,z61,z90,z17,z2,z4]),(0,[z7,z0,z731,z2,z4,z6])],[(0,[z50,z12,z1,z19,z4,z6]),(0,[z7,z0,z1,z2,z732,z6]),(0,[z7,z373,z584,z1,z2,z4])],[(0,[z7,z0,z246,z20,z4,z6]),(0,[z7,z0,z1,z2,z4,z733])],[(0,[z7,z0,z734,z1,z4,z6])],[(0,[z7,z0,z1,z2,z4,z735]),(0,[z7,z0,z1,z478,z4,z43]),(0,[z7,z48,z1,z49,z4,z6]),(0,[z7,z0,z318,z153,z4,z6]),(0,[z7,z0,z211,z17,z4,z6]),(0,[z7,z0,z17,z2,z4,z372]),(0,[z7,z0,z201,z179,z2,z4])],[(0,[z7,z0,z153,z2,z4,z68]),(0,[z7,z0,z1,z4,z532,z9])],[(0,[z7,z0,z1,z2,z4,z736]),(0,[z7,z0,z51,z56,z27,z4])],[(0,[z7,z0,z76,z77,z4,z6]),(0,[z7,z0,z318,z51,z1,z4])],[(0,[z7,z0,z1,z2,z4,z737]),(0,[z7,z515,z0,z17,z2,z4]),(0,[z34,z0,z1,z2,z5,z6]),(0,[z45,z0,z1,z2,z78,z6])],[(0,[z7,z0,z365,z2,z4,z6]),(0,[z7,z0,z17,z18,z88,z4]),(0,[z7,z138,z1,z2,z4,z33]),(0,[z7,z0,z1,z738,z4,z6])],[(0,[z7,z0,z1,z2,z4,z739]),(0,[z7,z196,z1,z4,z14,z148]),(0,[z7,z191,z0,z17,z2,z4]),(0,[z7,z0,z211,z4,z172,z6]),(0,[z7,z0,z105,z2,z277,z6])],[(0,[z7,z0,z1,z2,z80,z6]),(0,[z7,z0,z1,z2,z4,z740])]],
   [[(0,[z7,z0,z186,z2,z93,z6]),(0,[z7,z0,z168,z2,z181,z6]),(0,[z7,z417,z376,z1,z2,z4])],[(0,[z7,z0,z195,z2,z4,z298]),(0,[z45,z0,z1,z252,z3,z6])],[(0,[z7,z741,z1,z2,z4,z6]),(0,[z0,z1,z742,z19,z4,z6]),(0,[z45,z7,z0,z17,z2,z35]),(0,[z7,z0,z17,z495,z2,z4]),(1,[z7,z0,z2,z725,z6])],[],[(0,[z31,z0,z18,z2,z80,z6]),(0,[z7,z0,z1,z252,z4,z6]),(0,[z7,z0,z51,z81,z2,z4]),(0,[z7,z0,z17,z2,z4,z385])],[(0,[z7,z11,z106,z1,z2,z6]),(0,[z7,z90,z0,z17,z88,z4])],[(0,[z7,z0,z1,z743,z19,z4]),(0,[z705,z0,z1,z88,z4,z6]),(0,[z7,z0,z744,z2,z4,z6]),(0,[z745,z0,z1,z2,z4,z6]),(0,[z7,z0,z17,z2,z4,z547])],[(0,[z493,z0,z18,z2,z4,z6]),(0,[z144,z0,z1,z19,z4,z6]),(0,[z7,z0,z248,z1,z88,z4])],[(0,[z7,z0,z195,z2,z325,z6]),(0,[z7,z0,z1,z2,z746,z6]),(0,[z7,z0,z17,z2,z4,z553])],[(0,[z747,z0,z1,z2,z4,z6]),(0,[z7,z0,z476,z27,z2,z4]),(0,[z7,z0,z96,z1,z748,z6])],[(0,[z7,z0,z186,z2,z4,z6]),(0,[z34,z0,z1,z88,z5,z6]),(0,[z7,z0,z365,z2,z4,z32]),(0,[z7,z0,z17,z2,z4,z78])],[(0,[z0,z1,z19,z4,z653,z6]),(0,[z7,z0,z17,z317,z2,z4]),(0,[z7,z0,z1,z4,z219,z275]),(0,[z7,z0,z1,z30,z39,z6]),(1,[z7,z0,z1,z748,z6])],[(0,[z7,z379,z0,z1,z88,z6]),(0,[z7,z0,z1,z4,z6,z749]),(0,[z7,z0,z1,z2,z4,z42])],[(0,[z7,z0,z1,z750,z4,z6]),(0,[z7,z0,z1,z751,z4,z6]),(0,[z7,z0,z1,z2,z752,z6]),(0,[z7,z0,z17,z51,z19,z4]),(0,[z7,z0,z1,z88,z4,z753]),(0,[z7,z106,z1,z215,z4,z6]),(0,[z0,z1,z2,z4,z754,z6]),(0,[z0,z1,z2,z4,z708,z6])],[(0,[z7,z61,z0,z17,z2,z277]),(0,[z7,z0,z1,z4,z6,z755]),(0,[z7,z0,z1,z2,z4,z756]),(0,[z7,z0,z1,z2,z757,z4])],[(0,[z7,z0,z51,z1,z478,z4]),(0,[z7,z0,z758,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z759]),(0,[z7,z0,z41,z17,z2,z64])]],
   [[(0,[z7,z0,z760,z1,z19,z6]),(0,[z7,z0,z761,z1,z2,z4]),(0,[z479,z0,z73,z1,z2,z4])],[(0,[z7,z0,z1,z164,z4,z278])],[(0,[z7,z0,z1,z2,z4,z762]),(0,[z527,z127,z1,z2,z4,z6]),(0,[z31,z0,z18,z2,z4,z278])],[(0,[z7,z763,z1,z2,z4,z6]),(0,[z7,z0,z1,z4,z764,z6]),(0,[z7,z0,z765,z2,z4,z6])],[(0,[z84,z127,z17,z1,z2,z4]),(0,[z7,z0,z744,z88,z4,z6]),(0,[z7,z0,z1,z766,z4,z6])],[(0,[z50,z12,z51,z1,z2,z4]),(0,[z7,z0,z86,z1,z2,z64])],[(0,[z7,z0,z17,z120,z2,z4]),(0,[z7,z0,z81,z411,z4,z6]),(0,[z0,z1,z2,z4,z767,z6])],[(0,[z7,z0,z1,z77,z4,z6]),(0,[z0,z614,z1,z19,z4,z6]),(0,[z7,z768,z0,z17,z1,z4])],[(0,[z7,z0,z186,z88,z4,z6]),(0,[z7,z0,z1,z769,z4,z6])],[(0,[z7,z0,z770,z1,z2,z4]),(0,[z7,z0,z17,z168,z19,z4]),(0,[z7,z0,z1,z88,z117,z6]),(0,[z7,z0,z17,z305,z2,z4])],[(0,[z7,z330,z1,z147,z4,z6]),(0,[z7,z0,z771,z2,z4,z6])],[(0,[z7,z0,z1,z88,z4,z278]),(0,[z7,z0,z1,z772,z4,z6]),(0,[z7,z0,z1,z2,z4,z773])],[],[(0,[z7,z0,z1,z2,z6,z774]),(0,[z7,z0,z17,z2,z4,z473]),(0,[z7,z61,z17,z26,z2,z4]),(0,[z7,z0,z17,z2,z4,z536])],[(0,[z0,z1,z2,z4,z60,z708])],[(0,[z7,z0,z1,z2,z775,z6]),(0,[z7,z0,z51,z1,z165,z2])]],
   [[(0,[z7,z0,z776,z1,z2,z4]),(0,[z7,z0,z388,z76,z2,z4])],[(0,[z0,z17,z18,z132,z2,z4])],[(0,[z7,z0,z17,z1,z119,z4]),(0,[z7,z0,z777,z2,z4,z6]),(0,[z7,z0,z1,z778,z4,z6]),(0,[z7,z0,z17,z1,z2,z779])],[(0,[z7,z0,z1,z88,z4,z33]),(0,[z516,z0,z1,z88,z4,z6]),(0,[z7,z0,z25,z77,z4,z6]),(0,[z7,z0,z1,z780,z4,z6]),(0,[z7,z0,z27,z778,z4,z6]),(0,[z7,z0,z17,z734,z1,z4]),(0,[z7,z0,z1,z30,z748,z6])],[(0,[z7,z0,z1,z352,z4,z6]),(0,[z7,z0,z236,z2,z4,z35]),(0,[z479,z0,z1,z19,z4,z6]),(0,[z7,z781,z1,z2,z4,z6]),(0,[z0,z1,z362,z88,z4,z6]),(0,[z0,z1,z521,z88,z4,z6]),(0,[z7,z106,z1,z2,z4,z32]),(0,[z7,z0,z17,z1,z782,z4]),(0,[z7,z0,z1,z4,z748,z6])],[(0,[z368,z0,z1,z19,z4,z6]),(0,[z7,z61,z51,z26,z2,z4]),(0,[z7,z0,z17,z328,z2,z4]),(0,[z7,z0,z495,z2,z35,z6]),(0,[z7,z0,z179,z2,z4,z148]),(0,[z7,z0,z783,z2,z4,z6])],[(0,[z7,z1,z2,z784,z4,z6]),(0,[z7,z0,z153,z2,z4,z6]),(0,[z7,z0,z1,z785,z4,z6]),(0,[z7,z188,z0,z786,z2,z4]),(0,[z7,z0,z17,z2,z4,z459]),(0,[z7,z0,z17,z670,z2,z4])],[(0,[z7,z0,z17,z195,z2,z4]),(0,[z7,z0,z1,z2,z93,z298]),(0,[z7,z0,z1,z787,z4,z6]),(0,[z7,z0,z158,z1,z4,z6]),(0,[z7,z0,z788,z2,z4,z6]),(0,[z7,z1,z49,z789,z4,z6])],[],[(0,[z7,z0,z790,z1,z19,z4]),(0,[z7,z0,z791,z1,z4,z6]),(0,[z7,z0,z1,z2,z4,z792])],[(0,[z7,z0,z51,z1,z119,z4]),(0,[z7,z0,z53,z121,z1,z6]),(0,[z0,z381,z1,z88,z4,z6])],[(0,[z7,z0,z1,z88,z384,z6]),(0,[z7,z0,z17,z1,z19,z64]),(0,[z7,z391,z0,z17,z2,z4])],[(0,[z7,z0,z96,z1,z215,z6]),(0,[z7,z793,z0,z1,z2,z6]),(0,[z7,z0,z1,z2,z4,z794]),(0,[z7,z0,z211,z1,z4,z532])],[(0,[z7,z0,z1,z326,z74,z6]),(0,[z7,z0,z1,z795,z4,z6])],[(0,[z7,z0,z1,z2,z4,z796])],[(0,[z7,z0,z51,z195,z2,z4]),(0,[z7,z0,z1,z19,z4,z213])]],
   [[(0,[z7,z0,z153,z4,z14,z6])],[(0,[z7,z0,z1,z2,z4,z298]),(0,[z464,z12,z1,z2,z4,z6]),(0,[z7,z0,z53,z1,z66,z6]),(0,[z7,z0,z17,z1,z252,z4]),(0,[z797,z0,z1,z2,z4,z6]),(0,[z7,z0,z17,z2,z97,z35])],[(0,[z7,z0,z1,z88,z798,z6]),(0,[z75,z0,z76,z2,z4,z60]),(0,[z7,z61,z175,z26,z4,z6]),(1,[z7,z0,z778,z4,z6])],[(0,[z7,z0,z1,z799,z4,z6]),(0,[z7,z800,z1,z2,z4,z6]),(0,[z0,z1,z19,z70,z4,z6]),(0,[z7,z0,z1,z19,z477,z4]),(0,[z7,z0,z17,z27,z2,z277])],[(0,[z7,z0,z1,z2,z801,z6]),(0,[z7,z0,z802,z2,z4,z6]),(0,[z7,z0,z17,z19,z4,z35]),(0,[z7,z0,z803,z2,z4,z6]),(0,[z7,z0,z1,z2,z804,z6])],[(0,[z7,z0,z1,z19,z171,z59]),(0,[z34,z0,z1,z215,z5,z6]),(0,[z7,z0,z179,z51,z2,z4])],[(0,[z7,z0,z365,z215,z4,z6]),(0,[z7,z173,z1,z2,z4,z67])],[(0,[z7,z0,z1,z805,z4,z6]),(0,[z7,z0,z1,z19,z277,z6]),(0,[z34,z0,z302,z1,z2,z6]),(0,[z7,z0,z1,z2,z4,z806]),(0,[z7,z160,z17,z1,z2,z194]),(0,[z7,z0,z1,z2,z6,z740])],[(0,[z7,z0,z186,z478,z4,z6]),(0,[z7,z0,z51,z1,z30,z39])],[(0,[z7,z0,z51,z1,z252,z4])],[(0,[z7,z0,z17,z132,z2,z64]),(0,[z7,z0,z51,z1,z205,z4]),(0,[z7,z0,z17,z1,z807,z4])],[(0,[z52,z0,z132,z2,z4,z6]),(0,[z7,z0,z1,z808,z4,z6]),(0,[z7,z0,z1,z809,z4,z6])],[(0,[z7,z0,z810,z1,z2,z4]),(0,[z7,z0,z51,z76,z2,z4])],[(0,[z7,z0,z17,z1,z271,z4]),(0,[z7,z0,z1,z2,z4,z811]),(0,[z7,z0,z1,z812,z4,z6]),(0,[z7,z106,z17,z1,z2,z4]),(0,[z75,z0,z288,z1,z2,z4]),(0,[z7,z0,z168,z2,z181,z284])],[(0,[z7,z0,z17,z441,z2,z4]),(0,[z7,z577,z0,z17,z2,z4]),(0,[z0,z1,z2,z4,z6,z813]),(0,[z7,z0,z1,z814,z4,z6])],[(0,[z7,z0,z1,z88,z4,z298]),(0,[z84,z127,z1,z19,z4,z6]),(0,[z7,z815,z1,z2,z4,z6]),(0,[z7,z0,z816,z1,z4,z6]),(0,[z7,z0,z1,z19,z4,z724]),(0,[z7,z0,z1,z817,z4,z6]),(0,[z7,z0,z105,z2,z171,z59])]],
   [[(0,[z7,z243,z0,z17,z2,z4]),(0,[z7,z0,z818,z1,z4,z6]),(0,[z7,z0,z168,z2,z384,z6]),(0,[z7,z0,z17,z1,z19,z4]),(0,[z7,z0,z1,z19,z69,z6]),(0,[z7,z0,z819,z1,z4,z6]),(0,[z7,z90,z820,z2,z4,z6]),(0,[z7,z0,z821,z1,z2,z4])],[(0,[z7,z0,z822,z1,z2,z4]),(0,[z7,z0,z823,z2,z4,z6]),(0,[z7,z0,z786,z2,z4,z6]),(0,[z7,z0,z1,z2,z171,z371]),(0,[z7,z824,z17,z1,z2,z4])],[(0,[z7,z0,z1,z2,z4,z753]),(0,[z7,z0,z786,z2,z4,z94]),(0,[z7,z0,z1,z2,z825,z6]),(0,[z7,z0,z17,z1,z826,z4]),(0,[z7,z0,z1,z2,z171,z740])],[(0,[z7,z0,z1,z4,z827,z6]),(0,[z7,z61,z26,z2,z177,z6])],[(0,[z7,z828,z1,z2,z4,z6]),(0,[z7,z0,z829,z1,z2,z4]),(0,[z7,z0,z1,z830,z4,z6]),(0,[z7,z134,z1,z2,z4,z712]),(0,[z7,z0,z17,z288,z2,z4]),(0,[z7,z0,z1,z2,z277,z182])],[(0,[z7,z0,z51,z1,z271,z4]),(0,[z7,z0,z1,z2,z384,z831]),(0,[z7,z196,z1,z19,z4,z148]),(0,[z7,z0,z1,z19,z4,z532]),(0,[z7,z1,z19,z4,z6,z832]),(0,[z7,z106,z51,z1,z2,z4]),(0,[z7,z0,z17,z365,z2,z4]),(0,[z7,z0,z51,z2,z4,z530])],[(0,[z7,z0,z1,z88,z325,z6]),(0,[z0,z1,z19,z146,z4,z6]),(0,[z7,z0,z1,z19,z102,z6]),(0,[z7,z0,z1,z30,z215,z6])],[(0,[z7,z188,z0,z41,z17,z4])],[(0,[z7,z0,z51,z1,z19,z4]),(0,[z7,z0,z53,z1,z88,z6]),(0,[z479,z0,z1,z2,z4,z60]),(0,[z7,z0,z17,z2,z64,z29])],[(0,[z52,z0,z132,z88,z4,z6]),(0,[z0,z605,z1,z88,z4,z6])],[(0,[z7,z0,z1,z2,z833,z6]),(0,[z50,z715,z1,z2,z4,z6]),(0,[z7,z0,z834,z1,z4,z6]),(0,[z7,z0,z53,z1,z215,z6]),(0,[z7,z0,z17,z1,z77,z4]),(0,[z7,z0,z17,z1,z2,z835])],[(0,[z7,z0,z18,z2,z4,z278]),(0,[z7,z0,z836,z1,z80,z6]),(0,[z221,z0,z1,z88,z4,z6]),(0,[z7,z0,z17,z329,z2,z4]),(0,[z7,z0,z17,z1,z411,z4]),(0,[z7,z0,z2,z837,z4,z6])],[(0,[z7,z0,z17,z18,z2,z80]),(0,[z465,z0,z1,z88,z4,z6]),(0,[z34,z0,z1,z2,z5,z32]),(0,[z7,z0,z1,z838,z4,z6]),(0,[z7,z90,z2,z4,z481,z6])],[(0,[z7,z0,z51,z365,z2,z4]),(0,[z7,z0,z839,z1,z2,z4])],[(0,[z7,z0,z1,z2,z840,z6]),(0,[z7,z0,z365,z19,z4,z6]),(0,[z7,z0,z1,z841,z4,z6]),(0,[z45,z0,z1,z2,z754,z6]),(0,[z7,z0,z1,z2,z117,z6]),(0,[z7,z0,z1,z2,z842,z4])],[(0,[z7,z0,z17,z108,z2,z4]),(0,[z7,z0,z1,z843,z2,z6]),(0,[z0,z1,z844,z2,z4,z6]),(0,[z7,z0,z17,z132,z2,z4]),(0,[z137,z0,z1,z742,z4,z6]),(0,[z7,z0,z1,z19,z4,z371]),(0,[z7,z196,z154,z1,z2,z4])]],
   [[(0,[z7,z0,z1,z2,z4,z278]),(0,[z7,z0,z318,z1,z4,z6]),(0,[z7,z0,z845,z1,z2,z4])],[(0,[z7,z0,z1,z846,z4,z6]),(0,[z7,z0,z17,z508,z2,z4]),(0,[z7,z0,z1,z2,z847,z6]),(0,[z7,z0,z318,z1,z4,z94]),(0,[z7,z482,z1,z2,z194,z6]),(0,[z7,z0,z17,z51,z2,z277])],[(0,[z7,z0,z1,z848,z4,z6]),(0,[z7,z0,z1,z843,z352,z6]),(0,[z7,z0,z17,z539,z2,z4])],[(0,[z7,z0,z51,z1,z411,z4]),(0,[z7,z0,z333,z51,z2,z4])],[(0,[z7,z0,z849,z2,z4,z6]),(0,[z7,z0,z1,z850,z4,z6]),(0,[z7,z0,z217,z1,z19,z4]),(0,[z7,z0,z1,z2,z4,z851]),(0,[z7,z0,z852,z2,z4,z6]),(0,[z7,z0,z28,z88,z35,z6])],[(0,[z7,z0,z1,z2,z4,z853]),(0,[z7,z0,z269,z132,z2,z4]),(0,[z7,z0,z2,z4,z854,z29])],[(0,[z7,z0,z195,z88,z4,z6]),(0,[z7,z106,z1,z411,z4,z6]),(0,[z7,z0,z96,z1,z100,z6]),(0,[z0,z1,z2,z3,z754,z6]),(0,[z7,z61,z0,z17,z2,z64]),(0,[z7,z0,z1,z855,z4,z6]),(0,[z7,z0,z1,z2,z856,z6]),(0,[z7,z0,z17,z676,z2,z4])],[(0,[z7,z0,z2,z171,z23,z59])],[(0,[z7,z0,z41,z17,z88,z4]),(0,[z7,z0,z1,z2,z4,z33]),(0,[z7,z857,z1,z2,z4,z6]),(0,[z7,z90,z17,z62,z2,z4]),(0,[z7,z0,z858,z1,z2,z4]),(0,[z7,z0,z17,z1,z2,z859])],[(0,[z7,z379,z0,z51,z1,z2]),(0,[z7,z0,z1,z4,z860,z6]),(0,[z7,z0,z28,z79,z2,z35]),(0,[z7,z800,z17,z1,z2,z4]),(0,[z7,z0,z17,z1,z2,z856])],[(0,[z7,z0,z132,z2,z4,z278]),(0,[z7,z0,z17,z1,z350,z4]),(0,[z7,z0,z17,z1,z2,z69]),(0,[z7,z0,z476,z1,z2,z4])],[(0,[z7,z0,z17,z19,z4,z29]),(0,[z7,z279,z1,z2,z194,z6]),(0,[z7,z0,z1,z2,z4,z861])],[(0,[z7,z0,z1,z2,z862,z6]),(0,[z7,z0,z1,z165,z88,z6]),(0,[z7,z0,z1,z19,z4,z36]),(0,[z128,z0,z1,z19,z4,z6]),(0,[z75,z0,z1,z88,z4,z60]),(0,[z7,z0,z41,z354,z4,z6])],[(0,[z493,z0,z1,z19,z4,z6]),(0,[z7,z0,z1,z19,z4,z42]),(0,[z7,z0,z863,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z864]),(0,[z7,z90,z62,z2,z4,z36]),(0,[z7,z0,z17,z168,z2,z277]),(0,[z7,z0,z17,z1,z838,z4])],[(0,[z7,z0,z1,z19,z4,z43]),(0,[z7,z0,z1,z2,z4,z865])],[(0,[z7,z0,z1,z478,z4,z298]),(0,[z84,z127,z51,z1,z2,z4]),(0,[z866,z0,z1,z2,z4,z6]),(0,[z7,z0,z201,z17,z2,z4])]],
   [[(0,[z7,z0,z1,z2,z384,z6]),(0,[z7,z0,z758,z19,z4,z6]),(0,[z7,z134,z0,z153,z2,z4])],[(0,[z7,z0,z1,z867,z4,z6]),(0,[z7,z188,z1,z147,z4,z189])],[(0,[z7,z0,z51,z1,z350,z4]),(0,[z7,z0,z51,z1,z2,z69]),(0,[z626,z7,z0,z17,z2,z4]),(0,[z7,z0,z41,z17,z39,z4])],[(0,[z7,z578,z0,z17,z2,z4]),(0,[z7,z0,z17,z168,z2,z35]),(0,[z7,z0,z1,z4,z865,z223])],[(0,[z75,z0,z1,z2,z4,z708]),(0,[z7,z0,z17,z2,z64,z35])],[(0,[z31,z0,z18,z2,z384,z6]),(0,[z137,z0,z53,z1,z19,z6]),(0,[z7,z373,z0,z17,z2,z4])],[(0,[z7,z0,z1,z478,z325,z6]),(0,[z7,z0,z868,z1,z2,z4]),(0,[z7,z0,z1,z19,z869,z4]),(0,[z7,z0,z1,z165,z39,z6]),(0,[z7,z0,z870,z1,z4,z6]),(0,[z7,z61,z269,z26,z2,z4]),(0,[z7,z0,z1,z2,z4,z871]),(0,[z7,z0,z17,z1,z4,z14]),(0,[z7,z0,z1,z2,z277,z64])],[(0,[z7,z0,z872,z1,z4,z6]),(0,[z7,z0,z1,z2,z798,z6])],[(0,[z7,z0,z1,z873,z4,z6]),(0,[z7,z106,z1,z19,z4,z6]),(0,[z7,z0,z1,z228,z4,z237]),(0,[z7,z61,z0,z17,z2,z177]),(0,[z7,z0,z1,z874,z4,z6])],[(0,[z7,z0,z17,z2,z171,z35]),(0,[z7,z0,z875,z2,z4,z6])],[(0,[z7,z0,z1,z2,z4,z876]),(0,[z7,z0,z76,z88,z4,z6]),(0,[z7,z0,z86,z1,z88,z182]),(0,[z7,z0,z17,z2,z4,z116])],[(0,[z7,z61,z0,z17,z2,z4]),(0,[z7,z877,z1,z2,z4,z6]),(0,[z7,z0,z17,z2,z4,z123])],[(0,[z7,z0,z2,z4,z172,z36])],[(0,[z7,z0,z246,z17,z19,z4]),(0,[z7,z0,z76,z2,z878,z6]),(0,[z7,z0,z1,z2,z879,z6]),(0,[z7,z0,z2,z4,z172,z42])],[(0,[z7,z0,z880,z1,z2,z4]),(0,[z7,z138,z1,z88,z4,z6]),(0,[z7,z0,z51,z1,z4,z14])],[(0,[z7,z0,z881,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z882]),(0,[z7,z0,z883,z1,z2,z4]),(1,[z7,z1,z789,z4,z6]),(0,[z7,z0,z211,z1,z194,z6])]],
   [[(0,[z7,z0,z1,z2,z6,z884]),(0,[z7,z0,z1,z2,z181,z32]),(0,[z7,z0,z1,z30,z100,z6]),(0,[z7,z445,z1,z2,z4,z148]),(0,[z7,z0,z17,z291,z2,z4]),(0,[z7,z0,z51,z1,z2,z885])],[(0,[z0,z715,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z886]),(0,[z7,z0,z1,z887,z4,z6])],[(0,[z7,z62,z820,z2,z4,z6]),(0,[z7,z0,z51,z2,z4,z116]),(0,[z747,z0,z17,z1,z2,z4])],[(0,[z7,z0,z1,z2,z4,z888]),(0,[z7,z0,z1,z2,z4,z889]),(0,[z7,z0,z890,z1,z4,z6]),(0,[z7,z1,z789,z147,z4,z6]),(0,[z7,z0,z51,z2,z4,z123])],[(0,[z7,z0,z17,z1,z164,z4]),(0,[z7,z0,z1,z350,z4,z213]),(0,[z7,z0,z1,z2,z4,z891]),(0,[z7,z0,z1,z892,z4,z6]),(0,[z7,z0,z318,z4,z116,z6])],[(0,[z7,z11,z1,z2,z194,z6]),(0,[z7,z0,z17,z1,z303,z4]),(0,[z210,z7,z0,z17,z2,z4]),(0,[z7,z61,z449,z17,z2,z4])],[],[(0,[z7,z0,z2,z4,z893,z6]),(0,[z7,z0,z1,z2,z4,z894]),(0,[z7,z0,z153,z19,z4,z6]),(0,[z0,z1,z2,z754,z5,z6]),(0,[z7,z0,z17,z1,z2,z117]),(0,[z7,z0,z1,z2,z4,z895]),(0,[z7,z0,z896,z1,z2,z4])],[(0,[z7,z0,z2,z4,z116,z6]),(0,[z7,z0,z1,z897,z4,z6])],[(0,[z52,z0,z844,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z898]),(0,[z7,z0,z1,z39,z369,z6]),(0,[z7,z0,z211,z17,z4,z35])],[(0,[z7,z0,z899,z1,z4,z6]),(0,[z7,z900,z1,z2,z4,z6]),(0,[z7,z0,z79,z1,z2,z4]),(0,[z7,z0,z104,z1,z301,z4]),(0,[z7,z0,z1,z2,z59,z740])],[(0,[z7,z0,z1,z2,z325,z6]),(0,[z7,z0,z1,z901,z4,z6]),(0,[z7,z0,z17,z27,z2,z64]),(0,[z7,z0,z105,z2,z181,z6])],[(0,[z7,z0,z1,z88,z93,z6]),(0,[z7,z0,z2,z4,z902,z6]),(0,[z7,z0,z903,z1,z2,z4]),(0,[z7,z0,z79,z1,z4,z9]),(0,[z7,z0,z573,z1,z2,z64])],[(0,[z7,z0,z1,z807,z4,z6]),(0,[z7,z0,z96,z1,z239,z6]),(0,[z7,z0,z2,z4,z6,z904]),(0,[z7,z905,z1,z2,z4,z6])],[(0,[z7,z0,z906,z2,z4,z6])],[(0,[z7,z0,z1,z2,z907,z6]),(0,[z7,z0,z365,z411,z4,z6]),(0,[z7,z90,z0,z269,z2,z4]),(0,[z7,z0,z51,z1,z2,z117])]],
   [[(0,[z7,z689,z26,z2,z4,z6]),(0,[z7,z0,z908,z1,z2,z4]),(0,[z7,z48,z507,z1,z4,z6]),(0,[z7,z196,z1,z2,z4,z712])],[(0,[z7,z0,z195,z2,z93,z6]),(0,[z7,z0,z909,z1,z2,z6]),(0,[z7,z0,z236,z1,z19,z4]),(0,[z31,z0,z18,z164,z4,z6]),(0,[z7,z910,z1,z2,z4,z6])],[(0,[z7,z106,z1,z2,z3,z6]),(0,[z7,z160,z51,z1,z2,z194])],[(0,[z7,z0,z17,z684,z2,z4]),(0,[z7,z0,z17,z132,z88,z4]),(0,[z45,z0,z1,z88,z3,z6]),(0,[z7,z0,z911,z1,z2,z4])],[(0,[z137,z0,z1,z19,z4,z6]),(0,[z7,z0,z121,z508,z4,z6]),(0,[z7,z0,z912,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z277])],[(0,[z7,z11,z0,z1,z19,z6]),(1,[z7,z0,z17,z2,z69]),(0,[z7,z0,z1,z2,z913,z6]),(0,[z7,z0,z1,z2,z914,z6]),(0,[z7,z0,z1,z4,z915,z6])],[(0,[z7,z0,z1,z88,z4,z6]),(0,[z0,z844,z132,z2,z4,z6]),(0,[z7,z0,z79,z1,z2,z182])],[(0,[z7,z0,z192,z152,z4,z6]),(0,[z7,z0,z1,z88,z4,z94]),(0,[z7,z0,z175,z269,z1,z4])],[(0,[z7,z0,z1,z916,z4,z6])],[(0,[z0,z1,z88,z19,z4,z6]),(0,[z7,z0,z269,z1,z19,z4]),(0,[z7,z0,z1,z2,z878,z6]),(0,[z7,z0,z17,z153,z2,z4]),(0,[z7,z0,z28,z2,z35,z6]),(0,[z7,z0,z917,z1,z4,z6]),(0,[z7,z0,z1,z2,z277,z59])],[(0,[z7,z0,z1,z2,z918,z6]),(0,[z7,z0,z1,z919,z4,z6]),(0,[z7,z0,z151,z1,z4,z223])],[(0,[z7,z0,z195,z2,z4,z6]),(0,[z31,z0,z18,z88,z4,z6])],[(0,[z50,z12,z1,z271,z4,z6]),(0,[z7,z0,z920,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z921]),(0,[z464,z0,z1,z19,z4,z6]),(0,[z7,z0,z922,z1,z19,z6]),(0,[z7,z0,z1,z923,z4,z6])],[],[(0,[z7,z0,z17,z451,z2,z4])],[(0,[z7,z0,z1,z924,z4,z6]),(0,[z7,z0,z153,z2,z4,z223]),(0,[z7,z0,z2,z4,z6,z854])]],
   [[(0,[z34,z0,z1,z19,z5,z6]),(0,[z7,z815,z1,z19,z4,z6]),(0,[z7,z0,z17,z27,z2,z4]),(0,[z7,z0,z17,z1,z925,z4])],[(0,[z7,z0,z1,z215,z4,z33]),(0,[z75,z0,z1,z2,z4,z60]),(0,[z7,z0,z17,z1,z2,z879])],[(0,[z7,z0,z25,z88,z4,z6]),(0,[z7,z0,z926,z1,z4,z6]),(0,[z603,z7,z0,z1,z2,z277])],[(0,[z7,z0,z1,z2,z4,z927]),(0,[z7,z0,z1,z19,z80,z6])],[(0,[z7,z0,z1,z2,z4,z928]),(0,[z7,z0,z168,z19,z181,z6]),(0,[z7,z0,z17,z54,z2,z4])],[(0,[z7,z828,z1,z19,z4,z6]),(0,[z7,z0,z53,z51,z1,z2]),(0,[z7,z0,z51,z1,z77,z4]),(0,[z7,z1,z2,z913,z194,z6]),(0,[z7,z0,z41,z17,z185,z4]),(0,[z7,z0,z1,z2,z4,z854])],[(0,[z7,z0,z17,z2,z69,z6]),(0,[z7,z0,z929,z1,z4,z6]),(0,[z930,z0,z1,z2,z4,z6]),(0,[z7,z0,z86,z1,z2,z740])],[(0,[z0,z1,z88,z742,z4,z6])],[(0,[z7,z126,z1,z2,z913,z6])],[(0,[z7,z0,z931,z2,z4,z6]),(0,[z7,z138,z1,z215,z4,z6]),(0,[z7,z0,z17,z51,z2,z64]),(0,[z7,z0,z51,z1,z932,z4])],[(0,[z7,z0,z1,z933,z4,z6]),(0,[z7,z0,z934,z1,z4,z6]),(0,[z7,z0,z1,z2,z35,z32]),(0,[z7,z0,z1,z4,z935,z6])],[(0,[z7,z0,z1,z303,z4,z6]),(0,[z7,z0,z1,z936,z4,z6]),(0,[z482,z0,z1,z19,z4,z6]),(0,[z45,z351,z0,z1,z2,z6]),(0,[z7,z0,z153,z2,z4,z60]),(0,[z7,z0,z17,z2,z4,z532]),(0,[z7,z0,z17,z105,z2,z277])],[(0,[z7,z0,z937,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z938])],[(0,[z7,z0,z1,z2,z4,z939]),(0,[z75,z0,z25,z2,z4,z60]),(0,[z940,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z941])],[(0,[z7,z0,z186,z19,z4,z6]),(0,[z479,z0,z17,z18,z2,z4]),(0,[z7,z942,z1,z2,z4,z6]),(0,[z7,z0,z1,z4,z9,z6]),(0,[z7,z0,z211,z51,z1,z4])],[(0,[z7,z0,z76,z2,z4,z6]),(0,[z7,z0,z1,z2,z943,z6]),(0,[z7,z0,z1,z19,z117,z6])]],
   [[(0,[z7,z0,z1,z2,z4,z831]),(0,[z7,z501,z1,z44,z4,z6]),(0,[z7,z0,z17,z1,z361,z4])],[(0,[z7,z0,z1,z19,z4,z278]),(0,[z7,z0,z1,z2,z384,z944]),(0,[z34,z7,z0,z17,z2,z35]),(0,[z7,z0,z175,z51,z1,z4])],[(0,[z7,z679,z0,z17,z2,z4]),(0,[z7,z0,z1,z88,z4,z115]),(0,[z7,z0,z88,z4,z6,z123])],[(0,[z7,z138,z1,z2,z4,z6]),(0,[z7,z0,z1,z945,z19,z6]),(0,[z339,z7,z0,z17,z2,z4]),(0,[z7,z0,z17,z560,z2,z4])],[(0,[z7,z0,z946,z132,z2,z4]),(0,[z7,z0,z1,z947,z4,z6]),(0,[z7,z188,z17,z1,z147,z4]),(0,[z7,z0,z153,z2,z948,z6])],[(0,[z7,z0,z949,z1,z2,z4]),(0,[z7,z0,z950,z2,z4,z6]),(0,[z7,z0,z1,z951,z4,z6]),(0,[z7,z0,z1,z952,z4,z6]),(0,[z7,z0,z953,z1,z2,z4]),(0,[z7,z0,z954,z1,z4,z6]),(0,[z7,z0,z1,z2,z859,z6]),(0,[z7,z0,z17,z168,z2,z64]),(1,[z7,z0,z2,z4,z854]),(0,[z7,z0,z96,z51,z1,z22])],[(0,[z7,z0,z1,z2,z4,z955]),(0,[z7,z0,z1,z956,z4,z6]),(0,[z7,z0,z1,z2,z4,z957]),(0,[z7,z0,z41,z347,z4,z6])],[(0,[z7,z12,z1,z2,z93,z6])],[(0,[z7,z0,z17,z563,z2,z4]),(0,[z7,z0,z51,z1,z361,z4]),(0,[z7,z0,z79,z1,z2,z64])],[(0,[z7,z0,z1,z2,z958,z6]),(0,[z50,z11,z12,z1,z2,z6]),(0,[z7,z0,z1,z19,z4,z33]),(0,[z7,z0,z1,z959,z4,z6])],[(0,[z7,z0,z960,z1,z2,z4]),(0,[z34,z0,z1,z2,z754,z6])],[(0,[z961,z0,z1,z2,z4,z6]),(0,[z7,z0,z474,z17,z2,z4])],[(0,[z7,z126,z579,z1,z2,z6]),(0,[z7,z188,z51,z1,z147,z4]),(0,[z7,z0,z2,z4,z962,z6])],[(0,[z7,z0,z17,z1,z392,z4]),(0,[z7,z0,z53,z1,z30,z6]),(0,[z7,z106,z81,z2,z4,z6]),(0,[z34,z482,z0,z1,z2,z6]),(0,[z7,z0,z17,z158,z1,z4]),(0,[z7,z0,z17,z428,z2,z4]),(0,[z7,z0,z1,z2,z4,z963])],[(0,[z7,z964,z1,z2,z4,z6]),(0,[z7,z0,z17,z51,z2,z4])],[(0,[z7,z0,z965,z1,z2,z4]),(0,[z7,z0,z1,z2,z966,z6])]],
   [[(0,[z0,z17,z220,z18,z2,z4]),(0,[z7,z138,z1,z2,z4,z32]),(0,[z7,z0,z17,z130,z2,z64])],[(0,[z7,z0,z1,z2,z93,z6]),(0,[z7,z0,z760,z1,z2,z6]),(0,[z7,z0,z1,z19,z6,z774]),(0,[z7,z0,z19,z4,z6,z123]),(0,[z7,z0,z1,z2,z4,z967]),(0,[z187,z0,z1,z361,z4,z68]),(0,[z7,z0,z1,z2,z4,z968])],[(0,[z7,z0,z17,z2,z4,z36]),(0,[z7,z0,z153,z2,z969,z6])],[(0,[z50,z12,z1,z2,z4,z43]),(0,[z7,z0,z269,z158,z1,z4]),(0,[z7,z0,z970,z2,z4,z6]),(0,[z7,z0,z17,z2,z4,z42])],[(0,[z7,z0,z179,z88,z4,z6]),(0,[z7,z0,z41,z17,z27,z4])],[(0,[z7,z98,z1,z113,z4,z6]),(0,[z7,z0,z76,z2,z4,z68]),(0,[z7,z0,z51,z158,z1,z4]),(0,[z7,z0,z1,z2,z4,z284]),(0,[z7,z0,z1,z4,z6,z971])],[(0,[z7,z0,z246,z53,z1,z6]),(0,[z7,z0,z777,z19,z4,z6]),(0,[z7,z0,z1,z4,z219,z865])],[(0,[z0,z1,z19,z4,z6,z456]),(0,[z7,z0,z1,z972,z4,z6]),(0,[z7,z0,z1,z2,z4,z973])],[(0,[z7,z0,z1,z2,z4,z974]),(0,[z615,z0,z1,z19,z4,z6]),(0,[z45,z0,z1,z2,z3,z6]),(0,[z7,z0,z1,z2,z4,z975]),(0,[z7,z0,z17,z403,z2,z4])],[(0,[z7,z0,z195,z478,z4,z6]),(0,[z7,z0,z17,z387,z2,z4]),(0,[z7,z48,z17,z1,z49,z4])],[(0,[z7,z0,z53,z56,z1,z6]),(0,[z7,z0,z17,z168,z2,z4])],[(0,[z7,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z976,z4,z6]),(0,[z127,z715,z1,z2,z4,z6]),(0,[z7,z0,z1,z977,z4,z6]),(0,[z187,z0,z1,z88,z4,z68]),(0,[z7,z0,z17,z145,z2,z4])],[(0,[z7,z0,z1,z2,z4,z978]),(0,[z137,z0,z1,z165,z19,z6]),(0,[z7,z0,z1,z2,z4,z94])],[(0,[z7,z0,z17,z2,z4,z80]),(0,[z7,z0,z1,z979,z4,z6])],[(0,[z7,z0,z17,z2,z980,z4])],[(0,[z7,z0,z981,z1,z4,z6]),(0,[z7,z0,z1,z164,z4,z6]),(0,[z7,z0,z51,z1,z164,z4]),(0,[z7,z0,z1,z982,z4,z6]),(0,[z7,z0,z1,z2,z4,z983]),(0,[z7,z0,z1,z361,z4,z6]),(0,[z7,z0,z1,z99,z4,z458]),(0,[z7,z0,z984,z1,z2,z4])]],
   [[(0,[z7,z0,z51,z1,z303,z4]),(0,[z31,z0,z18,z2,z4,z6]),(0,[z0,z18,z844,z2,z4,z6]),(0,[z7,z0,z179,z214,z2,z4])],[(0,[z34,z0,z1,z411,z5,z6]),(0,[z183,z7,z0,z17,z2,z4]),(0,[z7,z48,z51,z1,z49,z4])],[(0,[z7,z0,z56,z4,z203,z6])],[(0,[z7,z0,z1,z88,z4,z284])],[(0,[z7,z0,z1,z2,z985,z6]),(0,[z7,z0,z2,z384,z35,z6]),(0,[z7,z0,z17,z1,z260,z4]),(0,[z7,z0,z41,z778,z4,z6]),(0,[z7,z0,z17,z471,z2,z4]),(0,[z7,z0,z986,z1,z2,z4])],[(0,[z7,z0,z1,z2,z4,z987]),(0,[z7,z0,z1,z19,z4,z298]),(0,[z7,z0,z1,z2,z988,z6]),(0,[z7,z0,z989,z1,z2,z4]),(0,[z7,z0,z990,z1,z2,z4]),(0,[z7,z0,z1,z4,z14,z6]),(0,[z7,z373,z0,z153,z2,z4]),(0,[z7,z0,z17,z130,z2,z4])],[(0,[z7,z0,z1,z2,z4,z991]),(0,[z7,z0,z1,z2,z4,z712])],[(0,[z7,z0,z992,z195,z2,z4]),(0,[z7,z0,z25,z2,z4,z6]),(0,[z7,z0,z1,z88,z4,z340]),(0,[z7,z0,z1,z993,z4,z6]),(0,[z7,z0,z994,z2,z4,z6])],[(0,[z7,z0,z1,z2,z995,z6]),(0,[z7,z0,z109,z27,z4,z6]),(0,[z377,z0,z1,z88,z4,z6]),(0,[z7,z61,z26,z2,z69,z6]),(0,[z7,z0,z1,z2,z996,z6]),(0,[z7,z367,z0,z17,z2,z4])],[(0,[z7,z138,z17,z1,z2,z4]),(0,[z7,z0,z1,z997,z4,z6]),(0,[z7,z0,z1,z2,z4,z998]),(0,[z7,z0,z41,z20,z4,z6]),(0,[z7,z0,z2,z4,z123,z42])],[(0,[z7,z0,z1,z2,z4,z999]),(0,[z31,z0,z844,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z384]),(0,[z7,z0,z394,z51,z2,z4]),(0,[z7,z0,z1000,z1,z2,z4])],[(0,[z52,z0,z132,z392,z4,z6]),(0,[z55,z0,z1,z19,z4,z6]),(0,[z7,z0,z1,z165,z100,z6]),(0,[z7,z0,z17,z2,z277,z35])],[(0,[z7,z0,z1,z19,z325,z6]),(0,[z7,z1,z2,z4,z6,z832]),(0,[z7,z0,z1001,z1,z2,z4]),(0,[z7,z106,z96,z1,z2,z6]),(0,[z7,z0,z51,z1,z260,z4]),(0,[z7,z61,z248,z26,z2,z4]),(0,[z7,z0,z1002,z1,z4,z6]),(0,[z7,z0,z51,z528,z2,z4]),(0,[z7,z0,z28,z2,z532,z35])],[],[(0,[z7,z0,z1003,z2,z4,z6])],[(0,[z52,z0,z132,z19,z4,z6]),(0,[z7,z0,z51,z1,z2,z277])]],
   [[(0,[z7,z0,z1,z2,z4,z1004])],[(0,[z7,z0,z88,z4,z23,z6]),(0,[z7,z0,z476,z1,z88,z4]),(0,[z7,z138,z51,z1,z2,z4]),(0,[z631,z0,z1,z2,z4,z68]),(0,[z7,z0,z41,z476,z2,z4])],[],[(0,[z7,z0,z1,z2,z4,z1005])],[(0,[z7,z0,z1,z2,z1006,z6]),(0,[z7,z0,z1,z2,z1007,z6]),(0,[z7,z0,z1,z2,z1008,z6]),(0,[z7,z0,z17,z2,z4,z421]),(0,[z7,z0,z1,z925,z4,z6]),(0,[z7,z0,z27,z4,z6,z410])],[(0,[z7,z0,z1,z1009,z4,z6]),(0,[z7,z98,z1,z49,z4,z6]),(0,[z34,z0,z81,z2,z5,z6])],[(0,[z7,z0,z19,z4,z6,z1010]),(0,[z7,z0,z1,z88,z4,z32])],[(0,[z7,z0,z1,z2,z4,z115]),(1,[z7,z0,z786,z2,z4]),(0,[z7,z0,z1,z1011,z4,z6])],[(0,[z665,z0,z1,z19,z4,z6])],[(0,[z7,z0,z1,z88,z4,z1012]),(0,[z7,z188,z466,z1,z4,z6])],[(0,[z7,z0,z1,z2,z1013,z6]),(0,[z7,z0,z28,z19,z35,z6]),(0,[z7,z0,z1,z411,z4,z33]),(0,[z7,z61,z820,z2,z4,z6]),(0,[z7,z0,z2,z509,z35,z6]),(0,[z7,z0,z1014,z1,z2,z4])],[(0,[z518,z0,z1,z2,z4,z60]),(0,[z7,z0,z96,z1,z332,z6]),(0,[z7,z0,z51,z1,z959,z4]),(0,[z7,z0,z1,z39,z748,z6])],[(0,[z7,z0,z195,z19,z4,z6]),(0,[z103,z0,z1,z2,z3,z6]),(0,[z7,z0,z2,z4,z1015,z6]),(0,[z7,z0,z1,z214,z4,z219])],[(0,[z0,z1,z355,z88,z4,z6])],[(0,[z75,z0,z1,z260,z4,z60]),(0,[z7,z0,z1,z2,z4,z1016])],[(0,[z7,z0,z1,z478,z93,z6]),(0,[z221,z0,z1,z742,z4,z6]),(0,[z7,z196,z0,z153,z2,z4])]],
   [[(0,[z7,z0,z19,z4,z23,z6]),(0,[z7,z0,z1,z1017,z4,z6]),(0,[z7,z0,z1,z1018,z4,z6]),(0,[z7,z0,z130,z1,z2,z212])],[(0,[z7,z0,z105,z88,z4,z6]),(0,[z7,z90,z0,z1019,z2,z4]),(0,[z7,z0,z56,z697,z4,z6])],[(0,[z75,z0,z1,z19,z4,z60]),(0,[z7,z61,z0,z17,z88,z4]),(0,[z7,z0,z1,z88,z1008,z6])],[(0,[z7,z0,z1020,z1,z2,z6]),(0,[z7,z0,z17,z199,z2,z4]),(0,[z7,z0,z1021,z1,z2,z4]),(0,[z7,z0,z17,z1,z4,z9]),(0,[z7,z0,z168,z51,z2,z181]),(0,[z7,z0,z17,z2,z4,z23])],[(0,[z7,z0,z1,z2,z779,z6]),(0,[z7,z0,z1,z30,z74,z6]),(0,[z7,z666,z0,z17,z2,z4])],[(0,[z7,z0,z17,z18,z19,z4]),(0,[z7,z0,z1022,z1,z19,z4]),(0,[z7,z0,z17,z504,z2,z4]),(0,[z7,z449,z431,z1,z2,z4])],[(0,[z7,z0,z1020,z1,z352,z6]),(0,[z7,z0,z1,z350,z4,z278]),(0,[z7,z106,z1,z30,z2,z6]),(0,[z7,z0,z1,z2,z277,z371])],[(0,[z7,z0,z1,z860,z80,z6]),(0,[z7,z126,z1,z88,z97,z6]),(0,[z7,z434,z0,z17,z2,z4])],[(0,[z7,z0,z211,z17,z2,z4]),(0,[z7,z0,z105,z2,z35,z6])],[(0,[z7,z0,z1,z478,z4,z6]),(0,[z7,z0,z17,z2,z80,z6]),(0,[z7,z0,z1023,z2,z4,z6]),(0,[z7,z0,z151,z1,z4,z133]),(0,[z7,z0,z179,z2,z4,z6])],[(0,[z7,z0,z1,z743,z2,z4]),(0,[z7,z0,z1,z2,z1024,z6]),(0,[z7,z0,z17,z2,z4,z309]),(0,[z7,z0,z17,z2,z135,z4]),(0,[z7,z0,z1,z1025,z4,z6])],[(0,[z7,z0,z1,z2,z1026,z6]),(0,[z7,z0,z1,z88,z1027,z4]),(0,[z45,z0,z1,z646,z2,z6])],[(0,[z7,z160,z106,z1,z2,z6]),(0,[z7,z0,z2,z725,z35,z6])],[(0,[z7,z0,z1,z1028,z4,z6]),(0,[z7,z90,z0,z17,z19,z4]),(0,[z7,z0,z1,z2,z550,z59]),(0,[z7,z0,z1,z1029,z4,z6])],[(0,[z0,z1,z19,z592,z4,z6]),(0,[z7,z0,z197,z1,z4,z223]),(0,[z7,z0,z1,z88,z4,z1030]),(0,[z7,z0,z81,z2,z4,z33])],[(0,[z7,z0,z248,z1,z19,z4]),(0,[z7,z48,z1,z49,z102,z6]),(0,[z7,z0,z1,z2,z371,z182])]],
   [[(0,[z7,z0,z1,z2,z714,z6]),(0,[z7,z0,z1,z19,z943,z6]),(0,[z187,z0,z1,z2,z4,z68]),(0,[z7,z0,z2,z4,z1031,z6])],[(0,[z7,z1032,z1,z2,z4,z6]),(0,[z7,z0,z79,z1,z88,z4]),(0,[z7,z0,z820,z2,z4,z6]),(0,[z7,z0,z1,z1033,z4,z6]),(0,[z7,z0,z2,z4,z1031,z94]),(0,[z7,z0,z17,z1,z2,z752]),(0,[z7,z768,z0,z1,z4,z6])],[(0,[z7,z0,z1034,z2,z4,z6]),(0,[z7,z0,z17,z217,z2,z4]),(0,[z7,z0,z17,z2,z4,z353]),(0,[z1035,z0,z1,z2,z4,z6]),(0,[z7,z0,z17,z2,z277,z29])],[(0,[z50,z12,z186,z2,z4,z6]),(0,[z7,z1036,z0,z1,z2,z6]),(0,[z1037,z0,z1,z2,z4,z6]),(0,[z7,z0,z211,z1,z4,z6])],[(0,[z7,z379,z0,z1,z19,z6]),(0,[z7,z0,z1,z19,z384,z6]),(0,[z7,z138,z1,z19,z4,z6]),(0,[z7,z0,z1,z215,z4,z6]),(0,[z1038,z0,z1,z2,z4,z6]),(0,[z7,z0,z1,z1039,z4,z6])],[(0,[z7,z0,z1,z271,z4,z43]),(0,[z7,z0,z1,z1040,z4,z6])],[(0,[z7,z0,z1,z88,z1041,z6]),(0,[z7,z0,z175,z1,z4,z6])],[],[(0,[z7,z0,z51,z1,z392,z4]),(0,[z7,z0,z776,z81,z2,z4]),(0,[z7,z0,z1042,z1,z4,z6]),(0,[z7,z1043,z0,z1,z2,z6])],[(0,[z7,z0,z1,z2,z1044,z6]),(0,[z7,z1,z2,z4,z1045,z6]),(0,[z7,z0,z17,z2,z4,z203]),(1,[z7,z0,z1,z2,z740])],[],[(0,[z7,z0,z236,z168,z2,z4]),(0,[z7,z0,z17,z1,z88,z277]),(0,[z45,z7,z0,z211,z1,z6]),(0,[z7,z126,z17,z1,z2,z97])],[(0,[z7,z0,z1,z4,z1046,z6]),(0,[z7,z0,z1,z2,z4,z944]),(0,[z7,z0,z318,z1,z4,z223]),(0,[z7,z0,z1,z2,z4,z340]),(0,[z7,z0,z17,z632,z2,z4])],[(0,[z7,z0,z1047,z1,z2,z4]),(0,[z1048,z7,z0,z1,z2,z6]),(1,[z7,z0,z1,z4,z865])],[(0,[z7,z0,z56,z27,z4,z42])],[(0,[z7,z0,z1,z2,z754,z6]),(0,[z7,z61,z154,z2,z4,z6]),(0,[z7,z0,z17,z1,z2,z721])]],
   [[(0,[z7,z0,z17,z2,z4,z370])],[(0,[z590,z0,z18,z2,z4,z6]),(0,[z7,z48,z1,z789,z4,z6])],[(0,[z7,z0,z1,z30,z591,z6])],[(0,[z7,z0,z844,z2,z4,z6]),(0,[z7,z0,z53,z17,z1,z19]),(0,[z7,z0,z175,z248,z1,z4]),(0,[z7,z126,z51,z1,z2,z97]),(0,[z7,z0,z96,z1,z425,z6])],[],[],[(0,[z7,z636,z1,z2,z194,z6]),(0,[z7,z0,z1,z2,z4,z1049])],[(0,[z7,z0,z836,z1,z4,z6]),(0,[z7,z0,z1050,z2,z4,z6]),(0,[z7,z0,z1,z88,z64,z6]),(0,[z7,z0,z17,z27,z88,z4]),(0,[z7,z0,z1,z826,z4,z6])],[(0,[z7,z1051,z1,z2,z4,z6]),(0,[z7,z134,z1,z2,z4,z67])],[(0,[z7,z0,z1052,z1,z2,z4]),(0,[z7,z0,z1053,z1,z4,z6]),(0,[z7,z0,z192,z17,z2,z4]),(0,[z7,z0,z1,z19,z4,z974]),(0,[z7,z0,z1,z2,z726,z6]),(0,[z0,z1,z1054,z2,z4,z6]),(0,[z7,z0,z1,z1055,z4,z6])],[(0,[z7,z0,z17,z2,z4,z396])],[(0,[z7,z0,z1,z2,z4,z32])],[],[(0,[z7,z0,z1,z2,z4,z1056]),(0,[z7,z0,z790,z1,z2,z4])],[(0,[z484,z0,z132,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z1012]),(0,[z7,z0,z246,z17,z2,z4]),(0,[z249,z0,z1,z88,z4,z6])],[(0,[z7,z0,z1,z2,z64,z68]),(0,[z7,z0,z17,z1,z2,z64])]],
   [[],[(0,[z31,z0,z18,z19,z4,z6]),(0,[z7,z0,z41,z96,z17,z4])],[(0,[z7,z0,z76,z2,z1057,z6])],[(0,[z7,z0,z1058,z2,z4,z6]),(0,[z45,z0,z1,z100,z3,z6]),(0,[z7,z0,z1,z1059,z4,z6])],[(0,[z7,z0,z1,z4,z219,z94]),(0,[z7,z0,z51,z1,z887,z4])],[(0,[z7,z0,z51,z1,z2,z384]),(0,[z0,z1,z19,z4,z668,z6])],[(0,[z7,z0,z1,z1060,z4,z6]),(0,[z7,z0,z1,z100,z4,z6]),(0,[z7,z106,z365,z2,z4,z6]),(0,[z7,z0,z1,z2,z1061,z6]),(0,[z7,z0,z1,z1062,z2,z6]),(0,[z7,z0,z105,z2,z4,z6])],[(0,[z7,z0,z1,z19,z4,z991]),(0,[z1063,z0,z1,z2,z4,z6]),(0,[z7,z0,z51,z1,z2,z64]),(0,[z7,z0,z17,z1,z2,z804])],[(0,[z50,z379,z12,z1,z2,z6]),(0,[z704,z0,z1,z2,z4,z68])],[(0,[z7,z0,z1064,z1,z4,z6]),(0,[z7,z0,z1,z1065,z4,z6]),(0,[z7,z0,z1066,z1,z2,z4]),(0,[z7,z0,z1,z19,z995,z6]),(0,[z7,z0,z17,z453,z2,z4]),(0,[z7,z61,z0,z269,z2,z4]),(0,[z7,z0,z1067,z2,z4,z6]),(0,[z7,z1,z2,z913,z4,z6]),(0,[z7,z0,z56,z778,z4,z6]),(0,[z7,z0,z17,z2,z4,z111])],[(0,[z50,z12,z1,z2,z4,z298]),(0,[z7,z0,z1,z742,z4,z6]),(0,[z1068,z0,z1,z2,z4,z6]),(0,[z1038,z0,z17,z1,z2,z4]),(0,[z7,z0,z17,z440,z2,z4])],[(0,[z7,z90,z62,z88,z4,z6]),(0,[z7,z0,z1,z88,z4,z1056]),(0,[z7,z0,z1069,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z1070])],[(0,[z7,z0,z1,z2,z1071,z6]),(0,[z7,z0,z1,z2,z4,z1072]),(0,[z7,z126,z1,z2,z97,z6]),(0,[z7,z0,z2,z4,z6,z1073]),(0,[z7,z0,z1,z4,z6,z1074]),(0,[z7,z196,z153,z2,z4,z148]),(0,[z7,z0,z1,z2,z4,z1075]),(0,[z7,z0,z1,z1076,z4,z6]),(0,[z7,z0,z333,z2,z35,z6])],[(0,[z221,z0,z17,z1,z88,z4]),(0,[z7,z0,z1,z1077,z4,z6]),(0,[z7,z0,z1,z2,z4,z1078]),(0,[z7,z0,z1,z2,z4,z1079]),(0,[z7,z1,z2,z4,z712,z148])],[(0,[z7,z0,z428,z2,z181,z6]),(0,[z7,z0,z1,z214,z162,z4])],[(0,[z7,z0,z1,z2,z4,z1080]),(0,[z7,z0,z604,z2,z35,z6]),(0,[z7,z0,z79,z18,z2,z4])]],
   [[(0,[z7,z0,z1,z2,z4,z1081]),(0,[z7,z0,z197,z1,z4,z359]),(0,[z7,z0,z1,z2,z6,z1082]),(0,[z7,z0,z1,z2,z1027,z4]),(0,[z7,z61,z158,z26,z4,z6])],[(0,[z50,z12,z1,z2,z325,z6]),(0,[z7,z0,z17,z1,z2,z177]),(0,[z7,z1,z2,z789,z4,z6]),(0,[z7,z0,z17,z1,z2,z102]),(0,[z7,z0,z41,z17,z20,z4])],[(0,[z715,z12,z1,z2,z4,z6]),(0,[z7,z11,z0,z17,z1,z2]),(0,[z7,z0,z236,z1,z2,z4]),(0,[z7,z0,z1083,z1,z2,z4]),(0,[z7,z0,z1084,z2,z4,z6]),(0,[z7,z0,z1,z782,z4,z6])],[(0,[z7,z0,z1,z2,z4,z1030]),(0,[z7,z0,z273,z1,z4,z133])],[(0,[z7,z0,z17,z1,z2,z4]),(0,[z7,z0,z17,z186,z2,z4]),(0,[z7,z0,z1,z2,z1085,z6]),(0,[z7,z0,z1086,z1,z2,z4]),(0,[z7,z170,z1,z2,z4,z148])],[(0,[z7,z0,z17,z51,z88,z4]),(0,[z7,z138,z1,z411,z4,z6]),(0,[z7,z0,z17,z25,z2,z4])],[(0,[z7,z0,z1,z2,z4,z1087]),(0,[z7,z11,z0,z1,z2,z6]),(0,[z7,z0,z17,z166,z2,z4]),(0,[z7,z0,z1088,z2,z4,z6]),(0,[z7,z0,z73,z1,z2,z64])],[(0,[z7,z0,z17,z1,z352,z4]),(0,[z7,z169,z1,z227,z4,z6]),(0,[z7,z160,z1,z88,z194,z6]),(0,[z294,z0,z1,z88,z4,z6]),(0,[z7,z0,z1,z2,z1089,z4])],[(0,[z7,z0,z151,z179,z4,z223])],[(0,[z7,z0,z1,z1090,z4,z6]),(0,[z7,z0,z2,z4,z1091,z6]),(0,[z7,z0,z17,z18,z2,z277]),(0,[z7,z0,z51,z1,z2,z177])],[(0,[z7,z0,z1,z205,z4,z6]),(0,[z7,z0,z269,z1,z2,z4])],[(0,[z380,z0,z1,z19,z4,z6]),(0,[z7,z0,z1,z2,z1041,z6]),(0,[z7,z0,z1,z4,z1092,z6])],[(0,[z7,z0,z51,z1,z2,z4]),(0,[z7,z0,z51,z186,z2,z4]),(0,[z7,z0,z1093,z1,z2,z4]),(0,[z7,z0,z1094,z1,z2,z4]),(0,[z7,z0,z2,z778,z4,z6]),(0,[z341,z7,z154,z1,z2,z4])],[(0,[z7,z0,z51,z25,z2,z4])],[(0,[z7,z0,z1095,z1,z2,z4]),(0,[z7,z0,z1096,z2,z4,z6]),(0,[z7,z0,z1,z2,z1057,z6]),(0,[z7,z0,z51,z1,z4,z9]),(0,[z7,z0,z51,z2,z4,z23])],[(0,[z7,z0,z1097,z2,z4,z6]),(0,[z7,z0,z51,z1,z352,z4]),(0,[z7,z0,z76,z260,z4,z6]),(0,[z7,z0,z153,z51,z2,z4]),(0,[z7,z0,z17,z268,z2,z4]),(0,[z7,z0,z51,z1,z1029,z4])]],
   [[(0,[z7,z0,z1,z2,z1098,z6]),(0,[z7,z0,z1,z2,z4,z1099]),(0,[z7,z0,z53,z1,z19,z6]),(0,[z7,z0,z51,z88,z4,z172]),(0,[z7,z0,z17,z240,z2,z4]),(0,[z7,z0,z1,z1100,z4,z6]),(0,[z7,z0,z2,z4,z6,z1101])],[(0,[z7,z0,z17,z168,z88,z4]),(0,[z7,z90,z0,z17,z2,z277]),(0,[z7,z0,z17,z567,z2,z4])],[(0,[z7,z0,z96,z1,z165,z6])],[(0,[z7,z0,z1,z1102,z4,z6]),(0,[z7,z0,z76,z19,z4,z6]),(0,[z0,z1,z19,z4,z71,z6]),(0,[z7,z0,z318,z17,z1,z4])],[(0,[z7,z0,z1,z4,z1103,z6])],[(0,[z7,z0,z186,z271,z4,z6]),(0,[z7,z0,z1,z2,z1104,z6]),(0,[z0,z220,z1,z19,z4,z6]),(0,[z7,z0,z1,z88,z177,z6]),(0,[z7,z0,z220,z1,z2,z64]),(0,[z7,z0,z1,z1105,z4,z6])],[(0,[z7,z0,z1,z1106,z4,z6])],[(0,[z7,z0,z18,z2,z64,z6]),(0,[z7,z0,z2,z4,z968,z35])],[(0,[z7,z0,z17,z1,z2,z325]),(0,[z7,z0,z217,z1,z2,z4])],[(0,[z7,z0,z217,z25,z2,z4]),(0,[z7,z138,z81,z2,z4,z6]),(0,[z7,z0,z17,z1019,z2,z4]),(0,[z7,z0,z1,z2,z948,z6]),(0,[z7,z0,z2,z4,z172,z854])],[(0,[z7,z0,z1107,z2,z4,z6]),(0,[z7,z1,z2,z97,z913,z6])],[(0,[z7,z0,z1,z19,z1024,z6]),(0,[z7,z0,z1,z1108,z4,z6]),(0,[z7,z0,z17,z105,z2,z4])],[(0,[z7,z0,z1,z2,z64,z6])],[(0,[z7,z0,z1,z1109,z4,z6]),(0,[z7,z0,z1,z411,z4,z6]),(0,[z7,z0,z1,z671,z4,z219]),(0,[z1063,z0,z17,z1,z2,z4])],[(0,[z7,z0,z1110,z1,z2,z6]),(0,[z34,z0,z365,z2,z5,z6]),(0,[z7,z0,z1,z2,z740,z182])],[(0,[z7,z0,z1111,z2,z4,z6]),(0,[z7,z0,z41,z17,z301,z4])]],
   [[(0,[z7,z0,z41,z17,z19,z4]),(0,[z7,z0,z17,z1,z951,z4])],[(0,[z187,z0,z1,z19,z4,z68]),(0,[z7,z0,z211,z1,z97,z6])],[],[(0,[z7,z0,z1112,z1,z2,z4]),(0,[z7,z0,z1001,z1,z88,z4]),(0,[z7,z0,z17,z1,z88,z64]),(0,[z7,z0,z1113,z1,z4,z6]),(0,[z7,z820,z26,z2,z4,z6]),(0,[z7,z0,z778,z20,z4,z6]),(0,[z7,z0,z168,z2,z181,z371]),(0,[z7,z0,z51,z105,z2,z4])],[(0,[z7,z126,z11,z1,z2,z6]),(0,[z7,z0,z1,z945,z2,z6]),(0,[z7,z467,z1,z2,z194,z6]),(0,[z7,z0,z1,z165,z19,z6]),(0,[z7,z0,z1,z215,z4,z32]),(1,[z0,z1,z2,z754,z6]),(0,[z7,z0,z2,z69,z172,z6]),(0,[z1114,z0,z1,z2,z4,z6])],[(0,[z7,z0,z1,z19,z93,z6]),(0,[z7,z0,z1,z1115,z4,z6]),(0,[z7,z0,z1,z214,z4,z865])],[(0,[z7,z0,z132,z2,z64,z6]),(0,[z261,z0,z1,z19,z4,z6]),(0,[z7,z0,z1116,z1,z4,z6]),(0,[z7,z0,z563,z2,z35,z6]),(0,[z7,z0,z1,z2,z4,z708]),(0,[z7,z196,z318,z1,z4,z148]),(0,[z7,z1117,z1,z2,z4,z6])],[(0,[z7,z0,z87,z1,z239,z6]),(0,[z7,z0,z1,z2,z969,z6])],[(1,[z0,z844,z2,z4,z6]),(0,[z7,z0,z1118,z2,z4,z6])],[(0,[z7,z0,z1,z19,z4,z284]),(0,[z7,z0,z1,z1119,z4,z6])],[(0,[z7,z0,z1,z88,z4,z189])],[(0,[z7,z0,z1,z392,z4,z6]),(0,[z7,z0,z1,z260,z4,z6]),(0,[z7,z0,z211,z79,z1,z4]),(0,[z7,z0,z1,z1120,z4,z6]),(0,[z7,z0,z51,z1,z1115,z4])],[(0,[z45,z0,z1,z19,z3,z6]),(0,[z7,z417,z1,z2,z4,z148])],[(0,[z7,z0,z17,z1,z165,z19]),(0,[z7,z0,z1,z19,z4,z340])],[(0,[z7,z0,z1121,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z1122]),(0,[z7,z0,z1,z4,z6,z865])],[(0,[z7,z0,z1,z19,z4,z6]),(0,[z7,z0,z1123,z1,z2,z6]),(0,[z7,z0,z1,z1124,z4,z6]),(0,[z7,z0,z2,z4,z35,z371])]],
   [[(0,[z7,z0,z1125,z1,z2,z6]),(0,[z7,z0,z17,z156,z2,z4]),(0,[z7,z0,z53,z1,z165,z6]),(0,[z7,z0,z1,z19,z4,z94]),(0,[z7,z90,z62,z2,z4,z6]),(0,[z7,z0,z17,z178,z2,z4])],[(0,[z7,z0,z1,z350,z4,z6]),(0,[z7,z0,z81,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z716]),(0,[z7,z0,z1,z1126,z4,z6]),(0,[z7,z0,z1,z2,z1127,z6])],[(0,[z7,z0,z1,z2,z4,z1128]),(0,[z7,z0,z86,z1,z19,z182]),(1,[z7,z1,z2,z913,z6]),(0,[z7,z0,z1,z2,z1129,z6]),(0,[z7,z0,z1,z2,z1130,z4])],[(0,[z7,z0,z1131,z1,z4,z6]),(0,[z7,z0,z1,z2,z4,z1132]),(0,[z7,z0,z1,z1133,z4,z6]),(0,[z7,z0,z1134,z2,z4,z6]),(0,[z7,z0,z1135,z2,z4,z6])],[],[(0,[z7,z0,z51,z1,z165,z19])],[(0,[z31,z0,z18,z350,z4,z6]),(0,[z7,z0,z1,z2,z4,z1136])],[(0,[z84,z127,z1,z352,z4,z6]),(0,[z34,z7,z0,z211,z1,z6]),(0,[z7,z0,z25,z260,z4,z6]),(0,[z7,z0,z76,z2,z4,z60])],[(0,[z7,z0,z17,z1,z88,z4]),(0,[z479,z0,z17,z1,z19,z4]),(0,[z34,z106,z1,z2,z5,z6]),(0,[z7,z701,z0,z17,z2,z4])],[(0,[z7,z0,z1,z19,z988,z6]),(0,[z0,z1,z646,z88,z4,z6]),(0,[z7,z0,z1,z2,z4,z1137])],[(0,[z7,z0,z1,z2,z4,z1138]),(0,[z7,z0,z488,z17,z2,z4])],[(0,[z7,z0,z1139,z2,z4,z6]),(0,[z7,z0,z1140,z1,z4,z6]),(0,[z7,z0,z17,z209,z2,z4]),(0,[z7,z0,z25,z19,z4,z6]),(0,[z7,z0,z911,z81,z2,z4]),(0,[z7,z0,z381,z17,z2,z4])],[(0,[z7,z0,z186,z2,z4,z43]),(0,[z7,z0,z1,z271,z4,z298]),(0,[z7,z1141,z1,z2,z4,z6]),(0,[z7,z0,z1,z19,z4,z32]),(0,[z7,z0,z1,z4,z1142,z6]),(0,[z7,z0,z17,z2,z4,z589]),(0,[z7,z0,z248,z158,z1,z4]),(0,[z7,z160,z1,z2,z194,z6])],[(0,[z7,z0,z1,z2,z4,z1143]),(0,[z7,z0,z2,z4,z6,z1010]),(0,[z7,z0,z15,z1,z632,z4])],[(0,[z7,z0,z1144,z2,z4,z6]),(0,[z7,z0,z109,z166,z4,z6]),(0,[z7,z0,z17,z1,z2,z918])],[(0,[z7,z0,z770,z195,z2,z4]),(0,[z7,z0,z1,z4,z1145,z6]),(0,[z7,z0,z1,z2,z4,z1146]),(1,[z0,z1,z742,z4,z6]),(0,[z7,z0,z81,z88,z4,z6]),(0,[z7,z61,z26,z88,z4,z6]),(0,[z7,z0,z41,z152,z4,z6]),(0,[z187,z0,z1,z205,z4,z68]),(0,[z7,z0,z17,z2,z194,z35]),(0,[z7,z0,z51,z2,z4,z582])]],
   [[(0,[z7,z0,z153,z2,z4,z219]),(0,[z7,z0,z79,z1,z2,z171])],[(0,[z7,z0,z1,z932,z4,z6]),(0,[z7,z48,z1,z227,z4,z6])],[(0,[z7,z0,z365,z2,z181,z6]),(0,[z7,z0,z17,z593,z2,z4])],[(0,[z7,z0,z1,z271,z325,z6]),(0,[z7,z0,z1,z214,z4,z458]),(0,[z7,z0,z17,z2,z4,z95])],[],[(0,[z187,z0,z1,z2,z4,z708]),(0,[z7,z0,z51,z2,z4,z172]),(0,[z7,z0,z1,z1147,z4,z6])],[(0,[z7,z1,z820,z2,z4,z6])],[(0,[z7,z0,z105,z19,z4,z6]),(0,[z7,z0,z41,z185,z4,z6])],[(0,[z221,z0,z51,z1,z88,z4]),(0,[z7,z0,z1148,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z1149])],[(0,[z7,z0,z1,z4,z1150,z6]),(0,[z187,z0,z220,z1,z2,z4]),(0,[z7,z0,z1151,z2,z4,z6])],[(0,[z0,z17,z220,z1,z19,z4]),(0,[z7,z0,z1,z88,z477,z4]),(0,[z7,z106,z1,z2,z5,z6]),(0,[z7,z0,z1,z2,z177,z6]),(0,[z7,z0,z1,z2,z4,z1152])],[(0,[z7,z0,z17,z132,z19,z4]),(0,[z7,z0,z1,z19,z4,z115])],[(0,[z7,z0,z1,z228,z4,z219]),(0,[z7,z90,z62,z2,z4,z115]),(0,[z7,z0,z51,z1,z2,z102]),(0,[z7,z0,z1,z2,z748,z6])],[(0,[z7,z0,z2,z4,z6,z1153])],[(0,[z0,z1,z742,z2,z4,z6]),(0,[z7,z0,z405,z1,z2,z182]),(0,[z7,z196,z2,z4,z116,z148])],[(0,[z50,z12,z1,z88,z4,z6]),(0,[z7,z0,z17,z18,z2,z384]),(0,[z0,z51,z1,z88,z19,z4]),(1,[z7,z0,z211,z17,z4]),(0,[z295,z0,z220,z1,z2,z4])]],
   [[(0,[z52,z0,z132,z119,z4,z6]),(0,[z7,z0,z922,z1,z2,z6]),(0,[z7,z0,z17,z2,z4,z69]),(0,[z7,z0,z1,z2,z4,z1154]),(0,[z7,z0,z96,z1,z22,z6])],[(0,[z7,z0,z1,z1155,z4,z6]),(0,[z7,z0,z217,z2,z4,z172]),(0,[z7,z106,z1,z2,z4,z33])],[],[(0,[z7,z0,z195,z271,z4,z6]),(0,[z7,z0,z1,z2,z4,z1156])],[(0,[z50,z12,z195,z2,z4,z6]),(0,[z7,z0,z1157,z2,z4,z6])],[],[(0,[z7,z0,z1158,z2,z4,z6]),(0,[z7,z0,z1,z2,z1159,z6]),(0,[z7,z0,z1,z1160,z4,z6]),(0,[z7,z0,z2,z4,z1161,z6])],[(0,[z7,z0,z1162,z2,z4,z6]),(0,[z511,z0,z1,z19,z4,z6]),(0,[z517,z0,z1,z88,z4,z6]),(0,[z7,z0,z17,z598,z2,z4]),(0,[z7,z310,z1,z2,z97,z6]),(0,[z7,z0,z1,z1163,z4,z6])],[(0,[z7,z0,z51,z1,z1059,z4])],[(0,[z7,z0,z946,z1,z2,z4]),(0,[z7,z0,z1,z2,z4,z1164]),(0,[z7,z0,z131,z1,z2,z372])],[(0,[z7,z0,z1,z2,z1165,z6]),(0,[z34,z0,z17,z1,z2,z5])],[(0,[z7,z0,z1,z2,z1166,z6]),(0,[z7,z515,z62,z2,z4,z6]),(0,[z7,z0,z2,z4,z6,z123])],[(0,[z7,z0,z1,z2,z1167,z6]),(0,[z0,z1,z165,z88,z19,z6]),(0,[z7,z196,z1,z88,z4,z148]),(0,[z7,z106,z1,z2,z181,z6])],[(0,[z7,z0,z179,z19,z4,z6]),(0,[z7,z0,z1,z4,z1168,z6]),(0,[z7,z188,z1,z44,z4,z6]),(0,[z7,z0,z1,z88,z102,z6])],[],[(0,[z7,z0,z1,z2,z4,z189]),(0,[z7,z188,z531,z1,z4,z6]),(0,[z7,z0,z41,z1,z117,z6]),(0,[z7,z0,z17,z2,z4,z854])]],
   [[(0,[z7,z0,z192,z17,z88,z4]),(0,[z7,z0,z1169,z1,z2,z4]),(0,[z408,z0,z1,z2,z4,z68])],[(0,[z7,z0,z1,z2,z1170,z6]),(0,[z7,z0,z1171,z2,z4,z6]),(0,[z7,z0,z1172,z2,z4,z6])],[(0,[z52,z0,z17,z132,z2,z4]),(0,[z7,z0,z1173,z2,z4,z6]),(0,[z7,z61,z17,z154,z2,z4]),(0,[z7,z0,z151,z1,z185,z4])],[(0,[z7,z0,z51,z1,z2,z325]),(0,[z7,z0,z1,z1174,z4,z6]),(0,[z7,z0,z1175,z2,z4,z6]),(0,[z7,z330,z1,z58,z4,z6]),(0,[z7,z0,z1176,z2,z4,z6]),(0,[z7,z0,z17,z4,z9,z35]),(0,[z7,z0,z168,z2,z277,z6]),(0,[z1068,z0,z17,z1,z2,z4])],[(0,[z7,z449,z1,z2,z4,z67]),(0,[z7,z0,z41,z17,z2,z277])],[(0,[z7,z1177,z0,z1,z2,z6]),(0,[z7,z0,z2,z4,z116,z36])],[(0,[z7,z0,z1022,z1,z2,z4]),(0,[z7,z0,z1,z19,z1104,z6]),(0,[z7,z0,z1,z2,z4,z1178]),(0,[z7,z0,z17,z1,z2,z1165])],[(0,[z7,z0,z2,z4,z1179,z6]),(0,[z7,z0,z1180,z1,z4,z6]),(0,[z7,z0,z51,z2,z4,z854])],[],[(0,[z7,z0,z41,z53,z1,z6]),(0,[z7,z0,z28,z9,z35,z6]),(0,[z7,z0,z1,z301,z4,z219])],[(0,[z7,z0,z1,z2,z325,z43]),(0,[z7,z0,z81,z215,z4,z6]),(0,[z7,z0,z1181,z1,z2,z4]),(0,[z7,z48,z0,z41,z17,z4]),(0,[z7,z0,z318,z1,z4,z219])],[(0,[z7,z0,z1,z2,z1182,z6]),(0,[z84,z127,z1,z303,z4,z6]),(1,[z0,z1,z2,z4,z708]),(0,[z7,z48,z1,z49,z117,z6])],[(0,[z7,z0,z365,z2,z35,z6]),(0,[z7,z0,z17,z608,z2,z4]),(0,[z7,z0,z17,z2,z4,z691])],[(0,[z7,z0,z1,z19,z64,z6]),(0,[z7,z0,z1,z411,z4,z32]),(0,[z7,z0,z2,z181,z725,z6])],[(0,[z7,z0,z53,z1,z22,z6]),(0,[z7,z0,z1183,z1,z4,z6]),(0,[z464,z0,z1,z2,z5,z6]),(0,[z7,z0,z1,z2,z1184,z6]),(0,[z7,z0,z51,z570,z2,z4])],[(0,[z7,z0,z1,z2,z4,z1185]),(0,[z7,z0,z17,z345,z2,z4]),(0,[z7,z1,z2,z1186,z4,z6])]],
   [[(0,[z31,z0,z17,z18,z2,z4]),(0,[z7,z261,z0,z17,z2,z4]),(0,[z7,z0,z1,z1187,z4,z6]),(0,[z7,z134,z584,z1,z2,z4])],[(0,[z7,z0,z17,z2,z4,z238]),(0,[z7,z0,z1,z1188,z4,z6])],[(0,[z7,z0,z1,z1189,z4,z6]),(0,[z7,z0,z2,z4,z532,z23]),(0,[z7,z1,z2,z1190,z4,z6])],[(0,[z7,z0,z1,z88,z4,z36]),(0,[z7,z0,z1,z2,z1191,z6]),(1,[z7,z1,z2,z4,z712]),(0,[z7,z0,z51,z552,z2,z4])],[(0,[z7,z0,z1,z2,z717,z6]),(0,[z7,z0,z1192,z1,z4,z6]),(0,[z7,z0,z1193,z1,z2,z4]),(0,[z7,z61,z26,z2,z4,z6]),(0,[z7,z0,z1,z2,z171,z372])],[(0,[z7,z0,z1,z88,z1194,z6])],[(0,[z0,z17,z1,z88,z19,z4]),(0,[z307,z0,z1,z19,z4,z6]),(0,[z7,z0,z1,z1195,z4,z6])],[(0,[z7,z0,z1,z1196,z4,z6]),(0,[z7,z0,z1197,z1,z2,z6]),(0,[z7,z0,z17,z1,z2,z1198]),(0,[z7,z0,z1,z1199,z4,z6])],[(0,[z31,z0,z51,z18,z2,z4]),(0,[z7,z0,z1,z1200,z4,z6]),(0,[z7,z0,z1201,z1,z4,z6]),(0,[z7,z0,z1202,z1,z2,z4]),(0,[z7,z0,z17,z1,z2,z1129]),(0,[z7,z0,z1,z748,z22,z6])],[(0,[z7,z0,z1,z271,z93,z6]),(0,[z7,z0,z236,z1,z88,z4]),(0,[z7,z0,z1,z88,z1182,z6]),(0,[z34,z0,z1,z2,z5,z33]),(0,[z7,z0,z17,z619,z2,z4]),(0,[z7,z446,z1,z2,z97,z6])],[(0,[z7,z127,z1,z2,z93,z6]),(0,[z7,z0,z195,z2,z4,z43]),(0,[z50,z12,z1,z2,z93,z6]),(0,[z7,z715,z1,z2,z4,z6]),(0,[z7,z689,z0,z17,z2,z4]),(0,[z7,z0,z365,z2,z4,z33])],[(0,[z7,z0,z1,z2,z4,z213]),(0,[z7,z0,z1,z2,z4,z1203]),(0,[z7,z0,z17,z2,z4,z968]),(0,[z7,z0,z168,z2,z4,z371]),(0,[z7,z0,z17,z347,z2,z4])],[(0,[z7,z0,z1,z2,z4,z1204])],[(0,[z7,z11,z0,z1,z88,z6]),(0,[z7,z0,z909,z1,z19,z6]),(0,[z7,z0,z1,z4,z1205,z6]),(0,[z7,z0,z17,z166,z88,z4]),(0,[z320,z0,z1,z88,z4,z6]),(0,[z7,z0,z17,z1,z215,z4]),(0,[z7,z0,z1206,z2,z4,z6]),(0,[z7,z188,z1,z147,z4,z6]),(0,[z7,z0,z1,z1207,z4,z6])],[(0,[z7,z188,z1,z147,z4,z94]),(0,[z7,z0,z1,z4,z6,z1208]),(0,[z7,z0,z130,z105,z2,z4])],[(0,[z7,z0,z17,z1,z2,z93]),(0,[z7,z126,z1,z2,z85,z6]),(0,[z7,z0,z1,z164,z4,z213]),(0,[z7,z0,z1209,z1,z2,z4]),(0,[z7,z1,z19,z784,z4,z6]),(0,[z7,z106,z1,z88,z4,z6]),(0,[z7,z0,z88,z4,z116,z6]),(0,[z7,z0,z1,z2,z477,z4])]],
   [[(0,[z31,z0,z18,z2,z4,z213]),(0,[z7,z0,z1,z1210,z4,z6])],[(0,[z7,z0,z1,z2,z885,z6]),(0,[z7,z0,z269,z1,z88,z4]),(0,[z7,z0,z81,z2,z4,z32]),(0,[z34,z0,z1,z2,z497,z6]),(0,[z7,z0,z1,z2,z1198,z6])],[(0,[z7,z0,z1,z1211,z4,z6]),(0,[z7,z0,z365,z2,z384,z6]),(0,[z7,z138,z365,z2,z4,z6]),(0,[z7,z0,z1,z789,z4,z6])],[(0,[z7,z0,z1,z271,z4,z6]),(0,[z7,z0,z51,z1,z88,z4]),(0,[z7,z114,z1,z2,z4,z67])],[(0,[z50,z12,z1,z2,z4,z6]),(0,[z7,z0,z88,z4,z6,z904])],[(0,[z496,z0,z132,z2,z4,z6]),(0,[z7,z0,z51,z1,z215,z4]),(0,[z7,z0,z1,z2,z1212,z6])],[(0,[z7,z106,z1,z2,z35,z6]),(0,[z7,z0,z1213,z1,z2,z4]),(0,[z7,z0,z41,z51,z20,z4])],[(0,[z7,z0,z17,z1,z2,z80]),(0,[z7,z0,z2,z80,z172,z6]),(0,[z7,z0,z1,z2,z4,z1214]),(0,[z7,z1215,z1,z2,z4,z6])],[],[(0,[z7,z0,z1,z1216,z4,z6]),(0,[z7,z0,z1,z88,z4,z213]),(0,[z0,z53,z1,z88,z19,z6]),(0,[z7,z0,z1,z2,z4,z1217])],[(0,[z7,z0,z1218,z2,z4,z6]),(0,[z7,z0,z1,z1219,z4,z6]),(0,[z7,z160,z1,z2,z913,z6]),(0,[z7,z0,z17,z2,z4,z448]),(0,[z7,z0,z2,z4,z23,z6])],[(0,[z7,z0,z17,z2,z4,z685]),(0,[z7,z0,z1,z1220,z4,z6]),(0,[z7,z48,z1,z4,z682,z6])],[(0,[z7,z0,z17,z92,z2,z4]),(0,[z7,z0,z17,z521,z2,z4]),(0,[z7,z0,z28,z51,z2,z35])],[(0,[z7,z0,z1,z1221,z4,z6]),(0,[z7,z0,z2,z4,z1222,z6]),(0,[z386,z0,z288,z1,z2,z4])],[(0,[z7,z0,z19,z4,z116,z6]),(0,[z319,z0,z1,z19,z4,z6]),(0,[z7,z0,z17,z88,z4,z35]),(0,[z7,z0,z1,z2,z1223,z4])],[(0,[z7,z0,z217,z1,z88,z4]),(0,[z7,z0,z51,z1,z2,z80]),(0,[z7,z0,z1,z88,z171,z59]),(0,[z7,z1117,z17,z1,z2,z4]),(0,[z7,z0,z151,z179,z2,z4])]],
   [[(0,[z642,z0,z132,z2,z4,z6]),(0,[z7,z126,z1,z19,z97,z6]),(0,[z7,z0,z17,z508,z19,z4]),(0,[z7,z0,z1,z2,z1224,z6])],[(0,[z7,z0,z1,z2,z4,z1225]),(0,[z7,z0,z56,z508,z4,z6]),(0,[z7,z0,z1,z88,z277,z6]),(0,[z7,z0,z1,z2,z64,z60]),(0,[z7,z196,z1,z2,z4,z148]),(0,[z7,z0,z1,z2,z4,z532])],[(0,[z7,z0,z1226,z2,z4,z6]),(0,[z7,z0,z1,z2,z102,z6])],[(0,[z7,z0,z1227,z1,z2,z4]),(0,[z7,z191,z1,z2,z194,z6])],[(0,[z7,z0,z1,z1228,z4,z6]),(0,[z7,z0,z17,z18,z2,z64]),(0,[z7,z0,z1,z19,z6,z1082]),(0,[z7,z0,z2,z4,z725,z6])],[(0,[z7,z0,z1,z4,z1229,z6])],[(0,[z7,z0,z51,z19,z4,z172]),(0,[z7,z0,z17,z2,z4,z332]),(0,[z7,z0,z17,z168,z2,z181]),(0,[z304,z7,z0,z1,z185,z4])],[(0,[z7,z0,z246,z455,z4,z6]),(0,[z7,z0,z1230,z2,z4,z6]),(0,[z7,z0,z105,z2,z4,z182])],[(0,[z137,z0,z17,z1,z19,z4]),(0,[z7,z0,z1,z2,z4,z1231]),(0,[z7,z0,z179,z2,z4,z67])],[(0,[z7,z0,z1,z2,z4,z1232]),(0,[z7,z0,z476,z1,z19,z4]),(0,[z7,z0,z17,z81,z2,z4]),(0,[z7,z416,z1,z2,z97,z6]),(0,[z7,z0,z105,z2,z4,z59])],[(0,[z7,z0,z1,z1233,z4,z6]),(0,[z7,z0,z1,z88,z69,z6])],[(0,[z7,z0,z1,z19,z177,z6]),(0,[z7,z0,z1,z2,z4,z1234]),(0,[z7,z0,z1,z2,z4,z371]),(0,[z7,z0,z1,z2,z4,z1235])],[(0,[z7,z90,z0,z17,z2,z64]),(0,[z7,z0,z1,z2,z4,z1236])],[],[(0,[z7,z0,z17,z388,z2,z4]),(1,[z7,z820,z2,z4,z6]),(0,[z7,z188,z1,z789,z4,z6]),(0,[z7,z0,z211,z28,z35,z6])],[(0,[z7,z0,z1237,z186,z2,z4]),(0,[z7,z0,z1237,z1,z2,z4]),(0,[z7,z0,z1,z4,z1238,z6]),(0,[z7,z0,z1,z88,z4,z532]),(0,[z408,z0,z388,z1,z2,z4])]],
   [[(0,[z7,z0,z1,z2,z93,z43]),(0,[z137,z0,z51,z1,z19,z4]),(0,[z7,z0,z1,z88,z732,z6]),(0,[z7,z0,z786,z1,z2,z4]),(0,[z7,z0,z51,z1,z2,z847])],[(0,[z7,z0,z1239,z1,z4,z6]),(0,[z7,z0,z1,z2,z4,z1240]),(0,[z7,z0,z1,z2,z171,z64])],[(0,[z7,z0,z17,z179,z2,z4])],[(0,[z7,z0,z186,z2,z4,z298]),(0,[z52,z0,z236,z132,z2,z4])],[(0,[z7,z0,z992,z1,z2,z4]),(0,[z7,z0,z17,z1,z478,z4]),(0,[z7,z1241,z1,z2,z4,z6]),(0,[z7,z0,z17,z697,z2,z4]),(0,[z7,z0,z151,z1,z4,z865])],[(0,[z34,z0,z51,z1,z2,z5])],[(0,[z7,z0,z1,z2,z4,z1242]),(0,[z7,z0,z1,z1243,z4,z6]),(0,[z7,z0,z953,z365,z2,z4]),(0,[z7,z0,z17,z28,z2,z35])],[(0,[z7,z0,z17,z1,z100,z4]),(0,[z7,z0,z17,z2,z4,z29])],[(0,[z7,z0,z365,z88,z4,z6]),(0,[z7,z0,z1,z2,z4,z36])],[(0,[z7,z0,z17,z18,z2,z4]),(0,[z7,z0,z1,z88,z4,z371]),(0,[z7,z0,z2,z4,z532,z172])],[(0,[z7,z0,z1,z2,z4,z43]),(0,[z7,z0,z186,z2,z325,z6]),(0,[z50,z12,z17,z1,z2,z4]),(0,[z7,z0,z1,z88,z80,z6]),(0,[z7,z0,z1,z2,z1194,z6]),(0,[z7,z61,z0,z17,z19,z4])],[(0,[z7,z0,z53,z51,z1,z19]),(0,[z7,z0,z168,z88,z181,z6]),(0,[z0,z302,z1,z88,z4,z6]),(0,[z7,z0,z960,z365,z2,z4]),(0,[z7,z0,z1,z1244,z4,z6])],[(0,[z500,z0,z1,z19,z4,z6])],[(0,[z52,z0,z51,z132,z2,z4]),(0,[z7,z0,z53,z17,z1,z2]),(0,[z7,z1215,z17,z1,z2,z4])],[(0,[z479,z0,z18,z2,z4,z6]),(0,[z7,z0,z1107,z19,z4,z6]),(0,[z7,z0,z41,z476,z20,z4]),(0,[z7,z0,z2,z277,z35,z6]),(0,[z7,z0,z1,z632,z4,z223])],[(0,[z7,z407,z0,z17,z2,z4]),(0,[z7,z0,z1,z1245,z4,z6]),(0,[z7,z0,z269,z18,z2,z4]),(0,[z7,z0,z1246,z2,z4,z6]),(0,[z7,z0,z51,z1,z100,z4]),(0,[z7,z0,z1247,z2,z4,z6])]],
   [[(0,[z7,z0,z1248,z2,z4,z6]),(0,[z7,z0,z1,z19,z4,z189]),(0,[z7,z0,z1,z1249,z4,z6]),(0,[z7,z0,z1250,z1,z2,z4])],[(0,[z7,z0,z53,z1,z2,z6]),(0,[z7,z90,z0,z17,z2,z4]),(0,[z7,z0,z1019,z1,z2,z4]),(0,[z7,z0,z17,z454,z2,z4])],[(0,[z50,z12,z1,z478,z4,z6]),(0,[z7,z0,z1,z2,z869,z4]),(1,[z7,z0,z17,z2,z80]),(0,[z7,z0,z168,z2,z725,z6])],[(0,[z7,z0,z1251,z2,z4,z6]),(0,[z7,z0,z248,z1,z2,z4])],[(0,[z7,z106,z1,z2,z4,z6]),(0,[z7,z379,z0,z17,z1,z2]),(0,[z7,z0,z17,z1,z165,z2]),(0,[z7,z0,z1,z2,z835,z6]),(0,[z7,z0,z56,z1,z117,z6]),(0,[z7,z0,z1,z2,z980,z4])],[(0,[z7,z0,z17,z88,z4,z29]),(0,[z7,z0,z27,z2,z980,z4]),(0,[z7,z0,z17,z2,z35,z182])],[(0,[z7,z0,z41,z477,z20,z4]),(0,[z7,z0,z211,z17,z1,z4])],[(0,[z7,z0,z1,z88,z4,z42]),(0,[z7,z0,z1,z1252,z4,z6]),(0,[z7,z417,z0,z17,z2,z4])],[(0,[z7,z0,z1,z88,z4,z43]),(0,[z7,z379,z0,z1,z2,z6]),(0,[z7,z824,z1,z2,z4,z6]),(0,[z7,z0,z1253,z2,z4,z6]),(0,[z7,z1,z2,z4,z67,z712])],[(0,[z52,z0,z217,z132,z2,z4]),(0,[z7,z0,z17,z946,z2,z4]),(0,[z7,z0,z79,z1,z19,z4]),(0,[z0,z471,z1,z19,z4,z6]),(0,[z7,z0,z1254,z1,z2,z4]),(0,[z7,z0,z175,z17,z1,z4]),(0,[z7,z0,z1,z2,z4,z1255]),(0,[z7,z0,z1,z2,z212,z182]),(0,[z7,z0,z1,z1256,z4,z6])],[(0,[z7,z126,z106,z1,z2,z6])],[(0,[z7,z0,z1257,z1,z2,z4]),(0,[z7,z0,z2,z4,z6,z1258]),(0,[z7,z0,z1,z1259,z4,z6])],[(0,[z7,z0,z1,z2,z1260,z6]),(0,[z506,z0,z1,z2,z4,z60])],[(0,[z7,z0,z96,z17,z1,z22])],[(0,[z7,z0,z2,z4,z1261,z6]),(0,[z7,z0,z1,z2,z4,z1262])],[(1,[z715,z1,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z1263]),(0,[z7,z0,z151,z1,z4,z94]),(0,[z7,z0,z1264,z2,z4,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 494) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 494).take 505) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 999).take 407) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1406)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [494, 505, 407] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 134).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 134).take 140).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 274).take 155).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 429).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [134, 140, 155, 83] = true :=
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

end PEqualNP.Outside.L_meta_38781

theorem PEqualNP.Outside.L_meta_38781 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4270377096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4270377096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38781.solve