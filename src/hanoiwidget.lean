import hanoi
import hanoitactics

open hanoi hanoi.tower
open widget widget.html widget.attr
open tactic hanoitactics

-- DUOLINGO COLORS ARE AESTHETIC <3
-- https://design.duolingo.com/identity/color
inductive color : Type
| cardinal
| bee
| beetle
| fox
| humpback
| macaw
| wolf
| white

open color

instance : has_to_string color :=
  ⟨ λ c, match c with
      | cardinal := "#ff4b4b"
      | bee := "#ffc800"
      | beetle := "#ce82ff"
      | fox := "#ff9600"
      | humpback := "#2b70c9"
      | macaw := "#1cb0f6"
      | wolf := "#777777"
      | white := "#ffffff"
    end
  ⟩

meta def pole_html (disks currDisks: ℕ) (c : color) : html empty :=
h "div" [
  style [
    ("background-color", to_string c),
    ("width", "5px"),
    ("height", to_string ((disks - currDisks)*10 + 10) ++ "px")
  ]
] []

#html pole_html 3 0 wolf

meta def disk_html (size : ℕ) (c : color) : html empty :=
h "div" [
  style [
    ("background-color", to_string c),
    ("width", to_string (size*20) ++ "px"),
    ("height", "10px")
  ]
] []

def disk_color1 : ℕ → color
| 1 := cardinal
| 2 := bee
| 3 := beetle
| 4 := fox
| 5 := humpback
| 6 := macaw
| _ := wolf -- no more than 6 disks D:

def disk_color2 : ℕ → color
| 1 := fox
| 2 := humpback
| 3 := macaw
| 4 := cardinal
| 5 := bee
| 6 := beetle
| _ := wolf

meta def disks_html (currDisks : list ℕ) : list (html empty) :=
currDisks.map (λ currDisk, disk_html currDisk (disk_color1 currDisk))

#html disk_html 1 cardinal
#html disk_html 2 bee
#html disk_html 3 beetle
#html disk_html 4 fox
#html disk_html 5 humpback
#html disk_html 6 macaw

meta def tower_html (disks : ℕ) (currDisks : list ℕ) : html empty :=
h "div" [
  style [
    ("display", "flex"),
    ("flex-direction", "column"),
    ("align-items", "center"),
    ("justify-items", "center"),
    ("width", to_string (disks*20 + 20) ++ "px"),
    ("height", to_string (disks*10 + 30) ++ "px")
  ]
] ([pole_html disks currDisks.length wolf] ++ (disks_html currDisks))

#html tower_html 3 [1,2,3]

meta def towers_html (t : position) : html empty :=
h "div" [
  style [
    ("display", "flex"),
    ("flex-direction", "row")
  ]
] [tower_html (num_disks t) t.A, tower_html (num_disks t) t.B, tower_html (num_disks t) t.C]

#html towers_html (position.mk [1,2,3] [] [])
#html towers_html (position.mk [2,3] [] [1])
#html towers_html (position.mk [3] [2] [1])
#html towers_html (position.mk [3] [1,2] [])
#html towers_html (position.mk [] [1,2] [3])
#html towers_html (position.mk [1] [2] [3])
#html towers_html (position.mk [1] [] [2,3])
#html towers_html (position.mk [] [] [1,2,3])

-- hanoi graph
-- Kevin showed me this cool thing https://twitter.com/stevenstrogatz/status/1340626057628688384?s=20
-- triangle from https://www.w3schools.com/howto/tryit.asp?filename=tryhow_css_shapes_triangle-up
meta def uptriangle_html (pole : ℕ) (trig text : color) : html empty :=
h "div" [
  style [
    ("width", "0px"),
    ("height", "0px"),
    ("border-left","25px solid transparent"),
    ("border-right", "25px solid transparent"),
    ("border-bottom", "50px solid " ++ to_string trig)
  ]
] [
  h "p" [
    style [
      ("position", "relative"),
      ("color", to_string text),
      ("font-size", "24px"),
      ("text-align", "center"),
      ("top", "18px"),
      ("right", "6.5px")
    ]
  ] [to_string pole]
]

#html uptriangle_html 1 humpback white
#html uptriangle_html 2 bee wolf
#html uptriangle_html 3 beetle white

meta def state_transitions_html (t : position) : html empty := sorry