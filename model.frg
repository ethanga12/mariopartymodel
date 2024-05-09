#lang forge/temporal

// option problem_type temporal
option max_tracelength 5
option min_tracelength 5
option solver Glucose

sig Tile {
	next: one Tile,
    back: one Tile, //are we gonna do this 
    index: one Int,
    color: one Color
}

abstract sig Color {}

one sig Red extends Color {}
one sig Blue extends Color {}
one sig Green extends Color {}

// one sig Root extends Tile {}


sig Board { //Board sig
    board: set Tile
}


pred wellformed[b: Board] {
	-- all nodes are reachable from the root
    all t : Tile { 
        t in b.board
        t.next != t
        t.back != t
        t.index != 0 implies {
            t.index = add[t.back.index, 1] 
            // t.index = subtract[t.next.index, 1]
            t.index > 0
        }
        all disj t1, t2 : Tile | {
            t1.index != t2.index
            t1.next != t2.next
            t1.back != t2.back
            t1.next = t2 implies {{t2.index = add[t1.index, 1]} and {t1.index = subtract[t2.index, 1]}} or t2.index = 0 
        }
    }
    (#{r : b.board | r.color = Red} = 1) // 2
    (#{g : b.board | g.color = Green } = 1) // 1
    (#{bl : b.board | bl.color = Blue } = 2) // 5
    one t : b.board | t.index = 0

    Star.tile in b.board and Star.tile.index > 2
}

abstract sig Player {
    var coins: one Int,
    var position: one Tile,
    // var stars: set Star,
    var stars: one Int,
    var items: set Item
}

abstract sig Item {}
sig Mushroom extends Item {} //sends them forward 3
sig FireFlower extends Item {} //Sends them back 3
sig GenieLamp extends Item {} //Sends them to the current location of the star
// sig Star extends Item {
//     var tile: one Int
// } //not sure if this is the best way to do this

one sig Star {
    var tile: one Tile
}

one sig Mario extends Player {}
one sig Luigi extends Player {}
one sig Toad extends Player {}
one sig Yoshi extends Player {}

pred init {
    all p: Player | p.coins = 5
    all p: Player | #{p.items} = 1
    all p: Player | #{p.stars} = 0
    all p: Player | p.position.index = 0

    all b: Board | wellformed[b]
}

pred move[p: Player, r: Int] {
    one moveTo: Tile, current: Tile | some item: Item | {
        // item not in p.items
        p.position = current
        some t : Tile | one root : Tile | {
            root.index = 0
            add[current.index, r] <= subtract[#{Tile}, 1] => {
                moveTo.index = add[current.index, r]
            } else {
                -- get the last index of the board, subtract from the current index, and add to r to get the new index
                moveTo.index = add[subtract[current.index, #{Tile}], r]
            }
            
        }

        moveTo.color = Blue => {
            p.coins' = add[p.coins, 1]
            // p.items' = p.items
            {#{p.items'} <  #{p.items} and {
                one i : p.items | {
                    p.items - i = p.items'
                    // i not in p.items'
                    i in Mushroom => {
                        // p.position' = moveTo.next.next.next

                        one tileAfterItem : Tile | {
                            -- now create a new tile that includes the effects of the item
                            tileAfterItem.index = add[moveTo.index, 3]

                            -- move to that tile instead of the original moveTo
                            p.position' = tileAfterItem
                        }
                    } else {
                        p.position' = moveTo
                    }
                    // i in FireFlower => {
                    //     some p2 : Player {
                    //         p2.position'' = p2.position'.back.back.back
                    //     }
                    // }

                    /** IMPORTANT: fireflower is currently not actually implemented. the item is supposed to move a random
                    player three tiles back on their next move, but forge's model of constraints instead of variable assignments
                    makes this potentially impossible. **/
                }
            }} or {
                p.items' = p.items
                p.position' = moveTo
            }
        }
        moveTo.color = Red => {
            p.coins' = subtract[p.coins, 1]
            // p.items' = p.items
            {#{p.items'} < #{p.items} and {
                one i : p.items | {
                    p.items - i = p.items'
                    // i not in p.items'
                    i in Mushroom => {
                        // p.position' = moveTo.next.next.next

                        one tileAfterItem : Tile | {
                            -- now create a new tile that includes the effects of the item
                            tileAfterItem.index = add[moveTo.index, 3]

                            -- move to that tile instead of the original moveTo
                            p.position' = tileAfterItem
                        }
                    }
                    i in GenieLamp => {
                        p.position' = Star.tile
                        p.stars' = add[p.stars, 1]
                        starMove
                    }
                    i in FireFlower => {
                        p.position' = moveTo
                    }
                    // i in FireFlower => {
                    //     some p2 : Player {
                    //         p2.position''= p2.position'.back.back.back
                    //     }
                    // }

                    /** IMPORTANT: fireflower is currently not actually implemented. the item is supposed to move a random
                    player three tiles back on their next move, but forge's model of constraints instead of variable assignments
                    makes this potentially impossible. **/
                }

            }} or {
                p.items' = p.items
                p.position' = moveTo
            }
        }
        moveTo.color = Green => {
            p.coins' = p.coins
            p.items' = p.items + item
            p.position' = moveTo
        }

        
    }
}

pred game_turn {

    all p: Player | {
        move[p, 1] or move[p, 2] or move[p, 3] or move[p, 4] or move[p, 5] or move[p, 6]
        minigame[p]
    }
}

pred minigame[p: Player] {
    p.coins' = add[p.coins, 2] or p.coins' = add[p.coins, 1]
}

pred starMove{
    one moveTo: Tile| {
        moveTo != Star.tile
        moveTo = Star.tile'
    }
}

pred final {
    some p: Player | p.stars = 1
}

pred trace_base {
    init
    // always wellformedall
    // always game_turn
    // always game_turn
    always { 
        game_turn
    }
        
    // p.stars' = p.stars
    // next_state move[Mario, 3]
}

pred wellformedall {
    all b: Board | wellformed[b]
}

run { trace_base } for exactly 1 Board, exactly 1 Mario, exactly 1 Luigi, exactly 1 Toad, exactly 1 Yoshi, exactly 4 Tile, 1 Green, 1 Red, 2 Blue, 6 Int, 8 Color, exactly 20 Mushroom, exactly 20 FireFlower, 40 Item
// run { wellformedall } for 7 Int, exactly 1 Board, exactly 1 Mario, exactly 1 Luigi, exactly 1 Toad, exactly 1 Yoshi, exactly 16 Tile