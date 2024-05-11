#lang forge/temporal

// option problem_type temporal
option max_tracelength 20
option min_tracelength 20
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

abstract sig Item {}
one sig Mushroom extends Item {} //sends them forward 3
one sig FireFlower extends Item {} //Sends them back 3
one sig GenieLamp extends Item {} //Sends them to the current location of the star

one sig Star {
    var tile: one Tile,
    var price: one Int
}
abstract sig Player {
    var coins: one Int,
    var position: one Tile,
    var stars: one Int,
    var items: func Item -> Int
}

one sig Mario extends Player {}
one sig Luigi extends Player {}
one sig Toad extends Player {}
one sig Yoshi extends Player {}


sig Board { //Board sig
    board: set Tile,
    var playersMoved: set Player
}

pred wellformed[b: Board] {
	-- all nodes are reachable from the root
    all t : Tile { 
        t in b.board
        t.next != t
        t.back != t
        t.index != 0 implies {
            t.index = add[t.back.index, 1]
            t.index > 0
        }
        all disj t1, t2 : Tile | {
            t1.index != t2.index
            t1.next != t2.next
            t1.back != t2.back
            t1.next = t2 implies {{t2.index = add[t1.index, 1]} and {t1.index = subtract[t2.index, 1]}} or t2.index = 0 
        }
    }
    (#{r : b.board | r.color = Red} = 2) // 2
    (#{g : b.board | g.color = Green } = 1) // 1
    (#{bl : b.board | bl.color = Blue } = 5) // 5
    one t : b.board | t.index = 0

    // Star.tile in b.board and Star.tile.index > 2

    b.playersMoved = none
}

pred init {
    all p: Player | p.coins = 5
    // all p: Player | #{p.items} = 1
    all p : Player | {
        p.items[Mushroom] = 0
        p.items[FireFlower] = 0
        p.items[GenieLamp] = 0
    }
    all p: Player | p.stars = 0
    all p: Player | p.position.index = 0
    Star.price = 5

    all b: Board | wellformed[b]
}

pred move[p: Player, r: Int] {
    one moveTo: Tile, current: Tile | {
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
            useItem[p, moveTo] or {
                p.items' = p.items
                p.position' = moveTo
            }
        }

        moveTo.color = Red => {
            p.coins' = subtract[p.coins, 1]
            useItem[p, moveTo] or {
                p.items' = p.items
                p.position' = moveTo
            }
        }

        moveTo.color = Green => {
            p.coins' = p.coins
            one i : Item | all other: Item | {
                i != other => p.items'[other] = p.items[other]
                p.items'[i] = add[p.items[i], 1]
            }
            p.position' = moveTo
        }

        -- check if player passed the star when getting to new position
        some tilesToStar : Int | {
            { tilesToStar <= r and tilesToStar >= 0 } => {
                add[p.position.index, tilesToStar] = Star.tile.index
                p.coins >= Star.price => {
                    p.stars' = add[p.stars, 1]
                    // p.coins' = subtract[p.coins, Star.price]
                } else {
                    p.stars' = p.stars
                    // p.coins' = p.coins
                }
                starMove
            } else {
                p.stars' = p.stars
                starStay
            }
        }
    }
}

pred useItem[p: Player, moveTo: Tile] {
    one i : Item | all other : Item | {
        i != other => p.items'[other] = p.items[other]
        -- ensure that player has at least one of the item and then remove one from their inventory
        p.items[i] > 0
        p.items'[i] = subtract[p.items[i], 1]
        i in Mushroom => {
            one tileAfterItem : Tile | {
                -- now create a new tile that includes the effects of the item
                tileAfterItem.index = moveTo.next.next.next.index

                -- move to that tile instead of the original moveTo
                p.position' = tileAfterItem
            }
        }
        i in GenieLamp => {
            p.position' = Star.tile
        }
        i in FireFlower => {
            p.position' = moveTo
        }
    }
}

pred stayPut[p: Player] {
    p.coins' = p.coins
    p.items' = p.items
    p.stars' = p.stars
    p.position' = p.position
}

pred move_player_turn[p: Player] {
    move[p, 1] or move[p, 2] or move[p, 3] or move[p, 4] or move[p, 5] or move[p, 6]
}

pred game_turn {
    one b: Board | {
        #{b.playersMoved} = 4 => {
            b.playersMoved' = none
            minigame
        } else {
            one p : Player - b.playersMoved | {
                move_player_turn[p]
                all otherP : Player - p | {
                    stayPut[otherP]
                }
                b.playersMoved' = b.playersMoved + p
            }
        }

    }
}

pred minigame {
    starStay
    all p: Player | {
        p.items' = p.items
        p.stars' = p.stars
        p.position' = p.position

        p.coins' = add[p.coins, 2] or p.coins' = add[p.coins, 1] or p.coins' = p.coins
    }
}

pred starMove{
    one moveTo: Tile | {
        moveTo != Star.tile
        moveTo = Star.tile'
    }
}

pred starStay{
    Star.tile' = Star.tile
    Star.price' = Star.price
}

pred final {
    some p: Player | p.stars = 1
}

pred trace_base {
    init
    always game_turn
    // eventually final //adding eventually final increases the time to solve significantly
}

pred wellformedall {
    all b: Board | wellformed[b]
}

// run { trace_base } for exactly 1 Board, exactly 8 Tile, 1 Green, 2 Red, 5 Blue, 6 Int, 8 Color, exactly 20 Mushroom, exactly 20 FireFlower, exactly 10 GenieLamp, 50 Item
run { trace_base } for exactly 1 Board, exactly 8 Tile, 1 Green, 2 Red, 5 Blue, 5 Int
// run { trace_base } for exactly 1 Board, exactly 1 Mario, exactly 1 Luigi, exactly 1 Toad, exactly 1 Yoshi, exactly 8 Tile, 1 Green, 2 Red, 5 Blue, 6 Int, 8 Color, exactly 20 Mushroom, exactly 20 FireFlower, exactly 10 GenieLamp, 50 Item
// run { wellformedall } for 7 Int, exactly 1 Board, exactly 1 Mario, exactly 1 Luigi, exactly 1 Toad, exactly 1 Yoshi, exactly 16 Tile