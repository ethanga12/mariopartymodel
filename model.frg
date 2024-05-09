#lang forge

option problem_type temporal
// option min_tracelength = 15

sig Tile {
	var next: one Tile,
    var back: one Tile, //are we gonna do this 
    var index: one Int,
    var color: one Color
}

sig Color {}

sig Red extends Color {}
sig Blue extends Color {}
sig Green extends Color {}

// one sig Root extends Tile {}


sig Board { //Board sig
    board: set Tile
}

// pred wellformed[b: Board] { //Tests that the board is wellformed
//     all row, col: Int | {
//         (row < 0 or row > 6 or col < 0 or col > 7) implies 
//             no b.board[row][col]
//         ((b.board[row][col] = R or b.board[row][col] = Y) and row >= 1) implies { //inductive falling
//             b.board[subtract[row, 1]][col] = R or b.board[subtract[row, 1]][col] = Y
//         }
//     }
//     #{row, col: Int | b.board[row][col] = R} >= #{row, col: Int | b.board[row][col] = Y} and #{row, col: Int | b.board[row][col] = R} < add[#{row, col: Int | b.board[row][col] = Y}, 2] //R moves first
// }


pred wellformed[b: Board] {
	-- all nodes are reachable from the root
    
    all t : b.board | {
        lone t : b.board | t.index = 0
        (#{r : t.color | r in Red} = 8)
        (#{g : t.color | g in Green } = 5)
        (#{b : t.color | b in Blue } = subtract[#{b.board}, 13])
        // Root->(t - Root) in ^next
        // (#{b : t.color | b in Blue } = 3)
        t.next != t
        t.back != t
        // t.back.next = t
        // t.next.back = t
        // t.next.index = 
        t.index != 0 implies t.index = add[t.back.index, 1] 
    }
    all disj t1, t2 : b.board | {
        t1.index != t2.index
        // t1.next = t2 implies {t2.index = add[t1.index, 1]}
    }
    // one t : b.board | t = Root

    // all disj tile, nextTile, notNextTile : b.board | {
    //     nextTile = tile.next
    // }

    // Root->(b.board - Root) in ^next
	
    // Root.index = 0
    // all t : b.board | {
    //     t.next != Root implies t.next.index = add[t.index, 1]
    //     t.next = Root implies t.next.index = 0
    // }
}

// abstract sig Pointer { // look at this later
// 	var position: lone Node
// }

// sig Red extends Tile {}
// sig Blue extends Tile {}
// sig Green extends Tile {}

abstract sig Player {
    var coins: one Int,
    var position: one Tile,
    var stars: set Star, 
    var items: set Item
}

abstract sig Item {
    // name: one 
}
sig Mushroom extends Item {} //sends them forward 3
sig FireFlower extends Item {} //Sends them back 3
sig Star extends Item {
    tile: one Int
} //not sure if this is the best way to do this

sig Mario extends Player {}
sig Luigi extends Player {}
sig Toad extends Player {}
sig Yoshi extends Player {}

pred init {
    all p: Player | p.coins = 10
    all p: Player | no p.stars
    all p: Player | no p.items
    all p: Player | p.position.index = 0 

    all b: Board | wellformed[b]
}

pred move[p: Player, r: Int] {
    // one next: Tile, current: Tile | {
    //     p.position = current
    //     next.index = add[current.index, r]
    //     p.position' = next
    // }

    p.position' = p.position.next

    // p.position.index' = add[p.position.index, r]
    // p.position.color' = Red => p.coins' = subtract[p.coins, 3]
    // p.position.color' = Blue => p.coins' = add[p.coins, 3]
    // p.position.color' = Green => {
    //     {{p.coins' = p.coins + 5} and not {p.coins' = p.coins - 5} and not {p.items' = p.items + Mushroom}} or 
    //     {not {p.coins' = p.coins + 5} and {p.coins' = p.coins - 5} and not {p.items' = p.items + Mushroom}} or 
    //     {not {p.coins' = p.coins + 5} and not {p.coins' = p.coins - 5} and {p.items' = p.items + Mushroom}}
    // }
    // {#{p.stars'} = add[#{p.stars}, 1]} => {
    //     some s: Star | p.position.index = s.tile
    //     p.coins >= 25
    //     p.coins' = p.coins - 25
    // }
}

pred final {
    some p: Player | p.stars = 1
}

pred trace_base {
    always wellformedall
    init
    some p: Player | eventually move[p, 1]
    // eventually final
}

pred wellformedall {
    all b: Board | wellformed[b]
}

run { trace_base } for 8 Int, exactly 1 Board, exactly 1 Mario, exactly 1 Luigi, exactly 1 Toad, exactly 1 Yoshi, exactly 16 Tile
// run { wellformedall } for 7 Int, exactly 1 Board, exactly 1 Mario, exactly 1 Luigi, exactly 1 Toad, exactly 1 Yoshi, exactly 16 Tile