#lang forge/temporal

open "model.frg"

//board formation
//tiles on board
//players on board
//4 players
//some star somewhere
//all players start at the same position
//players move in same direction
//players can move back w a fireflower
//players can move extra far w a mushroom 
//players can teleport to star 
//item increment on green tile
//coin decrement on red tile
//coin increment on blue tile
//star moves after purchase
//movement and looping the board
//players can't move more than 7 without a mushroom
//player can only move 0 if they used a fireflower
//player can only move 9 if they used a mushroom
//Once a player has a star, they can't lose it
//All players have moved before a minigame 
//All players can move again after a minigame

test suite for init { //also tests wellformedness
    test expect {
        validInitTest : {
            all t : Tile | all b : Board {
                t in b.board
                t.color = Red or t.color = Green or t.color = Blue
                (#{r : b.board | r.color = Red} = 2) // 2
                (#{g : b.board | g.color = Green } = 1) // 1
                (#{bl : b.board | bl.color = Blue } = 5) // 5
                #{b.board} = 8
                t.next.index = add[t.index, 1] or t.next.index = 0
                t.next.index = 0 => t.index = 7
            }
            all p : Player | all b : Board {
                p.position = 0
                p.coins = 5
                p.star = 0
                p.items[Mushroom] = 0 
                p.items[Fireflower] = 0
                p.items[GenieLamp] = 0
            }
        } is sat
        badPlayerCoins : {
            all t : Tile | all b : Board {
                t in b.board
                t.color = Red or t.color = Green or t.color = Blue
                (#{r : b.board | r.color = Red} = 2) // 2
                (#{g : b.board | g.color = Green } = 1) // 1
                (#{bl : b.board | bl.color = Blue } = 5) // 5
                #{b.board} = 8
                t.next.index = add[t.index, 1] or t.next.index = 0
                t.next.index = 0 => t.index = 7
            }
            some p : Player | all b : Board {
                p.position = 0
                p.coins = 6
                p.star = 0
                p.items[Mushroom] = 0 
                p.items[Fireflower] = 0
                p.items[GenieLamp] = 0
            }
        } is unsat
        badPlayerItems : {
            all t : Tile | all b : Board {
                t in b.board
                t.color = Red or t.color = Green or t.color = Blue
                (#{r : b.board | r.color = Red} = 2) // 2
                (#{g : b.board | g.color = Green } = 1) // 1
                (#{bl : b.board | bl.color = Blue } = 5) // 5
                #{b.board} = 8
                t.next.index = add[t.index, 1] or t.next.index = 0
                t.next.index = 0 => t.index = 7
            }
            some p : Player | all b : Board {
                p.position = 0
                p.coins = 5
                p.star = 0
                p.items[Mushroom] > 0 or
                p.items[Fireflower] > 0 or 
                p.items[GenieLamp] > 0
            }
        } is unsat
        badPlayerStars : {
            all t : Tile | all b : Board {
                t in b.board
                t.color = Red or t.color = Green or t.color = Blue
                (#{r : b.board | r.color = Red} = 2) // 2
                (#{g : b.board | g.color = Green } = 1) // 1
                (#{bl : b.board | bl.color = Blue } = 5) // 5
                #{b.board} = 8
                t.next.index = add[t.index, 1] or t.next.index = 0
                t.next.index = 0 => t.index = 7
            }
            some p : Player | all b : Board {
                p.position = 0
                p.coins = 5
                p.star = 1
                p.items[Mushroom] = 0
                p.items[Fireflower] = 0 
                p.items[GenieLamp] = 0
            }
        } is unsat
        noGreen : {
            all t : Tile | all b : Board {
                t in b.board
                t.color = Red or t.color = Green or t.color = Blue
                (#{r : b.board | r.color = Red} = 2) // 2
                (#{g : b.board | g.color = Green } = 0) // 1
                (#{bl : b.board | bl.color = Blue } = 5) // 5
                #{b.board} = 8
                t.next.index = add[t.index, 1] or t.next.index = 0
                t.next.index = 0 => t.index = 7
            }
            some p : Player | all b : Board {
                p.position = 0
                p.coins = 5
                p.star = 0
                p.items[Mushroom] = 0
                p.items[Fireflower] = 0 
                p.items[GenieLamp] = 0
            }
        } is unsat
        wrongTileDistribution : {
            all t : Tile | all b : Board {
                t in b.board
                t.color = Red or t.color = Green or t.color = Blue
                (#{r : b.board | r.color = Red} = 1) // 2
                (#{g : b.board | g.color = Green } = 5) // 1
                (#{bl : b.board | bl.color = Blue } = 2) // 5
                #{b.board} = 8
                t.next.index = add[t.index, 1] or t.next.index = 0
                t.next.index = 0 => t.index = 7
            }
            some p : Player | all b : Board {
                p.position = 0
                p.coins = 5
                p.star = 0
                p.items[Mushroom] = 0
                p.items[Fireflower] = 0 
                p.items[GenieLamp] = 0
            }
        } is unsat
    }
}

test suite for move {
    test expect {
        validNormalMove : {
            some p : Player | some b : Board {
                p.position = 0
                p.position' = 1 or 
                p.position' = 2 or 
                p.position' = 3 or
                p.position' = 4 or
                p.position' = 5 or
                p.position' = 6 
            } is sat
        }
         validGreenTileMove : {
            some p : Player | some b : Board {
                p.position = 0
                p.position' = 1 or 
                p.position' = 2 or 
                p.position' = 3 or
                p.position' = 4 or
                p.position' = 5 or
                p.position' = 6 
                p.items[Mushroom] = 0
            } is sat
            
        }
    }
}



