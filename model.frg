#lang forge/temporal

abstract sig Position {
    var tile: one Tile
}
abstract sig Start extends Position {}
abstract sig Tile {
    var position: one Position
}
sig Red extends Tile {}
sig Blue extends Tile {}
sig Green extends Tile {}

abstract sig Player {
    var coins: one Int,
    var position: one Position,
    var stars: set Star, 
    var items: one Item
}

abstract sig Item {
    var name: one String
}
sig Mushroom extends Item {} //sends them forward 3
sig FireFlower extends Item {} //Sends them back 3
sig Star extends Item {var position: one Position} //not sure if this is the best way to do this

sig Mario extends Player {}
sig Luigi extends Player {}
sig Toad extends Player {}
sig Yoshi extends Player {}

pred init {
    all p: Player | p.coins = 10
    all p: Player | p.stars = none
    all p: Player | p.items = none
    all p: Player | p.position = Start
}

pred move[p: Player, r: Int] {
    p.position.tile.position' = add[p.position.tile.position, r]
    p.position.tile' = Red => p.coins' = subtract[p.coins, 3]
    p.position.tile' = Blue => p.coins' = add[p.coins, 3]
    p.position.tile' = Green => {
        {p.coins' = add[p.coins, 5] and not subtract[p.coins, 5]
        and not p.items += Mushroom} or 
        {not p.coins' = add[p.coins, 5] and not subtract[p.coins, 5] and p.items += Mushroom} or 
        {not p.coins' = add[p.coins, 5] and subtract[p.coins, 5] and not p.items += Mushroom}
    }
    (p.position.tile' = some Star.position) and p.coins >= 25 => p.stars' = add[p.stars, 1] and subtract[p.coins, 25] //how to get sart to move? 
}