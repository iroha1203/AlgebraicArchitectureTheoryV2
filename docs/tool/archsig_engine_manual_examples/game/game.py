"""一部屋のターン制ゲーム。説明用のコードであり、ArchSig 実装ではない。"""

from dataclasses import dataclass, replace


BOARD = frozenset({(0, 0), (1, 0), (2, 0), (0, 1), (2, 1), (0, 2), (1, 2), (2, 2)})
MONSTER = (2, 2)
KEYS = ("up", "right", "down", "left", "hit", "wait")
SCREEN_DIRECTIONS = {"up": (0, -1), "right": (1, 0), "down": (0, 1), "left": (-1, 0)}
ROTATIONS = ((1, 0, 0, 1), (0, -1, 1, 0), (-1, 0, 0, -1), (0, 1, -1, 0))
HEALTH_LEVELS = (0, 1, 2)
QUARTER_TURNS = (0, 1, 2, 3)
PALETTES = (0, 1)
ANIMATION_FRAMES = (0, 1)
DAMAGE_BONUSES = (0, 1)


@dataclass(frozen=True)
class Game:
    x: int
    y: int
    health: int
    monster_health: int


@dataclass(frozen=True)
class View:
    quarter_turn: int
    palette: int
    animation_frame: int


@dataclass(frozen=True)
class Command:
    kind: str
    dx: int = 0
    dy: int = 0


def admissible(s: Game) -> bool:
    return (s.x, s.y) in BOARD and s.health in HEALTH_LEVELS and s.monster_health in HEALTH_LEVELS and (s.health > 0 or s.monster_health > 0) and (s.monster_health == 0 or (s.x, s.y) != MONSTER)


def adjacent(s: Game) -> bool:
    return abs(s.x - MONSTER[0]) + abs(s.y - MONSTER[1]) == 1


def decode(key: str, view: View) -> Command:
    if key == "hit":
        return Command("attack")
    if key == "wait":
        return Command("wait")
    x, y = SCREEN_DIRECTIONS[key]
    a, b, c, d = ROTATIONS[view.quarter_turn]
    return Command("move", a * x + b * y, c * x + d * y)


def advance(s: Game, command: Command, damage_bonus: int) -> Game:
    if s.health == 0 or s.monster_health == 0:
        return s
    if command.kind == "move":
        destination = (s.x + command.dx, s.y + command.dy)
        if destination in BOARD and destination != MONSTER:
            s = replace(s, x=destination[0], y=destination[1])
    if command.kind == "attack" and adjacent(s):
        s = replace(s, monster_health=max(0, s.monster_health - (1 + damage_bonus)))
    if s.monster_health > 0 and adjacent(s):
        s = replace(s, health=max(0, s.health - 1))
    return s


def play_step(s: Game, key: str, view: View, damage_bonus: int) -> Game:
    return advance(s, decode(key, view), damage_bonus)


def display(s: Game, view: View) -> tuple:
    return (s.x, s.y, s.health, s.monster_health, view.quarter_turn, view.palette, view.animation_frame)


# 以下は、ホストに登録する記録形式の候補。
# 候補の正しさ、最小性、共通コアへの帰属を Atom に書き込まない。
@dataclass(frozen=True)
class Event:
    kind: str
    dx: int
    dy: int
    damage_bonus: int


def encode_event(key: str, view: View, damage_bonus: int) -> Event:
    command = decode(key, view)
    return Event(command.kind, command.dx, command.dy, damage_bonus if command.kind == "attack" else 0)



def record_key(key: str, view: View, damage_bonus: int) -> str:
    return key


def record_command(key: str, view: View, damage_bonus: int) -> Command:
    return decode(key, view)


def state_cases() -> tuple:
    return tuple(Game(p[0], p[1], h, m)
                 for p in BOARD for h in HEALTH_LEVELS for m in HEALTH_LEVELS
                 if admissible(Game(p[0], p[1], h, m)))


def input_cases() -> tuple:
    return tuple((key, View(angle, palette, frame), bonus)
                 for key in KEYS for angle in QUARTER_TURNS
                 for palette in PALETTES for frame in ANIMATION_FRAMES
                 for bonus in DAMAGE_BONUSES)


def play_scenario(s: Game, scenario: tuple) -> Game:
    return play_step(s, scenario[0], scenario[1], scenario[2])


def game_value(s: Game) -> tuple:
    return (s.x, s.y, s.health, s.monster_health)


def record_raw(scenario: tuple) -> str:
    return record_key(scenario[0], scenario[1], scenario[2])


def record_logical(scenario: tuple) -> Command:
    return record_command(scenario[0], scenario[1], scenario[2])


def record_resolved(scenario: tuple) -> Event:
    return encode_event(scenario[0], scenario[1], scenario[2])


# 有限モデルを利用するホストへの登録。関数名と役割を分ける。
# 観測者は登録先の用途と target の参照を記録する。
MODEL_PORTS = (
    ("state-domain", state_cases),
    ("input-domain", input_cases),
    ("turn", play_scenario),
    ("state-reading", game_value),
)
RECORDERS = (
    ("keys", record_raw),
    ("commands", record_logical),
    ("events", record_resolved),
)
