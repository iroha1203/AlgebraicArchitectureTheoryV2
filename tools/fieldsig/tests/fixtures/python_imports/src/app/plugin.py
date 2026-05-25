from importlib.metadata import entry_points


def load_plugins():
    return entry_points(group="app.plugins")
