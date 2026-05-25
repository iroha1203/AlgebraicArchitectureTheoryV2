import requests as http
from . import util
from app.models import User

def load(name):
    return __import__(name)
