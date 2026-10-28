import unittest
import sys
import os

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from cognition import flash_search

class TestCognition(unittest.TestCase):
    def test_flash_search(self):
        # This is a basic test to ensure the function runs without errors
        flash_search("test query")

if __name__ == '__main__':
    unittest.main()