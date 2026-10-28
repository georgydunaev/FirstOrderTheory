import unittest
from cognition import flash_search

class TestFlashSearch(unittest.TestCase):
    def test_flash_search(self):
        # Test the flash_search function with a sample query
        query = "sample query"
        results = flash_search(query)
        self.assertIsInstance(results, list)

if __name__ == '__main__':
    unittest.main()