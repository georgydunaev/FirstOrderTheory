import unittest
from cognition import flash_search

class TestFlashSearch(unittest.TestCase):
    def test_flash_search(self):
        # Test the flash_search function with a sample query
        query = "sample query"
        results = flash_search(query)
        self.assertIsInstance(results, list)

    def test_flash_search_empty_query(self):
        # Test the flash_search function with an empty query
        query = ""
        results = flash_search(query)
        self.assertIsInstance(results, list)

    def test_flash_search_special_characters(self):
        # Test the flash_search function with special characters
        query = "@#$%^&*()"
        results = flash_search(query)
        self.assertIsInstance(results, list)

if __name__ == '__main__':
    unittest.main()