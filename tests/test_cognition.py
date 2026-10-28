import unittest
from cognition import flash_search

class TestCognition(unittest.TestCase):
    def test_flash_search(self):
        query = "test query"
        results = flash_search(query)
        self.assertIsInstance(results, list)

if __name__ == '__main__':
    unittest.main()