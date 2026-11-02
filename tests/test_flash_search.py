import unittest
from cognition import flash_search


class TestFlashSearchModule(unittest.TestCase):
    def test_flash_search(self):
        self.assertIsNotNone(flash_search)
        self.assertIsInstance(flash_search("sample"), list)


if __name__ == "__main__":
    unittest.main()
