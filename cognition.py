def flash_search(query):
    """Perform a search operation based on the given query.

    Args:
        query (str): The search query.

    Returns:
        list: A list of results matching the query.
    """
    import sqlite3

    # Connect to the database
    conn = sqlite3.connect('search_database.db')
    cursor = conn.cursor()

    # Execute the search query
    cursor.execute("SELECT * FROM terms WHERE term LIKE ?", ('%' + query + '%',))

    # Fetch all results
    results = cursor.fetchall()

    # Close the connection
    conn.close()
    return results
