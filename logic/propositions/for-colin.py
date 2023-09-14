def shirtDiscount():
    print("Pick a shirt!")
    stickerPrice = float(input("What is the sticker price?"))
    tagColor = input("What is the tag color?")

    if tagColor == "pink":
        stickerPrice -= stickerPrice * .2
    elif tagColor == "green":
        stickerPrice -= stickerPrice * .4
    elif tagColor == "blue": 
        stickerPrice -= stickerPrice * .6

    print("Your reduced price is", stickerPrice)


class ColinList(list):
    def __init__(self, *args):
        list.__init__(self, *args)

    def nextItem(self):
        if len(self) == 0:
            return None
        else:
            return self.pop(0)


def findUsersNumber(L : ColinList, S : int, debug : bool = True):
    currentItem = L.nextItem()
    if debug: print("Looking for", S)
    while currentItem is not None:
        if debug: print("Checking current item:", currentItem)
        if currentItem == S:
            if debug: print("   Found user's number!")
            return True
        else:
            if debug: print("   Not user's number.")
            currentItem = L.nextItem()
    if debug: print("User's number is not in list.")
    return False

lst = ColinList([5,2,4,1,6,8,9,3])
findUsersNumber(lst, 6)