#include <iostream>

using namespace std;

class Polygon {
	protected:
		int width, height;
	public:
		void set_values (int a, int b) {
			width = a;
			height = b;
		}

		virtual void print() {
			printf("polygon print()!\n");
		}

		virtual int area() {
			return 0;
		}
		Polygon() {
		}
		~Polygon() = default;
};

class Rectangle : public Polygon {
	public:
		Rectangle() {
		}

		int area() {
			return width * height;
		}
};

class Triangle : public Polygon {
	private:
		int dummyVal;
		char *dummyVal2;
	public:
		Triangle () {
		}

		int area() {
			return (width * height) / 2;
		}
};

void regular_function() {
	cout << "Hello from regular function" << endl;
}

int main(void) {
	Triangle trgl;
	volatile int dummy = 4;
	trgl.set_values(89,90);

	trgl.area();

	dummy += dummy * 3;

	printf("printing %i\n", dummy);	
	printf("done!\n");
	return 0;
}

