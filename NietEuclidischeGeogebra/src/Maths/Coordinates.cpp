// Coordinates.cpp : Defines the entry point for the application.
//
#include "Coordinates.h"
#include <windows.h>
#include <chrono>
#include <thread>
#include <cmath>

class CoordinateSystem {//creates a coordinate system
private:
	int coordinates[3] = { 0,0,0 };

	struct Coords {
		float x;
		float y;
	};
public:

	//Ik neem hier aan dat de z-as de diepte is. Dus normale 2d assenstelsel + naar je toe (+z) + verder van je af (-z)

	//float domainMin = -10.0f;// Minimum domain on the x-axis
	//float domainMax = 10.0f; // Maximum domain on the x-axis
	//void EditMaxDomain(int i);// Edit the Max side of the domain by i
	//void EditMinDomain(int i);// Edit the Min side of the domain by i
	//void SetMaxDomain(int i);// Set the Max domain to i
	//void SetMinDomain(int i);// Set the Min domain to i

	//float rangeMin = -10.0f;// Minimum domain on the y-axis
	//float rangeMax = 10.0f; // Maximum domain on the y-axis
	//void EditMaxRange(int i);// Edit the Max side of the range by i
	//void EditMinRange(int i);// Edit the Min side of the range by i
	//void SetMaxRange(int i);// Set the Max range to i
	//void SetMinRange(int i);// Set the Min range to i

	//float depthMin = 0.0f;// Minimum Depth on the z-axis (Further back)
	//float depthMax = 0.0f; // Maximum Depth on the z-axis (Closer to you)
	//void EditMaxDepth(int i); // Edit the Max side of the range by i
	//void EditMinDepth(int i); // Edit the Min side of the range by i
	//void SetMaxDepth(int i);// Set the Max Depth to i
	//void SetMinDepth(int i);// Set the Min Depth to i

	Coords NormalizeCoordinate(float CordX, float CordY, int WindowX, int WindowY);//Convert Cartesian Coordinates to relative coordinates on the window.
	void PrintCoordinates(float x, float y);// Print the coordinates to the console
};


void CoordinateSystem::PrintCoordinates(float x, float y) {
	coordinates[0] = x;
	coordinates[1] = y;
	std::cout << "[";
	for (int i = 0; i < 2; i++) {
		std::cout << coordinates[i] << " ";
	};
	std::cout << "]";
};

CoordinateSystem::Coords CoordinateSystem::NormalizeCoordinate(float CordX, float CordY, int WindowWidth, int WindowHeight) {


	/*WindowX = Columns #
	 WindowY = Rows #
	 SystemWidth = Coordinate System width (domain)
	 Systemheight = Coordinate System height (range)
	*/

	//OpenGL coordinates x[-1,1]y[-1,1]
	/*float xMover =(fabs(domainMax) + fabs(domainMin))  / WindowWidth;
	float yMover = (fabs(rangeMax) + fabs(rangeMin)) / WindowWidth;*/

	//std::cout << "---------\n";
	//std::cout << "xMover: " << xMover << "\n";
	//std::cout << "yMover: " << yMover << "\n";

	/*std::cout << "WindowWidth " << WindowWidth << std::endl;
	std::cout << "WindowHeight " << WindowHeight << std::endl;
	std::cout << "SystemWidth " << (fabs(domainMax) + fabs(domainMin)) << std::endl;
	std::cout << "SystemHeight " << (fabs(rangeMax) + fabs(rangeMin)) << std::endl;*/

	//unit
	float scale = 20;// in pixels
	float offsetX = 0;//in coords
	float offsetY = 0;//in coords 

	float glX = (offsetX + CordX) * scale;//in pixels
	float glY = (offsetY + CordY) * scale;// in pixels

	printf("----------");
	std::cout << "Coord " << CordX << " " << CordY << std::endl;
	std::cout << "OpenGL Coord.\n Pixels X: " << glX << " \nPixels Y: " << glY << std::endl;
	//check if out of bounds

	if (glX > ((WindowWidth / 2) + 1) || glY > ((WindowHeight / 2) + 1)) {
		printf("NAN");
		return { std::nanf(""), std::nanf("") };
	}

	printf("VALID");
	return { glX,glY };
};


int main()
{
	CoordinateSystem Euclidean;
	CONSOLE_SCREEN_BUFFER_INFO csbi;
	int columns, rows;

	//std::cout << "Domain " << Euclidean.domainMin << " " << Euclidean.domainMax << "\n";
	//std::cout << "Range " << Euclidean.rangeMin << " " << Euclidean.rangeMax << "\n";
	//std::cout << "Transform " << Euclidean.NormalizeCoordinate(1, 4, 140, 85) << "\n";
	//Euclidean.PrintCoordinates(1, 4);

	//create infinite loop
	while (true) {

		Euclidean.NormalizeCoordinate(5000, 400, 600, 400);
		std::this_thread::sleep_for(std::chrono::milliseconds(1000));

	}
	return 0;
}
