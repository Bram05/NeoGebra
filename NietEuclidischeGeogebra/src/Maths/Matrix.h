#pragma once

#include <array>
#include <cstdint>

namespace Maths
{
	template <std::uint32_t rows, std::uint32_t columns, typename T = float>
	class Matrix
	{
	public:
		T& operator()(std::uint32_t row, std::uint32_t column);
		const T& operator()(std::uint32_t row, std::uint32_t column) const;

	public:
		std::array<T, rows* columns> m_Data;
	};

	// Matrix - matrix operations
	template <std::uint32_t rows1, std::uint32_t columns1, std::uint32_t columns2, typename m1T = float, typename m2T>
	auto operator*(const Matrix<rows1, columns1, m1T>& m1, const Matrix<columns1, columns2, m2T>& m2)
		->Matrix<rows1, columns2, decltype(m1(0, 0)* m2(0, 0))>;

	template <std::uint32_t rows, std::uint32_t columns, typename T = float>
	auto operator+(const Matrix<rows, columns, T>& m1, const Matrix<rows, columns, T>& m2)
		->Matrix<rows, columns, decltype(m1(0, 0) + m2(0, 0))>;

	template <std::uint32_t rows, std::uint32_t columns, typename T = float>
	auto operator-(const Matrix<rows, columns, T>& m1, const Matrix<rows, columns, T>& m2)
		->Matrix<rows, columns, decltype(m1(0, 0) + m2(0, 0))>;

	// Scalar - matrix operations
	template <std::uint32_t rows, std::uint32_t columns, typename matrixT = float, typename scalarT = float>
	auto operator*(scalarT num, const Matrix<rows, columns, matrixT>& matrix)->Matrix<rows, columns, decltype(num* matrix(0, 0))>;

	template <std::uint32_t rows, std::uint32_t columns, typename matrixT = float, typename scalarT = float>
	auto operator+(scalarT num, const Matrix<rows, columns, matrixT>& matrix)->Matrix<rows, columns, decltype(num + matrix)>;

	template <std::uint32_t rows, std::uint32_t columns, typename matrixT = float, typename scalarT = float>
	auto operator-(scalarT num, const Matrix<rows, columns, matrixT>& matrix)->Matrix<rows, columns, decltype(num - matrix)>;

	template <std::uint32_t rows, std::uint32_t columns, typename matrixT = float, typename scalarT = float>
	auto operator/(scalarT num, const Matrix<rows, columns, matrixT>& matrix)->Matrix<rows, columns, decltype(num / matrix)>;



	// Implementations
	/*template<std::uint32_t rows, std::uint32_t columns, typename T>
	Matrix<rows, columns, T>::Matrix()
	{
		for (std::uint32_t i{ 0 }; i < rows * columns; ++i)
			m_Data[i] = T();
	}

	template<std::uint32_t rows, std::uint32_t columns, typename T>
	Matrix<rows, columns, T>::Matrix(T value)
	{
		constexpr T smallest{ std::min(rows, columns) };
		for (std::uint32_t i{ 0 }; i < smallest; ++i)
			m_Data[i * columns + i] = value;
	}

	template<std::uint32_t rows, std::uint32_t columns, typename T>
	Matrix<rows, columns, T>::Matrix(std::initializer_list<T> data)
	{
		m_Data = data;
	}

	template<std::uint32_t rows, std::uint32_t columns, typename T>
	Matrix<rows, columns, T>::Matrix(const Matrix& other)
		: m_Data{ other.m_Data }
	{
	}

	template<std::uint32_t rows, std::uint32_t columns, typename T>
	Matrix<rows, columns, T>::Matrix(const T* data)
	{
		for (std::uint32_t i{ 0 }; i < rows; ++i)
		{
			for (std::uint32_t j{ 0 }; j < columns; ++j)
			{
				m_Data[i * columns + j] = data[i * columns + j];
			}
		}
	}*/

	template<std::uint32_t rows, std::uint32_t columns, typename T>
	T& Matrix<rows, columns, T>::operator()(std::uint32_t row, std::uint32_t column)
	{
		return m_Data[row * columns + column];
	}

	template<std::uint32_t rows, std::uint32_t columns, typename T>
	const T& Matrix<rows, columns, T>::operator()(std::uint32_t row, std::uint32_t column) const
	{
		return m_Data[row * columns + column];
	}



	// Matrix - Matrix operations
	template<std::uint32_t rows1, std::uint32_t columns1, std::uint32_t columns2, typename m1T, typename m2T>
	auto operator*(const Matrix<rows1, columns1, m1T>& m1, const Matrix<columns1, columns2, m2T>& m2) -> Matrix<rows1, columns2, decltype(m1(0, 0)* m2(0, 0))>
	{
		Matrix<rows1, columns2, decltype(m1(0, 0)* m2(0, 0))> result = {};
		for (std::uint32_t row{ 0 }; row < rows1; ++row)
		{
			for (std::uint32_t column{ 0 }; column < columns2; ++column)
			{
				for (std::uint32_t i{ 0 }; i < columns1; ++i)
				{
					result(row, column) += m1(row, i) * m2(i, column);
				}
			}
		}
		return result;
	}

	template<std::uint32_t rows, std::uint32_t columns, typename T>
	auto operator+(const Matrix<rows, columns, T>& m1, const Matrix<rows, columns, T>& m2) -> Matrix<rows, columns, decltype(m1(0, 0) + m2(0, 0))>
	{
		Matrix<rows, columns, decltype(m1(0, 0) + m2(0, 0))> result;
		for (std::uint32_t i{ 0 }; i < rows; ++i)
		{
			for (std::uint32_t j{ 0 }; j < columns; ++j)
			{
				result(i, j) = m1(i, j) + m2(i, j);
			}
		}
		return result;
	}

	template<std::uint32_t rows, std::uint32_t columns, typename T>
	auto operator-(const Matrix<rows, columns, T>& m1, const Matrix<rows, columns, T>& m2) -> Matrix<rows, columns, decltype(m1(0, 0) + m2(0, 0))>
	{
		Matrix<rows, columns, decltype(m1(0, 0) + m2(0, 0))> result;
		for (std::uint32_t i{ 0 }; i < rows; ++i)
		{
			for (std::uint32_t j{ 0 }; j < columns; ++j)
			{
				result(i, j) = m1(i, j) - m2(i, j);
			}
		}
		return result;
	}

	// Scalar - matrix operations

	template<std::uint32_t rows, std::uint32_t columns, typename matrixT, typename scalarT>
	auto operator*(scalarT num, const Matrix<rows, columns, matrixT>& matrix) -> Matrix<rows, columns, decltype(num* matrix)>
	{
		Matrix<rows, columns, decltype(num * matrix(0, 0))> result;
		for (std::uint32_t i{ 0 }; i < rows; ++i)
		{
			for (std::uint32_t j{ 0 }; j < columns; ++j)
			{
				result(i, j) = num * matrix(i, j);
			}
		}
		return result;
	}

	template<std::uint32_t rows, std::uint32_t columns, typename matrixT, typename scalarT>
	auto operator+(scalarT num, const Matrix<rows, columns, matrixT>& matrix) -> Matrix<rows, columns, decltype(num + matrix)>
	{
		Matrix<rows, columns, decltype(num + matrix)> result;
		for (std::uint32_t i{ 0 }; i < rows; ++i)
		{
			for (std::uint32_t j{ 0 }; j < columns; ++j)
			{
				result(i, j) = num + matrix(i, j);
			}
		}
		return result;
	}

	template<std::uint32_t rows, std::uint32_t columns, typename matrixT, typename scalarT>
	auto operator-(scalarT num, const Matrix<rows, columns, matrixT>& matrix) -> Matrix<rows, columns, decltype(num - matrix)>
	{
		Matrix<rows, columns, decltype(num + matrix)> result;
		for (std::uint32_t i{ 0 }; i < rows; ++i)
		{
			for (std::uint32_t j{ 0 }; j < columns; ++j)
			{
				result(i, j) = num - matrix(i, j);
			}
		}
		return result;
	}

	template<std::uint32_t rows, std::uint32_t columns, typename matrixT, typename scalarT>
	auto operator/(scalarT num, const Matrix<rows, columns, matrixT>& matrix) -> Matrix<rows, columns, decltype(num / matrix)>
	{
		Matrix<rows, columns, decltype(num + matrix)> result;
		for (std::uint32_t i{ 0 }; i < rows; ++i)
		{
			for (std::uint32_t j{ 0 }; j < columns; ++j)
			{
				result(i, j) = num / matrix(i, j);
			}
		}
		return result;
	}

} // namespace Mathematics